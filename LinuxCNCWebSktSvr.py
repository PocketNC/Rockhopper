#!/usr/bin/python 
# -*- coding: cp1252 -*-

# *****************************************************
# *****************************************************
# WebServer Interface for LinuxCNC system
#
# Usage: LinuxCNCWebSktSvr.py <LinuxCNC_INI_file_name>
#
# Provides a web server using normal HTTP/HTTPS communication
# to information about the running LinuxCNC system.  Most
# data is transferred to and from the server over a
# WebSocket using JSON formatted commands and replies.
#
#
# ***************************************************** 
# *****************************************************
#
# Copyright 2012, 2013 Machinery Science, LLC
# Copyright 2018 Pocket NC, Inc.
#
import sys
import os
import gc
import linuxcnc
import datetime
import math
import tornado.ioloop
import tornado.web
import tornado.autoreload
import tornado.websocket
import logging
import json
import subprocess
import hal
import time
import MakeHALGraph
from copy import deepcopy
import re
import ssl
import GCodeReader
from ConfigParser import SafeConfigParser
import hashlib
import base64
#import rpdb2
import socket
import time
import threading
import fcntl
import signal
import select
import glob
import shutil
import tempfile
import zipfile
from random import random
from time import strftime
from optparse import OptionParser
from netifaces import interfaces, ifaddresses, AF_INET
from ini import read_ini_data, write_ini_data, ini_differences, merge_ini_data, get_parameter, set_parameter
import machinekit.hal
import httplib



originRE = re.compile("https?://([a-z0-9]+\.)?pocketnc.com")

def set_date_string(dateString):
  subprocess.call(['sudo', 'date', '-s', dateString])

# modified from https://stackoverflow.com/questions/5967500/how-to-correctly-sort-a-string-with-a-number-inside
def toIntOrString(text):
    try:
        retval = int(text)
    except ValueError:
        retval = text
    return retval

def natural_keys(text):
    return [ toIntOrString(c) for c in re.split('[v.-]', text) ]
    
UpdateStatusPollPeriodInMilliSeconds = 50
UpdateHALPollPeriodInMilliSeconds = 500
UpdateErrorPollPeriodInMilliseconds = 50

eps = float(0.000001)

main_loop =tornado.ioloop.IOLoop.instance()

linuxcnc_command = linuxcnc.command()

# TODO - make this an env var or something?
POCKETNC_DIRECTORY = "/home/pocketnc/pocketnc"

sys.path.insert(0, os.path.join(POCKETNC_DIRECTORY, "Settings"))
import version as boardRevision

BOARD_REVISION = boardRevision.getVersion()

INI_DEFAULTS_FILE = os.path.join(POCKETNC_DIRECTORY, "Settings/versions/%s/PocketNC.ini" % BOARD_REVISION)
SETTINGS_PATH = os.path.join(POCKETNC_DIRECTORY, "Settings")
CALIBRATION_OVERLAY_FILE = os.path.join(POCKETNC_DIRECTORY, "Settings/CalibrationOverlay.inc")

A_COMP_FILE = os.path.join(POCKETNC_DIRECTORY, "Settings/a.comp")
B_COMP_FILE = os.path.join(POCKETNC_DIRECTORY, "Settings/b.comp")

INI_FILENAME = ''
INI_FILE_PATH = ''

CONFIG_FILENAME = '%s/Rockhopper/CLIENT_CONFIG.JSON' % POCKETNC_DIRECTORY

MAX_BACKPLOT_LINES=50000

instance_number = 0

lastLCNCerror = ""

options = ""

lastBackplotFilename = ""
lastBackplotData = ""
BackplotLock = threading.Lock() 

uploadingFile = None
pressureData = []
temperatureData = []

class GitHubConnectionMonitor( object ):
  def __init__(self):
    self.ableToConnect = False
    self.stop = False
  
  def test_connection(self):
    while True:
      try:
        conn = httplib.HTTPConnection('www.github.com')
        conn.request('HEAD', '/pocketnc/pocketnc.git')
        resp = conn.getresponse()
        self.ableToConnect = resp.status < 400
      except socket.gaierror:
        self.ableToConnect = False
      if self.stop:
        break
      time.sleep(1)
    
connectionMonitor = GitHubConnectionMonitor()
connectionTestThread = threading.Thread(target=connectionMonitor.test_connection)
connectionTestThread.start()

def sigterm_handler(_signo, _stack_frame):
  connectionMonitor.stop = True
  main_loop.stop()
  sys.exit(0)

signal.signal(signal.SIGTERM, sigterm_handler)
signal.signal(signal.SIGINT, sigterm_handler)

# *****************************************************
# Class to poll linuxcnc for status.  Other classes can request to be notified
# when a poll happens with the add/del_observer methods
# *****************************************************
class LinuxCNCStatusPoller(object):
    def __init__(self, main_loop, UpdateStatusPollPeriodInMilliSeconds):
        global lastLCNCerror
        # open communications with linuxcnc
        self.linuxcnc_status = linuxcnc.stat()
        try:
            self.linuxcnc_status.poll()
            self.linuxcnc_is_alive = True
        except:
            self.linuxcnc_is_alive = False

        self.linuxcnc_errors = linuxcnc.error_channel()
        lastLCNCerror = ""
        self.errorid = 0
        
        # begin the poll-update loop of the linuxcnc system
        self.scheduler = tornado.ioloop.PeriodicCallback( self.poll_update, UpdateStatusPollPeriodInMilliSeconds, io_loop=main_loop )
        self.scheduler.start()
        
        # begin the poll_update_errors loop of the linuxcnc system
        self.scheduler_errors = tornado.ioloop.PeriodicCallback( self.poll_update_errors, UpdateErrorPollPeriodInMilliseconds, io_loop=main_loop )
        self.scheduler_errors.start()
        
        # register listeners
        self.observers = []
        self.hal_observers = []

        hss_ini_data = read_ini_data(INI_FILENAME, 'POCKETNC_FEATURES', 'HIGH_SPEED_SPINDLE')
        self.is_hss = len(hss_ini_data['parameters']) > 0 and hss_ini_data['parameters'][0]['values']['value'] == '1'
        if self.is_hss:
          # wait here until the hss userspace components are loaded
          while True:
            try:
              self.hss_aborted_pin = machinekit.hal.Pin("hss_warmup.aborted")
              self.hss_full_warmup_pin = machinekit.hal.Pin("hss_warmup.full_warmup_needed")
              self.hss_p_abort_pin = machinekit.hal.Pin("hss_sensors.p_abort")
              self.hss_p_detect_abort_pin = machinekit.hal.Pin("hss_sensors.p_detect_abort")
              self.hss_t_abort_pin = machinekit.hal.Pin("hss_sensors.t_abort")
              self.hss_t_detect_abort_pin = machinekit.hal.Pin("hss_sensors.t_detect_abort")
              break
            except:
              time.sleep(.1)
        else:
          self.hss_aborted_pin = None
          self.hss_full_warmup_pin = None
          self.hss_p_abort_pin = None
          self.hss_p_detect_abort_pin = None
          self.hss_t_abort_pin = None
          self.hss_t_detect_abort_pin = None

        rtc_ini_data = read_ini_data(INI_FILENAME, 'POCKETNC_FEATURES', 'RUN_TIME_CLOCK')
        has_rtc = len(rtc_ini_data['parameters']) > 0 and rtc_ini_data['parameters'][0]['values']['value'] == '1'
        if has_rtc:
          safetyCounter = 0
          while True:
            try:
              self.rtc_seconds_pin = machinekit.hal.Pin("run_time_clock.seconds")
              break
            except:
              safetyCounter += 1
              if(safetyCounter > 1000):
                  break
              time.sleep(0.1)
        
        self.axis_velocities = {}
        for n in range(5):
          print n
          self.axis_velocities[n] = machinekit.hal.Pin("axis." + `n` + ".joint-vel-cmd")

        interlock_ini_data = read_ini_data(INI_FILENAME, 'POCKETNC_FEATURES', 'INTERLOCK')
        self.has_interlock = len(interlock_ini_data['parameters']) > 0 and interlock_ini_data['parameters'][0]['values']['value'] == '1'
        if self.has_interlock:
          while True:
            try:
              self.interlock_pause_alert_pin = machinekit.hal.Pin("interlock.pause-alert")
              self.interlock_spindle_stop_alert_pin = machinekit.hal.Pin("interlock.spindle-stop-alert")
              self.interlock_exception_alert_pin = machinekit.hal.Pin("interlock.exception-alert")
              break
            except:
              time.sleep(.01)
        else:
          self.interlock_pause_alert_pin = None
          self.interlock_spindle_stop_alert_pin = None
          self.interlock_exception_alert_pin = None

        # HAL dictionaries of signals and pins
        self.pin_dict = {}
        self.sig_dict = {}
        
        self.counter = 0

    def add_observer(self, callback):
        self.observers.append(callback)

    def del_observer(self, callback):
        self.observers.remove(callback)

    def add_hal_observer(self, callback):
        self.hal_observers.append(callback)

    def del_hal_observer(self, callback):
        self.hal_observers.remove(callback)

    def clear_all(self, matching_connection):
        self.obervers = []

    def poll_update_errors(self):
      global lastLCNCerror

      try:
        if (self.linuxcnc_is_alive is False):
            return
        if (self.hss_aborted_pin is not None) and self.hss_aborted_pin.get():
          if (self.hss_full_warmup_pin is not None) and self.hss_full_warmup_pin.get():
            lastLCNCerror = { 
              "kind": "spindle_warmpup", 
              "type":"error", 
              "text": "You must run the full spindle warm up sequence (approx. 50 minutes) since it hasn't been turned on in over 1 week.", 
              "time":strftime("%Y-%m-%d %H:%M:%S"), 
              "id":self.errorid 
            }
          else:
            lastLCNCerror = { 
              "kind": "spindle_warmpup", 
              "type":"error", 
              "text": "You must run the short spindle warm up sequence (approx. 10 minutes) since it hasn't been turned on in over 12 hours.", 
              "time":strftime("%Y-%m-%d %H:%M:%S"), 
              "id":self.errorid 
            }
          self.errorid += 1
          self.hss_aborted_pin.set(0);
        elif (self.hss_p_abort_pin is not None) and self.hss_p_abort_pin.get():
          lastLCNCerror = { 
            "kind": "spindle_pressure", 
            "type":"error", 
            "text": "Spindle air supply pressure below minimum 20 PSI (0.138 MPA).", 
            "time":strftime("%Y-%m-%d %H:%M:%S"), 
            "id":self.errorid 
          }
          self.errorid += 1
          self.hss_p_abort_pin.set(0);
        elif (self.hss_p_detect_abort_pin is not None) and self.hss_p_detect_abort_pin.get():
          lastLCNCerror = { 
            "kind": "spindle_pressure_detect", 
            "type":"error", 
            "text": "Failed to detect air supply pressure sensor. Spindle cannot be turned on.", 
            "time":strftime("%Y-%m-%d %H:%M:%S"), 
            "id":self.errorid 
          }
          self.errorid += 1
          self.hss_p_detect_abort_pin.set(0);
        elif (self.hss_t_abort_pin is not None) and self.hss_t_abort_pin.get():
          lastLCNCerror = { 
            "kind": "spindle_temperature", 
            "type":"error", 
            "text": "Ambient temperature is outside the spindle's safe operating range of 32-104F (0-40C).", 
            "time":strftime("%Y-%m-%d %H:%M:%S"), 
            "id":self.errorid 
          }
          self.errorid += 1
          self.hss_t_abort_pin.set(0);
        elif (self.hss_t_detect_abort_pin is not None) and self.hss_t_detect_abort_pin.get():
          lastLCNCerror = { 
            "kind": "spindle_pressure_detect", 
            "type":"error", 
            "text": "Failed to detect main board temperature sensor. Spindle cannot be turned on.", 
            "time":strftime("%Y-%m-%d %H:%M:%S"), 
            "id":self.errorid 
          }
          self.errorid += 1
          self.hss_t_detect_abort_pin.set(0);
        elif (self.interlock_pause_alert_pin is not None) and self.interlock_pause_alert_pin.get():
          lastLCNCerror = { 
            "kind": "interlock_program", 
            "type":"error", 
            "text": "Enclosure opened while program running, program has been paused.",
            "time":strftime("%Y-%m-%d %H:%M:%S"), 
            "id":self.errorid
          }
          self.errorid += 1
          self.interlock_pause_alert_pin.set(0)
        elif (self.interlock_spindle_stop_alert_pin is not None) and self.interlock_spindle_stop_alert_pin.get():
          lastLCNCerror = { 
            "kind": "interlock_program", 
            "type":"error", 
            "text": "Enclosure opened while spindle enabled, spindle has been stopped.",
            "time":strftime("%Y-%m-%d %H:%M:%S"), 
            "id":self.errorid
          }
          self.errorid += 1
          self.interlock_spindle_stop_alert_pin.set(0)
        elif (self.interlock_exception_alert_pin is not None) and self.interlock_exception_alert_pin.get():
          lastLCNCerror = { 
            "kind": "interlock_exception", 
            "type":"error",
            "text": "An exception has occured in the interlock HAL component, machine has been E-stopped as a precaution.",
            "time":strftime("%Y-%m-%d %H:%M:%S"),
            "id":self.errorid
          }
          self.errorid += 1
          self.interlock_exception_alert_pin.set(0)  
        else:
          if ( (self.linuxcnc_errors is None) ):
              self.linuxcnc_errors = linuxcnc.error_channel()
          try:    
              error = self.linuxcnc_errors.poll()

              if error:
                  kind, text = error
                  if kind in (linuxcnc.NML_ERROR, linuxcnc.OPERATOR_ERROR):
                      typus = "error"
                  else:
                      typus = "info"
                  lastLCNCerror = { "kind":kind, "type":typus, "text":text, "time":strftime("%Y-%m-%d %H:%M:%S"), "id":self.errorid }

                  self.errorid = self.errorid + 1 
          except:
              pass
      except Exception as e:
        print e

    def poll_update(self):
        global linuxcnc_command

        # update linuxcnc status
        if (self.linuxcnc_is_alive):
            try:
                if ( self.linuxcnc_status is None ):
                    self.linuxcnc_status = linuxcnc.stat()
                    linuxcnc_command = linuxcnc.command()
                self.linuxcnc_status.poll()
            except:
                self.linuxcnc_status = None
                linuxcnc_command = None
        else:
            self.linuxcnc_errors = None
            self.linuxcnc_status = None
            linuxcnc_command = None

        # notify all obervers of new status data poll
        for observer in self.observers:
            try:
                observer()
            except Exception as ex:
                self.del_observer(observer)



# *****************************************************
# Global LinuxCNCStatus Polling Object
# *****************************************************
LINUXCNCSTATUS = []

    

# *****************************************************
# Class to track an individual status item
# *****************************************************
class StatusItem( object ):

    def __init__( self, name=None, valtype='', help='', watchable=True, isarray=False, arraylen=0, requiresLinuxCNCUp=True, coreLinuxCNCVariable=True, isAsync=False ):
        self.name = name
        self.valtype = valtype
        self.help = help
        self.isarray = isarray
        self.arraylength = arraylen
        self.watchable = watchable
        self.requiresLinuxCNCUp = requiresLinuxCNCUp
        self.coreLinuxCNCVariable = coreLinuxCNCVariable
        self.isasync = isAsync
        self.halBinding = None


    @staticmethod
    def from_name( name ):
        global StatusItems
        val = StatusItems.get( name, None )
        if val is not None:
            return val
        if name.find('halpin_') is 0:
            return StatusItem( name=name, valtype='halpin', help='HAL pin.', isarray=False )
        elif name.find('halsig_') is 0:
            return StatusItem( name=name, valtype='halsig', help='HAL signal.', isarray=False )
        return None

    # puts this object into the dictionary, with the key == self.name
    def register_in_dict( self, dictionary ):
        dictionary[ self.name ] = self

    def to_json_compatible_form( self ):
        return self.__dict__

    def backplot_async( self, async_buffer, async_lock, linuxcnc_status_poller ):

        global lastBackplotFilename
        global lastBackplotData
        
        def do_backplot( self, async_buffer, async_lock, filename ):
            global MAX_BACKPLOT_LINES
            global lastBackplotFilename
            global lastBackplotData
            global BackplotLock

            BackplotLock.acquire()
            try:
                if (lastBackplotFilename != filename):
                    gr = GCodeReader.GCodeRender( INI_FILENAME )
                    gr.load()
                    lastBackplotData = gr.to_json(maxlines=MAX_BACKPLOT_LINES)
                    lastBackplotFilename = filename
                reply = {'data':lastBackplotData, 'code':LinuxCNCServerCommand.REPLY_COMMAND_OK }
            except Exception as ex:
                reply = {'data':'','code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }
                print "Error in back plot", ex
            BackplotLock.release()

            async_lock.acquire()
            async_buffer.append(reply)
            async_lock.release()
            return

        if (( async_buffer is None ) or ( async_lock is None)):
            return { 'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND,'data':'' }

        if (lastBackplotFilename == linuxcnc_status_poller.linuxcnc_status.file):
            return {'data':lastBackplotData, 'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        
        #thread = threading.Thread(target=do_backplot, args=(self, async_buffer, async_lock, linuxcnc_status_poller.linuxcnc_status.file))
        #thread.start()
        return { 'code':LinuxCNCServerCommand.REPLY_COMMAND_OK, 'data':'' } 

    def backplot( self ):
        global MAX_BACKPLOT_LINES
        global BackplotLock
        reply = ""
        BackplotLock.acquire()
        try:
            gr = GCodeReader.GCodeRender( INI_FILENAME )
            gr.load()
            reply = gr.to_json(maxlines=MAX_BACKPLOT_LINES)
        except ex:
            print ex
        BackplotLock.release()
        return reply

    def check_if_rotary_motion_only( self ):
      global LINUXCNCSTATUS
      epsilon = 0.000001
      
      is_linear_motion = abs(LINUXCNCSTATUS.axis_velocities[0].get()) > epsilon
      is_linear_motion |= abs(LINUXCNCSTATUS.axis_velocities[1].get()) > epsilon
      is_linear_motion |= abs(LINUXCNCSTATUS.axis_velocities[2].get()) > epsilon

      is_rotary_motion = abs(LINUXCNCSTATUS.axis_velocities[3].get()) > epsilon
      is_rotary_motion |= abs(LINUXCNCSTATUS.axis_velocities[4].get()) > epsilon

      return is_rotary_motion and not is_linear_motion

    def update_hss_sensor_data( self, new_reading, data_list, large_change_threshold ):
      try:
        newReading = float(new_reading)
        # Always add to list if it is empty
        if not data_list:
          data_list.append([time.time(), newReading])
          return

        mostRecentReadingTime = data_list[-1][0]
        nowTime = time.time()
        # We want at least one reading per minute
        shouldAppend = (nowTime - mostRecentReadingTime) > 60

        # Always save reading if magnitude of change is large enough
        if not shouldAppend:
          change = newReading - data_list[-1][1]
          shouldAppend = abs(change) > large_change_threshold

        if shouldAppend:
          data_list.append([nowTime, newReading])

        # Remove any data points older than 1 hour
        while ( nowTime - data_list[0][0] ) > 3600:
          data_list.pop(0)

      except Exception as ex:
        print ex


    def read_gcode_file( self, filename ):
        try:
            f = open(filename, 'r')
            ret = f.read()
        except ex:
            print ex
            ret = ""
        finally:
            f.close()
        return ret

    @staticmethod
    def get_ini_data_item(section, item_name):
        try:
            reply = StatusItem.get_ini_data( only_section=section.strip(), only_name=item_name.strip() )
        except Exception as ex:
            reply = {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND,'data':''}
        return reply        

    @staticmethod
    def get_overlay_data():
      try:
        ini_data = read_ini_data(CALIBRATION_OVERLAY_FILE)
        reply = {'data': ini_data, 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK }
      except Exception as ex:
        reply = {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND,'data':''}

      return reply


    # called in a "get_config" command to read the config file and output it's values
    @staticmethod
    def get_ini_data( only_section=None, only_name=None ):
        global INI_FILENAME

        try:
            ini_data = read_ini_data(INI_FILENAME, only_section, only_name)
            reply = {'data': ini_data,'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        except Exception as ex:
            reply = {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND,'data':''}

        return reply

    @staticmethod
    def check_hal_file_listed_in_ini( filename ):
        # check this is a valid hal file name
        f = filename
        found = False
        halfiles = StatusItem.get_ini_data( only_section='HAL', only_name='HALFILE' )
        halfiles = halfiles['data']['parameters']
        for v in halfiles:
            if (v['values']['value'] == f):
                found = True
                break
        if not found:
            halfiles = StatusItem.get_ini_data( only_section='HAL', only_name='POSTGUI_HALFILE' )
            halfiles = halfiles['data']['parameters']
            for v in halfiles:
                if (v['values']['value'] == f):
                    found = True
                    break
        return found

    def get_compensation( self ):
        reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK }

        try:
            data = {
                'a': [],
                'b': []
            }
            af = open(A_COMP_FILE, 'r')
            a_data = af.read()

            bf = open(B_COMP_FILE, 'r')
            b_data = bf.read()

            atriples = a_data.split()
            btriples = b_data.split()

            for ai in range(0, len(atriples), 3):
                angle = float(atriples[ai])
                forward = float(atriples[ai+1])
                backward = float(atriples[ai+2])
                data['a'].append([ angle, forward, backward ])

            for bi in range(0, len(btriples), 3):
                angle = float(btriples[bi])
                forward = float(btriples[bi+1])
                backward = float(btriples[bi+2])
                data['b'].append([ angle, forward, backward ])

            reply['data'] = data

        except:
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        finally:
          try:
              af.close()
              bf.close()
          except:
              pass

        return reply

    def get_client_config( self ):
        global CONFIG_FILENAME
        reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK }
        reply['data'] = '{}'

        try:
            fo = open( CONFIG_FILENAME, 'r' )
            reply['data'] = fo.read()
        except:
            reply['data'] = '{}'
        finally:
            try:
                fo.close()
            except:
                pass
        return reply


    def get_hal_file( self, filename ): 
        global INI_FILENAME
        global INI_FILE_PATH        
        try:

            reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK }
            # strip off just the filename, if a path was given
            # we will only look in the config directory, so we ignore path
            [h,f] = os.path.split( filename )
            if not StatusItem.check_hal_file_listed_in_ini( f ):
                reply['code']= LinuxCNCServerCommand.REPLY_ERROR_INVALID_PARAMETER
                return reply

            reply['data'] = ''

            try:
                fo = open( os.path.join( INI_FILE_PATH, f ), 'r' )
                reply['data'] = fo.read()
            except:
                reply['data'] = ''
            finally:
                try:
                    fo.close()
                except:
                    pass
            
        except Exception as ex:
            reply['data'] = ''
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND

        return reply

    def get_current_version(self):
        global POCKETNC_DIRECTORY

        try:
            cur_version = subprocess.check_output(['git', 'describe'], cwd=POCKETNC_DIRECTORY).strip()
        except:
            return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }


        return { "code": LinuxCNCServerCommand.REPLY_COMMAND_OK, "data": cur_version }

    def get_versions(self):
        try:
            all_versions = subprocess.check_output(['git', 'tag', '-l'], cwd=POCKETNC_DIRECTORY).split()
            all_versions.sort(key=natural_keys)
        except:
            return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

        return { "code": LinuxCNCServerCommand.REPLY_COMMAND_OK, "data": all_versions }

    def test_github_connection(self):
      global connectionMonitor
      return { "code": LinuxCNCServerCommand.REPLY_COMMAND_OK, "data": connectionMonitor.ableToConnect }

    def list_gcode_files( self, directory ):
        file_list = []
        code = LinuxCNCServerCommand.REPLY_COMMAND_OK
        try:
            if directory is None:
                directory = "."
                directory = StatusItem.get_ini_data( only_section='DISPLAY', only_name='PROGRAM_PREFIX' )['data']['parameters'][0]['values']['value']
        except:
            pass
        try:
            file_list = glob.glob(  os.path.join(directory,'*.[nN][gG][cC]') )
        except:
            code = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        return { "code":code, "data":file_list, "directory":directory }

    def detect_usb( self ):
      detected = False
      try:
        # usbmount uses available dir with lowest number among /media/usb[0-7] as mount location
        usbDirBase = "/media/usb"
        usbDir = ""
        for mountDirIdx in range(8):
          usbDir = usbDirBase + str( mountDirIdx )
          if ( os.path.exists(usbDir) and len(os.listdir(usbDir)) > 0 ):
            detected = True
      except:
        pass
      reply = { "code":LinuxCNCServerCommand.REPLY_COMMAND_OK, "data":detected }
      return reply

    def map_usb( self ):
      try:
        usbMap = { "detected" : False }
        # usbmount uses available dir with lowest number among /media/usb[0-7] as mount location
        usbDirBase = "/media/usb"
        usbDir = ""
        for mountDirIdx in range(8):
          usbDir = usbDirBase + str( mountDirIdx )
          if ( os.path.exists(usbDir) and len(os.listdir(usbDir)) > 0 ):
            usbMap["detected"] = True
            usbMap["mountPath"] = usbDir
            break
        if usbMap["detected"]:
          startIdx = usbDir.rfind(os.sep) + 1
          #adapted from http://code.activestate.com/recipes/577879-create-a-nested-dictionary-from-oswalk/
          for path, dirs, files in os.walk(usbDir):
            currentDirs = path[startIdx:].split(os.sep)
            # Don't add anything within a hidden dir to map
            if any( d[0] == '.' or d == 'System Volume Information' for d in currentDirs ):
              continue
            # Navigate through the nested dicts until a new dict is created for the current location
            currentLocation = usbMap
            for d in currentDirs:
              currentLocation = currentLocation.setdefault(d, {} )
            for f in files:
              if ( f[0] != '.' ) and ( f[-4:].lower() == '.ngc' ):
                currentLocation[f] = None
      except Exception as e:
        code = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        ret["data"] = e.message
      return  { "code":LinuxCNCServerCommand.REPLY_COMMAND_OK, "data":usbMap }

    def get_users( self ):
        global userdict
        return  { "code":LinuxCNCServerCommand.REPLY_COMMAND_OK, "data":userdict.keys() }

    def get_system_status( self ):
        code = LinuxCNCServerCommand.REPLY_COMMAND_OK
        ret = { "data": {} }

        try:
            df_data = subprocess.check_output(['df']).split()
            #df gives 6 columns of data. The 6th column, Mounted on, provides a search term for the root directory ("/") which is consistent across tested versions of df
            #The 3 desired disk space values are located 4, 3, and 2 positions behind the location of this search term
            totalIndex = df_data.index("/") - 4
            (total,used,available) = [ int(x) for x in df_data[totalIndex:totalIndex+3] ] 

            logs_used = int(subprocess.check_output(['sudo', 'du', '-k', '-d', '0', '/var/log']).split()[0])

            ini_data = read_ini_data(INI_FILENAME)
            ncfiles_path = get_parameter(ini_data, "DISPLAY", "PROGRAM_PREFIX")["values"]["value"]

            ncfiles_used = int(subprocess.check_output(['du', '-k', '-d', '0', ncfiles_path]).split()[0])

            ret["data"] = {
                "disk": {
                    "total": total,
                    "other": total-available-logs_used-ncfiles_used,
                    "available": available,
                    "logs": logs_used,
                    "ncfiles": ncfiles_used
                },
                "addresses": [],
                # Format date/time so that javascript can parse it simply with new Date(string) while
                # and get the correct date and time regardless of time zone. The browser can then show
                # the local time zone.
                "date": str(datetime.datetime.utcnow().strftime("%a %b %d %H:%M:%S UTC %Y"))
            }

            for ifaceName in interfaces():
                ret["data"]["addresses"] += [ i['addr'] for i in ifaddresses(ifaceName).setdefault(AF_INET, [{'addr':'No IP addr'}]) if i['addr'] not in ['127.0.0.1'] ]

            ret["data"]["swap"] = {
                "exists": os.path.isfile("/my_swap")
            }

            if ret["data"]["swap"]["exists"]:
                ret["data"]["swap"]["size"] = os.path.getsize("/my_swap")
                ret["data"]["swap"]["on"] = "my_swap" in subprocess.check_output(['sudo', 'swapon', '-s'])
        except Exception as e:
            code = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            ret["data"] = e.message

        ret["code"] = code

        return ret

      
      
    def get_calibration_data( self ):
        ret = { "code":LinuxCNCServerCommand.REPLY_COMMAND_OK, "data":"" }
        try:
          tmpDir = tempfile.mkdtemp()

          shutil.copy(CALIBRATION_OVERLAY_FILE, tmpDir)
          shutil.copy(A_COMP_FILE, tmpDir)
          shutil.copy(B_COMP_FILE, tmpDir)

          shutil.make_archive(os.path.join(application_path,"static/calibration"), "zip", tmpDir)

          ret['data'] = 'static/calibration.zip'

          shutil.rmtree(tmpDir)
        except Exception as ex:
          print "exception", ex
          ret['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
          ret['data'] = ''
        return ret
      
    def get_halgraph( self ):
        ret = { "code":LinuxCNCServerCommand.REPLY_COMMAND_OK, "data":"" }
        try:
            analyzer = MakeHALGraph.HALAnalyzer()
            analyzer.parse_pins()
            analyzer.write_svg( os.path.join(application_path,"static/halgraph.svg") )
            ret['data'] = 'static/halgraph.svg'
        except:        
            ret['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            ret['data'] = ''
        return ret

    def get_hal_binding( self ):
        ret = { "code":LinuxCNCServerCommand.REPLY_COMMAND_OK, "data":"" }
        if self.halBinding is None:
            try:
                if self.name.find('halpin_') is 0:
                    self.halBinding = machinekit.hal.Pin( self.name[7:] )
                else:
                    self.halBinding = machinekit.hal.Signal( self.name[7:] )
            except RuntimeError as ex:
                print 'RuntimeError error binding StatusItem attribute to HAL object: %s' % (ex)
                ret['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
                ret['data'] = ''
                return ret
        try:
            ret['data'] = self.halBinding.get()
        except Exception as ex:
            print 'Exception getting StatusItem HAL Pin value: %s' % (ex)
            ret['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            ret['data'] = ''
        return ret


    # called in on_new_poll to update the current value of a status item
    def get_cur_status_value( self, linuxcnc_status_poller, item_index, command_dict, async_buffer=None, async_lock=None ):
        global lastLCNCerror

        ret = { "code":LinuxCNCServerCommand.REPLY_COMMAND_OK, "data":"" } 
        try:
            if (self.name == 'running'):
                if linuxcnc_status_poller.linuxcnc_is_alive:
                    ret['data'] = 1
                else:
                    ret['data'] = 0
                return ret
                
            if (not linuxcnc_status_poller.linuxcnc_is_alive and self.requiresLinuxCNCUp ):
                ret = { "code":LinuxCNCServerCommand.REPLY_LINUXCNC_NOT_RUNNING, "data":"Server is not running." }
                return ret

            if (not self.coreLinuxCNCVariable):

                # these are the "special" variables, not using the LinuxCNC status object
                if (self.name.find('halpin_') is 0) or (self.name.find('halsig_') is 0):
                    ret = self.get_hal_binding()
                    if self.name.find('halpin_hss_sensors') is 0:
                        if( self.name.find('pressure') != -1 ):
                          self.update_hss_sensor_data(ret['data'], pressureData, 0.001)
                        elif( self.name.find('temperature') != -1 ):
                          self.update_hss_sensor_data(ret['data'], temperatureData, 0.1)
                elif (self.name.find('backplot_async') is 0):
                     ret = self.backplot_async(async_buffer, async_lock,linuxcnc_status_poller)
                elif (self.name.find('backplot') is 0):
                    ret['data'] = self.backplot()
                elif (self.name == 'ini_file_name'):
                    ret['data'] = INI_FILENAME
                elif (self.name == 'file_content'):
                    ret['data'] = self.read_gcode_file(linuxcnc_status_poller.linuxcnc_status.file)
                elif (self.name == 'versions'):
                    ret = self.get_versions()
                elif (self.name == 'current_version'):
                    ret = self.get_current_version()
                elif (self.name == 'github_connection'):
                    ret = self.test_github_connection()
                elif (self.name == 'ls'):
                    ret = self.list_gcode_files( command_dict.get("directory", None) )
                elif (self.name == 'usb_detected'):
                    ret = self.detect_usb()
                elif (self.name == 'usb_map'):
                    ret = self.map_usb()
                elif (self.name == 'halgraph'):
                    ret = self.get_halgraph()
                elif (self.name == 'calibration_data'):
                    ret = self.get_calibration_data()
                elif (self.name == 'system_status'):
                    ret = self.get_system_status()
                elif (self.name == 'config'):
                    ret = StatusItem.get_ini_data()
                elif (self.name == 'config_overlay'):
                    ret = StatusItem.get_overlay_data()
                elif (self.name == 'config_item'):
                    ret = StatusItem.get_ini_data_item(command_dict.get("section", ''),command_dict.get("parameter", ''))
                elif (self.name == 'halfile'):
                    ret = self.get_hal_file( command_dict.get("filename", '') )
                elif (self.name == 'client_config'):
                    ret = self.get_client_config()
                elif (self.name == 'compensation'):
                    ret = self.get_compensation()
                elif (self.name == 'users'):
                    ret = self.get_users()
                elif (self.name == 'board_revision'):
                    ret['data'] = BOARD_REVISION
                elif (self.name == 'dogtag'):
                    ret['data'] = subprocess.check_output(['cat', '/etc/dogtag']).strip()
                elif (self.name == 'error'):
                    ret['data'] = lastLCNCerror
                elif (self.name == 'rtc_seconds'):
                    if linuxcnc_status_poller.rtc_seconds_pin:
                        ret['data'] = linuxcnc_status_poller.rtc_seconds_pin.get()
                elif (self.name == 'rotary_motion_only'):
                    ret['data'] = self.check_if_rotary_motion_only() 
                elif (self.name == 'pressure_data'):
                    ret['data'] = pressureData[:]
                elif (self.name == 'temperature_data'):
                    ret['data'] = temperatureData[:]
            else:
                # Variables that use the LinuxCNC status poller
                if (self.isarray):
                    ret['data'] = (linuxcnc_status_poller.linuxcnc_status.__getattribute__( self.name ))[item_index]
                else:
                    ret['data'] = linuxcnc_status_poller.linuxcnc_status.__getattribute__( self.name )

        except Exception as ex :
            ret['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            ret['data'] = ''
        return ret

tool_table_entry_type = type( linuxcnc.stat().tool_table[0] )
tool_table_length = len(linuxcnc.stat().tool_table)
axis_length = len(linuxcnc.stat().axis)
class StatusItemEncoder(json.JSONEncoder):
    def default(self, obj):
        global tool_table_entry_type
        if isinstance(obj, tool_table_entry_type):
            return list(obj)
        if isinstance(obj, StatusItem):
            return obj.to_json_compatible_form()
        if isinstance(obj, CommandItem):
            return { "name":obj.name, "paramTypes":obj.paramTypes, "help":obj.help }
        return json.JSONEncoder.default(self, obj)



# *****************************************************
# Global list of possible status items from linuxcnc
# *****************************************************
StatusItems = {}
StatusItem( name='acceleration',             watchable=True, valtype='float',   help='Default acceleration.  Reflects INI file value [TRAJ]DEFAULT_ACCELERATION' ).register_in_dict( StatusItems )
StatusItem( name='active_queue',             watchable=True, valtype='int'  ,   help='Number of motions blending' ).register_in_dict( StatusItems )
StatusItem( name='actual_position',          watchable=True, valtype='float[]', help='Current trajectory position. Array of floats: (x y z a b c u v w). In machine units.' ).register_in_dict( StatusItems )
StatusItem( name='adaptive_feed_enabled',    watchable=True, valtype='int',     help='status of adaptive feedrate override' ).register_in_dict( StatusItems )
StatusItem( name='ain',                      watchable=True, valtype='float[]', help='current value of the analog input pins' ).register_in_dict( StatusItems )
StatusItem( name='angular_units',            watchable=True, valtype='string' , help='From [TRAJ]ANGULAR_UNITS ini value' ).register_in_dict( StatusItems )
StatusItem( name='aout',                     watchable=True, valtype='float[]', help='Current value of the analog output pins' ).register_in_dict( StatusItems )
StatusItem( name='axes',                     watchable=True, valtype='int' ,    help='From [TRAJ]AXES ini value' ).register_in_dict( StatusItems )
StatusItem( name='axis_mask',                watchable=True, valtype='int' ,    help='Mask of axis available. X=1, Y=2, Z=4 etc.' ).register_in_dict( StatusItems )
StatusItem( name='block_delete',             watchable=True, valtype='bool' ,   help='Block delete currently on/off' ).register_in_dict( StatusItems )
StatusItem( name='command',                  watchable=True, valtype='string' , help='Currently executing command' ).register_in_dict( StatusItems )
StatusItem( name='current_line',             watchable=True, valtype='int' ,    help='Currently executing line' ).register_in_dict( StatusItems )
StatusItem( name='current_vel',              watchable=True, valtype='float' ,  help='Current velocity in cartesian space' ).register_in_dict( StatusItems )
StatusItem( name='cycle_time',               watchable=True, valtype='float' ,  help='From [TRAJ]CYCLE_TIME ini value' ).register_in_dict( StatusItems )
StatusItem( name='debug',                    watchable=True, valtype='int' ,    help='Debug flag' ).register_in_dict( StatusItems )
StatusItem( name='delay_left',               watchable=True, valtype='float' ,  help='remaining time on dwell (G4) command, seconds' ).register_in_dict( StatusItems )
StatusItem( name='din',                      watchable=True, valtype='int[]' ,  help='current value of the digital input pins' ).register_in_dict( StatusItems )
StatusItem( name='distance_to_go',           watchable=True, valtype='float' ,  help='remaining distance of current move, as reported by trajectory planner, in cartesian space' ).register_in_dict( StatusItems )
StatusItem( name='dout',                     watchable=True, valtype='int[]' ,  help='current value of the digital output pins' ).register_in_dict( StatusItems )
StatusItem( name='dtg',                      watchable=True, valtype='float[]', help='remaining distance of current move, as reported by trajectory planner, as a pose (tuple of 9 floats). ' ).register_in_dict( StatusItems )
StatusItem( name='echo_serial_number',       watchable=True, valtype='int' ,    help='The serial number of the last completed command sent by a UI to task. All commands carry a serial number. Once the command has been executed, its serial number is reflected in echo_serial_number' ).register_in_dict( StatusItems )
StatusItem( name='enabled',                  watchable=True, valtype='int' ,    help='trajectory planner enabled flag' ).register_in_dict( StatusItems )
StatusItem( name='estop',                    watchable=True, valtype='int' ,    help='estop flag' ).register_in_dict( StatusItems )
StatusItem( name='exec_state',               watchable=True, valtype='int' ,    help='Task execution state.  EMC_TASK_EXEC_ERROR = 1, EMC_TASK_EXEC_DONE = 2, EMC_TASK_EXEC_WAITING_FOR_MOTION = 3, EMC_TASK_EXEC_WAITING_FOR_MOTION_QUEUE = 4,EMC_TASK_EXEC_WAITING_FOR_IO = 5, EMC_TASK_EXEC_WAITING_FOR_MOTION_AND_IO = 7,EMC_TASK_EXEC_WAITING_FOR_DELAY = 8, EMC_TASK_EXEC_WAITING_FOR_SYSTEM_CMD = 9, EMC_TASK_EXEC_WAITING_FOR_SPINDLE_ORIENTED = 10' ).register_in_dict( StatusItems )
StatusItem( name='feed_hold_enabled',        watchable=True, valtype='int' ,    help='enable flag for feed hold' ).register_in_dict( StatusItems )
StatusItem( name='feed_override_enabled',    watchable=True, valtype='int' ,    help='enable flag for feed override' ).register_in_dict( StatusItems )
StatusItem( name='feedrate',                 watchable=True, valtype='float' ,  help='current feedrate' ).register_in_dict( StatusItems )
StatusItem( name='file',                     watchable=True, valtype='string' , help='currently executing gcode file' ).register_in_dict( StatusItems )
StatusItem( name='file_content',             coreLinuxCNCVariable=False, watchable=False,valtype='string' , help='currently executing gcode file contents' ).register_in_dict( StatusItems )
StatusItem( name='versions',                 requiresLinuxCNCUp=False, coreLinuxCNCVariable=False, watchable=False,valtype='string[]' , help='available PocketNC versions (list of tags available in git repository)').register_in_dict( StatusItems )
StatusItem( name='current_version',          requiresLinuxCNCUp=False, coreLinuxCNCVariable=False, watchable=False,valtype='string' , help='current PocketNC version (current tag in git repository)' ).register_in_dict( StatusItems )
StatusItem( name='board_revision',          requiresLinuxCNCUp=False, coreLinuxCNCVariable=False, watchable=True,valtype='string' , help='current board revision' ).register_in_dict( StatusItems )
StatusItem( name='dogtag',          requiresLinuxCNCUp=False, coreLinuxCNCVariable=False, watchable=True,valtype='string' , help='dogtag' ).register_in_dict( StatusItems )
StatusItem( name='flood',                    watchable=True, valtype='int' ,    help='flood enabled' ).register_in_dict( StatusItems )
StatusItem( name='g5x_index',                watchable=True, valtype='int' ,    help='currently active coordinate system, G54=0, G55=1 etc.' ).register_in_dict( StatusItems )
StatusItem( name='g5x_offset',               watchable=True, valtype='float[]', help='offset of the currently active coordinate system, a pose' ).register_in_dict( StatusItems )
StatusItem( name='g92_offset',               watchable=True, valtype='float[]', help='pose of the current g92 offset' ).register_in_dict( StatusItems )
StatusItem( name='gcodes',                   watchable=True, valtype='int[]' ,  help='currently active G-codes. Tuple of 16 ints.' ).register_in_dict( StatusItems )
StatusItem( name='homed',                    watchable=True, valtype='int' ,    help='flag for homed state' ).register_in_dict( StatusItems )
StatusItem( name='id',                       watchable=True, valtype='int' ,    help='currently executing motion id' ).register_in_dict( StatusItems )
StatusItem( name='inpos',                    watchable=True, valtype='int' ,    help='machine-in-position flag' ).register_in_dict( StatusItems )
StatusItem( name='input_timeout',            watchable=True, valtype='int' ,    help='flag for M66 timer in progress' ).register_in_dict( StatusItems )
StatusItem( name='interp_state',             watchable=True, valtype='int' ,    help='Current state of RS274NGC interpreter.  EMC_TASK_INTERP_IDLE = 1,EMC_TASK_INTERP_READING = 2,EMC_TASK_INTERP_PAUSED = 3,EMC_TASK_INTERP_WAITING = 4' ).register_in_dict( StatusItems )
StatusItem( name='interpreter_errcode',      watchable=True, valtype='int' ,    help='Current RS274NGC interpreter return code. INTERP_OK=0, INTERP_EXIT=1, INTERP_EXECUTE_FINISH=2, INTERP_ENDFILE=3, INTERP_FILE_NOT_OPEN=4, INTERP_ERROR=5' ).register_in_dict( StatusItems )
StatusItem( name='joint_actual_position',    watchable=True, valtype='float[]' ,help='Actual joint positions' ).register_in_dict( StatusItems )
StatusItem( name='joint_position',           watchable=True, valtype='float[]', help='Desired joint positions' ).register_in_dict( StatusItems )
StatusItem( name='kinematics_type',          watchable=True, valtype='int' ,    help='identity=1, serial=2, parallel=3, custom=4 ' ).register_in_dict( StatusItems )
StatusItem( name='limit',                    watchable=True, valtype='int[]' ,  help='Tuple of axis limit masks. minHardLimit=1, maxHardLimit=2, minSoftLimit=4, maxSoftLimit=8' ).register_in_dict( StatusItems )
StatusItem( name='linear_units',             watchable=True, valtype='int' ,    help='reflects [TRAJ]LINEAR_UNITS ini value' ).register_in_dict( StatusItems )
StatusItem( name='lube',                     watchable=True, valtype='int' ,    help='lube on flag' ).register_in_dict( StatusItems )
StatusItem( name='lube_level',               watchable=True, valtype='int' ,    help='reflects iocontrol.0.lube_level' ).register_in_dict( StatusItems )
StatusItem( name='max_acceleration',         watchable=True, valtype='float' ,  help='Maximum acceleration. reflects [TRAJ]MAX_ACCELERATION ' ).register_in_dict( StatusItems )
StatusItem( name='max_velocity',             watchable=True, valtype='float' ,  help='Maximum velocity, float. reflects [TRAJ]MAX_VELOCITY.' ).register_in_dict( StatusItems )
StatusItem( name='mcodes',                   watchable=True, valtype='int[]' ,  help='currently active M-codes. tuple of 10 ints.' ).register_in_dict( StatusItems )
StatusItem( name='mist',                     watchable=True, valtype='int' ,    help='mist on flag' ).register_in_dict( StatusItems )
StatusItem( name='motion_line',              watchable=True, valtype='int' ,    help='source line number motion is currently executing' ).register_in_dict( StatusItems )
StatusItem( name='motion_mode',              watchable=True, valtype='int' ,    help='motion mode' ).register_in_dict( StatusItems )
StatusItem( name='motion_type',              watchable=True, valtype='int' ,    help='Trajectory planner mode. EMC_TRAJ_MODE_FREE = 1 = independent-axis motion, EMC_TRAJ_MODE_COORD = 2 coordinated-axis motion, EMC_TRAJ_MODE_TELEOP = 3 = velocity based world coordinates motion' ).register_in_dict( StatusItems )
StatusItem( name='optional_stop',            watchable=True, valtype='int' ,    help='option stop flag' ).register_in_dict( StatusItems )
StatusItem( name='paused',                   watchable=True, valtype='int' ,    help='motion paused flag' ).register_in_dict( StatusItems )
StatusItem( name='pocket_prepped',           watchable=True, valtype='int' ,    help='A Tx command completed, and this pocket is prepared. -1 if no prepared pocket' ).register_in_dict( StatusItems )
StatusItem( name='position',                 watchable=True, valtype='float[]', help='Trajectory position, a pose.' ).register_in_dict( StatusItems )
StatusItem( name='probe_tripped',            watchable=True, valtype='int' ,    help='Flag, true if probe has tripped (latch)' ).register_in_dict( StatusItems )
StatusItem( name='probe_val',                watchable=True, valtype='int' ,    help='reflects value of the motion.probe-input pin' ).register_in_dict( StatusItems )
StatusItem( name='probed_position',          watchable=True, valtype='float[]', help='position where probe tripped' ).register_in_dict( StatusItems )
StatusItem( name='probing',                  watchable=True, valtype='int' ,    help='flag, true if a probe operation is in progress' ).register_in_dict( StatusItems )
StatusItem( name='program_units',            watchable=True, valtype='int' ,    help='one of CANON_UNITS_INCHES=1, CANON_UNITS_MM=2, CANON_UNITS_CM=3' ).register_in_dict( StatusItems )
StatusItem( name='queue',                    watchable=True, valtype='int' ,    help='current size of the trajectory planner queue' ).register_in_dict( StatusItems )
StatusItem( name='queue_full',               watchable=True, valtype='int' ,    help='the trajectory planner queue is full' ).register_in_dict( StatusItems )
StatusItem( name='read_line',                watchable=True, valtype='int' ,    help='line the RS274NGC interpreter is currently reading' ).register_in_dict( StatusItems )
StatusItem( name='rotation_xy',              watchable=True, valtype='float' ,  help='current XY rotation angle around Z axis' ).register_in_dict( StatusItems )
StatusItem( name='settings',                 watchable=True, valtype='float[]', help='Current interpreter settings.  settings[0] = sequence number, settings[1] = feed rate, settings[2] = speed' ).register_in_dict( StatusItems )
StatusItem( name='spindle_brake',            watchable=True, valtype='int' ,    help='spindle brake flag' ).register_in_dict( StatusItems )
StatusItem( name='spindle_direction',        watchable=True, valtype='int' ,    help='rotational direction of the spindle. forward=1, reverse=-1' ).register_in_dict( StatusItems )
StatusItem( name='spindle_enabled',          watchable=True, valtype='int' ,    help='spindle enabled flag' ).register_in_dict( StatusItems )
StatusItem( name='spindle_increasing',       watchable=True, valtype='int' ,    help='' ).register_in_dict( StatusItems )
StatusItem( name='spindle_override_enabled', watchable=True, valtype='int' ,    help='spindle override enabled flag' ).register_in_dict( StatusItems )
StatusItem( name='spindle_speed',            watchable=True, valtype='float' ,  help='spindle speed value, rpm, > 0: clockwise, < 0: counterclockwise' ).register_in_dict( StatusItems )
StatusItem( name='spindlerate',              watchable=True, valtype='float' ,  help='spindle speed override scale' ).register_in_dict( StatusItems )
StatusItem( name='state',                    watchable=True, valtype='int' ,    help='current command execution status, int. One of RCS_DONE=1, RCS_EXEC=2, RCS_ERROR=3' ).register_in_dict( StatusItems )
StatusItem( name='task_mode',                watchable=True, valtype='int' ,    help='current task mode, int. one of MODE_MDI=3, MODE_AUTO=2, MODE_MANUAL=1' ).register_in_dict( StatusItems )
StatusItem( name='task_paused',              watchable=True, valtype='int' ,    help='task paused flag' ).register_in_dict( StatusItems )
StatusItem( name='task_state',               watchable=True, valtype='int' ,    help='Current task state. one of STATE_ESTOP=1, STATE_ESTOP_RESET=2, STATE_ON=4, STATE_OFF=3' ).register_in_dict( StatusItems )
StatusItem( name='tool_in_spindle',          watchable=True, valtype='int' ,    help='current tool number' ).register_in_dict( StatusItems )
StatusItem( name='tool_offset',              watchable=True, valtype='float' ,  help='offset values of the current tool' ).register_in_dict( StatusItems )
StatusItem( name='velocity',                 watchable=True, valtype='float' ,  help='default velocity, float. reflects [TRAJ]DEFAULT_VELOCITY' ).register_in_dict( StatusItems )

StatusItem( name='halpin_halui.max-velocity.value',    coreLinuxCNCVariable=False, watchable=True, valtype='float',help='maxvelocity' ).register_in_dict( StatusItems )
StatusItem( name='halpin_spindle_voltage.speed_measured',    coreLinuxCNCVariable=False, watchable=True, valtype='float',help='Measured spindle speed using clock pin' ).register_in_dict( StatusItems )

StatusItem( name='halpin_hss_warmup.full_warmup_needed',    coreLinuxCNCVariable=False, watchable=True, valtype='bool',help='Flag that indicates high speed spindle needs to be warmed up.' ).register_in_dict( StatusItems )
StatusItem( name='halpin_hss_warmup.warmup_needed',    coreLinuxCNCVariable=False, watchable=True, valtype='bool',help='Flag that indicates high speed spindle needs to be warmed up.' ).register_in_dict( StatusItems )
StatusItem( name='halpin_hss_warmup.performing_warmup',    coreLinuxCNCVariable=False, watchable=True, valtype='bool',help='Flag that indicates the high speed spindle warm up is in process.' ).register_in_dict( StatusItems )
StatusItem( name='halpin_hss_sensors.pressure',    coreLinuxCNCVariable=False, watchable=True, valtype='float',help='Pressure in MPa as read by MPRLS.' ).register_in_dict( StatusItems )
StatusItem( name='halpin_hss_sensors.temperature',    coreLinuxCNCVariable=False, watchable=True, valtype='float',help='Temperature in C as read by MCP9808' ).register_in_dict( StatusItems )
StatusItem( name='pressure_data',            coreLinuxCNCVariable=False, watchable=True, valtype='float[]', help='Pressure data history, back as far as one hour' ).register_in_dict( StatusItems )
StatusItem( name='temperature_data',         coreLinuxCNCVariable=False, watchable=True, valtype='float[]', help='Temperature data history, back as far as one hour. Key is timestamp.' ).register_in_dict( StatusItems )

StatusItem( name='ls',                       coreLinuxCNCVariable=False, watchable=True, valtype='string[]',help='Get a list of gcode files.  Optionally specify directory with "directory":"string", or default directory will be used.  Only *.ngc files will be listed.' ).register_in_dict( StatusItems )
StatusItem( name='usb_detected',             coreLinuxCNCVariable=False, watchable=True, valtype='bool',help='Checks if any USB drives have been mounted at one of the USB sub-directories in /media' ).register_in_dict( StatusItems )
StatusItem( name='usb_map',                  coreLinuxCNCVariable=False, watchable=False, valtype='dict',help='Create a nested dictionary that represents the folder structure of a USB device that has been mounted at /media/usb[0-7]' ).register_in_dict( StatusItems )
StatusItem( name='backplot',                 coreLinuxCNCVariable=False, watchable=False, valtype='string[]',help='Backplot information.  Potentially very large list of lines.' ).register_in_dict( StatusItems )
StatusItem( name='backplot_async',           coreLinuxCNCVariable=False, watchable=False, valtype='string[]', isAsync=True, help='Backplot information.  Potentially very large list of lines.' ).register_in_dict( StatusItems )
StatusItem( name='config',                   coreLinuxCNCVariable=False, watchable=False, valtype='dict',    help='Config (ini) file contents.', requiresLinuxCNCUp=False  ).register_in_dict( StatusItems )
StatusItem( name='config_overlay',           coreLinuxCNCVariable=False, watchable=False, valtype='dict',    help='Config Overlay (ini) file contents.', requiresLinuxCNCUp=False  ).register_in_dict( StatusItems )
StatusItem( name='config_item',              coreLinuxCNCVariable=False, watchable=False, valtype='dict',    help='Specific section/name from the config file.  Pass in section=??? and name=???.', requiresLinuxCNCUp=False  ).register_in_dict( StatusItems )
StatusItem( name='halfile',                  coreLinuxCNCVariable=False, watchable=False, valtype='string',  help='Contents of a hal file.  Pass in filename=??? to specify the hal file name', requiresLinuxCNCUp=False ).register_in_dict( StatusItems )
StatusItem( name='halgraph',                 coreLinuxCNCVariable=False, watchable=False, valtype='string',  help='Filename of the halgraph generated from the currently running instance of LinuxCNC.  Filename will be "halgraph.svg"' ).register_in_dict( StatusItems )
StatusItem( name='calibration_data',         coreLinuxCNCVariable=False, watchable=False, valtype='string',  help='Filename of the calibration.zip file generated from the current machine specific calibration data.' ).register_in_dict( StatusItems )
StatusItem( name='system_status',            coreLinuxCNCVariable=False, watchable=False, valtype='dict',  help='System status information, such as IP addresses, disk usage, etc.' ).register_in_dict( StatusItems )
StatusItem( name='ini_file_name',            coreLinuxCNCVariable=False, watchable=True,  valtype='string',  help='INI file to use for next LinuxCNC start.', requiresLinuxCNCUp=False ).register_in_dict( StatusItems )
StatusItem( name='client_config',            coreLinuxCNCVariable=False, watchable=True,  valtype='string',  help='Client Configuration.', requiresLinuxCNCUp=False ).register_in_dict( StatusItems )
StatusItem( name='users',                    coreLinuxCNCVariable=False, watchable=True,  valtype='string',  help='Web server user list.', requiresLinuxCNCUp=False ).register_in_dict( StatusItems )

StatusItem( name='compensation',             coreLinuxCNCVariable=False, watchable=False,  valtype='dict',  help='a and b axis compensation', requiresLinuxCNCUp=False ).register_in_dict( StatusItems )

StatusItem( name='error',                    coreLinuxCNCVariable=False, watchable=True,  valtype='dict',    help='Error queue.' ).register_in_dict( StatusItems )
StatusItem( name='running',                  coreLinuxCNCVariable=False, watchable=True,  valtype='int',     help='True if linuxcnc is up and running.', requiresLinuxCNCUp=False ).register_in_dict( StatusItems )
StatusItem( name='halsig_interlockClosed',   coreLinuxCNCVariable=False, watchable=True,  valtype='string',     help='Monitors status of interlock. Also true if not equipped with interlock.' ).register_in_dict( StatusItems )
StatusItem( name='halpin_interlock.program-paused-by-interlock',   coreLinuxCNCVariable=False, watchable=True,  valtype='string',     help='If the interlock is opened while a program is loaded (running or paused), the interlock will inhibit the spindle and feed until its release pin is set to TRUE.' ).register_in_dict( StatusItems )

StatusItem( name='rtc_seconds',              coreLinuxCNCVariable=False, watchable=True, valtype='float', help='Run time of current cycle in seconds' ).register_in_dict( StatusItems )
StatusItem( name='rotary_motion_only',       coreLinuxCNCVariable=False, watchable=True, valtype='bool',  help='True if any rotational axis is in motion but not any linear axis.').register_in_dict( StatusItems ) 

# Array Status items
StatusItem( name='tool_table',               watchable=True, valtype='float[]', help='list of tool entries. Each entry is a sequence of the following fields: id, xoffset, yoffset, zoffset, aoffset, boffset, coffset, uoffset, voffset, woffset, diameter, frontangle, backangle, orientation', isarray=True, arraylen=tool_table_length ).register_in_dict( StatusItems )
StatusItem( name='axis',                     watchable=True, valtype='dict' ,   help='Axis Dictionary', isarray=True, arraylen=axis_length ).register_in_dict( StatusItems )
StatusItem( name='github_connection',        requiresLinuxCNCUp=False, coreLinuxCNCVariable=False, watchable=True,valtype='bool' , help='Whether connection to the PocketNC github repository can be established.' ).register_in_dict( StatusItems )


# *****************************************************
# Class to issue cnc commands
# *****************************************************
class CommandItem( object ):
    
    # Command types
    MOTION=0
    HAL=1
    SYSTEM=2
    
    def __init__( self, name=None, paramTypes=[], help='', command_type=MOTION, isasync=False ):
        self.name = name
        self.paramTypes = paramTypes
        self.help = help
        for idx in xrange(0, len(paramTypes)):
            paramTypes[idx]['ordinal'] = str(idx)
        self.type = command_type
        self.isasync = isasync

    # puts this object into the dictionary, with the key == self.name
    def register_in_dict( self, dictionary ):
        dictionary[ self.name ] = self

    def temp_set_ini_data( self, commandDict, linuxcnc_status_poller ):
        global HAL_INTERFACE
        global linuxcnc_command

        reply = { 'code': LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND, 'rowId': commandDict['data']['rowId'] }

        iniitem2halpins = {
            'AXIS_0': {
                'BACKLASH': 'ini.0.backlash',
                'DIRHOLD': 'hal_pru_generic.stepgen.00.dirhold',
                'DIRSETUP': 'hal_pru_generic.stepgen.00.dirsetup',
                'FERROR': 'ini.0.ferror',
                'MAX_ACCELERATION': 'ini.0.max_acceleration',
                'MAX_VELOCITY': 'ini.0.max_velocity',
                'MIN_FERROR': 'ini.0.min_ferror',
                'MAX_LIMIT': 'ini.0.max_limit',
                'MIN_LIMIT': 'ini.0.min_limit',
                'SCALE': 'hal_pru_generic.stepgen.00.position-scale',
                'STEPGEN_MAX_ACC': 'hal_pru_generic.stepgen.00.maxaccel',
                'STEPGEN_MAX_VEL': 'hal_pru_generic.stepgen.00.maxvel',
                'STEPLEN': 'hal_pru_generic.stepgen.00.steplen',
                'STEPSPACE': 'hal_pru_generic.stepgen.00.stepspace',
                'HOME_OFFSET': 'axis.0.home-offset'
            },
            'AXIS_1': {
                'BACKLASH': 'ini.1.backlash',
                'DIRHOLD': 'hal_pru_generic.stepgen.01.dirhold',
                'DIRSETUP': 'hal_pru_generic.stepgen.01.dirsetup',
                'FERROR': 'ini.1.ferror',
                'MAX_ACCELERATION': 'ini.1.max_acceleration',
                'MAX_VELOCITY': 'ini.1.max_velocity',
                'MIN_FERROR': 'ini.1.min_ferror',
                'MAX_LIMIT': 'ini.1.max_limit',
                'MIN_LIMIT': 'ini.1.min_limit',
                'SCALE': 'hal_pru_generic.stepgen.01.position-scale',
                'STEPGEN_MAX_ACC': 'hal_pru_generic.stepgen.01.maxaccel',
                'STEPGEN_MAX_VEL': 'hal_pru_generic.stepgen.01.maxvel',
                'STEPLEN': 'hal_pru_generic.stepgen.01.steplen',
                'STEPSPACE': 'hal_pru_generic.stepgen.01.stepspace',
                'HOME_OFFSET': 'axis.1.home-offset'
            },
            'AXIS_2': {
                'BACKLASH': 'ini.2.backlash',
                'DIRHOLD': 'hal_pru_generic.stepgen.02.dirhold',
                'DIRSETUP': 'hal_pru_generic.stepgen.02.dirsetup',
                'FERROR': 'ini.2.ferror',
                'MAX_ACCELERATION': 'ini.2.max_acceleration',
                'MAX_VELOCITY': 'ini.2.max_velocity',
                'MIN_FERROR': 'ini.2.min_ferror',
                'MAX_LIMIT': 'ini.2.max_limit',
                'MIN_LIMIT': 'ini.2.min_limit',
                'SCALE': 'hal_pru_generic.stepgen.02.position-scale',
                'STEPGEN_MAX_ACC': 'hal_pru_generic.stepgen.02.maxaccel',
                'STEPGEN_MAX_VEL': 'hal_pru_generic.stepgen.02.maxvel',
                'STEPLEN': 'hal_pru_generic.stepgen.02.steplen',
                'STEPSPACE': 'hal_pru_generic.stepgen.02.stepspace',
                'HOME_OFFSET': 'axis.2.home-offset'
            },
            'AXIS_3': {
                'BACKLASH': 'ini.3.backlash',
                'DIRHOLD': 'hal_pru_generic.stepgen.03.dirhold',
                'DIRSETUP': 'hal_pru_generic.stepgen.03.dirsetup',
                'FERROR': 'ini.3.ferror',
                'MAX_ACCELERATION': 'ini.3.max_acceleration',
                'MAX_VELOCITY': 'ini.3.max_velocity',
                'MIN_FERROR': 'ini.3.min_ferror',
                'MAX_LIMIT': 'ini.3.max_limit',
                'MIN_LIMIT': 'ini.3.min_limit',
                'SCALE': 'hal_pru_generic.stepgen.03.position-scale',
                'STEPGEN_MAX_ACC': 'hal_pru_generic.stepgen.03.maxaccel',
                'STEPGEN_MAX_VEL': 'hal_pru_generic.stepgen.03.maxvel',
                'STEPLEN': 'hal_pru_generic.stepgen.03.steplen',
                'STEPSPACE': 'hal_pru_generic.stepgen.03.stepspace',
                'HOME_OFFSET': 'axis.3.home-offset'
            },
            'AXIS_4': {
                'BACKLASH': 'ini.4.backlash',
                'DIRHOLD': 'hal_pru_generic.stepgen.04.dirhold',
                'DIRSETUP': 'hal_pru_generic.stepgen.04.dirsetup',
                'FERROR': 'ini.4.ferror',
                'MAX_ACCELERATION': 'ini.4.max_acceleration',
                'MAX_VELOCITY': 'ini.4.max_velocity',
                'MIN_FERROR': 'ini.4.min_ferror',
                'MAX_LIMIT': 'ini.4.max_limit',
                'MIN_LIMIT': 'ini.4.min_limit',
                'SCALE': 'hal_pru_generic.stepgen.04.position-scale',
                'STEPGEN_MAX_ACC': 'hal_pru_generic.stepgen.04.maxaccel',
                'STEPGEN_MAX_VEL': 'hal_pru_generic.stepgen.04.maxvel',
                'STEPLEN': 'hal_pru_generic.stepgen.04.steplen',
                'STEPSPACE': 'hal_pru_generic.stepgen.04.stepspace',
                'HOME_OFFSET': 'axis.4.home-offset'
            }
        }

        data = commandDict['data']
        section = iniitem2halpins.get(data['section'])
        if section:
            pin = section.get(data['name'])
            if pin:
                was_on = False
                if linuxcnc_status_poller.linuxcnc_status.task_state == linuxcnc.STATE_ON:
                    was_on = True
                    linuxcnc_command.state(linuxcnc.STATE_OFF)
                    while linuxcnc_status_poller.linuxcnc_status.task_state == linuxcnc.STATE_ON:
                        print "waiting for power to turn off..."
                        time.sleep(.1)
                        linuxcnc_status_poller.poll_update()

                try:
                    HAL_INTERFACE.set_p(pin, data['value'])
                    if was_on:
                        linuxcnc_command.state(linuxcnc.STATE_ON)
                    reply['code'] = LinuxCNCServerCommand.REPLY_COMMAND_OK
                except Exception as ex:
                    print "Error setting hal pin"
                    print ex
            else:
                print "No pin found for variable %s in section %s" % (data['name'], data['section'])
        else:
            print "No section %s" % (data['section'])

        return reply

    # called in a "put_config" command to write INI data to INI file, completely re-writing the file
    def put_ini_data( self, commandDict ):
        global INI_FILENAME
        global INI_DEFAULTS_FILE
        global CALIBRATION_OVERLAY_FILE
        reply = { 'code': LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }
        try:
            overlay = commandDict['data']

            write_ini_data(overlay, CALIBRATION_OVERLAY_FILE)
            reply['code'] = LinuxCNCServerCommand.REPLY_COMMAND_OK
        except:
            print "Unexpected error:", sys.exc_info()[0]
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        finally:
            try:
                inifile.close()
            except:
                pass

        return reply

    def toggle_v1_v2revP(self):
      global BOARD_REVISION
      try:
        if BOARD_REVISION == "v1revH":
          print "Clearing version file"
          boardRevision.clearVersionFile()
        else:
          print "Writing version file"
          boardRevision.writeVersionFile("v1revH")
        return self.restart_linuxcnc_and_rockhopper()
      except e:
        print e
        return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

    def set_version(self, version):
        global POCKETNC_DIRECTORY

        try:
           subprocess.call(['./updateScript.sh', version], cwd=POCKETNC_DIRECTORY)
        except:
            return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

        return { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'refresh_ui' }


    def set_date(self, dateString):
        try:
          set_date_string(dateString)
        except Exception as e:
           return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND, "data": e.message }

        return { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'set_date' }


    #Create a swap file, allocate space, set permissions, and make entry in /etc/fstab
    def create_swap(self, commandDict):
      reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'create_swap', 'data' : { 'isSwapCmd' : 'true' } }
      try:
        #df reports disk space with units of KiB
        diskSpaceMb = StatusItems['system_status'].get_system_status()['data']['disk']['available'] * 0.001024
        swapSizeMb = int(commandDict['0'])
        #We've decided on 256 MB free as a minimum for now. -JMD 6/6/19
        if diskSpaceMb < ( swapSizeMb + 256 ):
          reply['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND_PARAMETER
          reply['data']['notify'] = {'text' : 'Not enough free disk space to create swap file of requested %s MB size.' % (swapSizeMb) }
          return reply
        subprocess.call(['sudo', 'fallocate', '-l', '%sMB' % (commandDict['0']), '/my_swap'], cwd=POCKETNC_DIRECTORY)
        subprocess.call(['sudo', 'chmod', '600', '/my_swap'], cwd=POCKETNC_DIRECTORY)
        subprocess.call(['sudo', 'mkswap', '/my_swap'], cwd=POCKETNC_DIRECTORY)
        fstab = subprocess.check_output(['sudo', 'cat', '/etc/fstab'], cwd=POCKETNC_DIRECTORY)
        if "/my_swap swap swap defaults 0 0" not in fstab:
          subprocess.call(['sudo', 'sh', '-c',  'echo "/my_swap swap swap defaults 0 0" >> /etc/fstab'], cwd=POCKETNC_DIRECTORY)
      except Exception as e:
        reply["code"] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND

      return reply


    def enable_swap(self, commandDict):
      reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'enable_swap', 'data' : { 'isSwapCmd' : 'true' } }
      try:
        subprocess.call(['sudo', 'swapon', '/my_swap'])
      except Exception as e:
        print 'enable exception'
        print e
        reply["code"] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND

      return reply


    def disable_swap(self, commandDict):
      reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'disable_swap', 'data' : { 'isSwapCmd' : 'true' } }
      try:
        p = subprocess.Popen(['sudo', 'swapoff', '-v', '/my_swap'], stderr=subprocess.PIPE, stdout=subprocess.PIPE )
        result, err = p.communicate()
        if 'swapoff failed: Cannot allocate memory' in err:
          reply['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND_PARAMETER
          reply['data']['notify'] = {'text' : 'The swap file cannot be disabled right now. Insufficient space available in primary RAM to hold contents of swap file.' }
      except Exception as e:
        reply["code"] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND

      return reply


    #Delete swap file and its entry in /etc/fstab
    def delete_swap(self, commandDict):
      reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'delete_swap', 'data' : { 'isSwapCmd' : 'true' } }
      try:
        subprocess.call(['sudo', 'sed', '-i', '/my_swap swap swap defaults 0 0/d', '/etc/fstab'])
        subprocess.call(['sudo', 'rm', '/my_swap'])
      except Exception as e:
        reply["code"] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND

      return reply


    def clear_logs(self, commandDict):
        try:
           subprocess.call(['sudo', 'find', '/var/log', '-name', '*.*.gz', '-exec', 'rm', '{}', ';'], cwd=POCKETNC_DIRECTORY)
           subprocess.call(['sudo', 'find', '/var/log', '-type', 'f', '-exec', 'truncate', '-s', '0', '{}', ';'], cwd=POCKETNC_DIRECTORY)
        except:
           return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

        return { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'clear_logs' }

    def clear_ncfiles(self, commandDict):
        try:
            ini_data = read_ini_data(INI_FILENAME)
            ncfiles_path = get_parameter(ini_data, "DISPLAY", "PROGRAM_PREFIX")["values"]["value"]

            subprocess.call(['find', ncfiles_path, '-type', 'f', '-exec', 'rm', '{}', ';'], cwd=POCKETNC_DIRECTORY)
        except:
            return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

        return { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'id': 'clear_ncfiles' }

    def check_for_updates(self, commandDict):
        global POCKETNC_DIRECTORY

        try:
           subprocess.call(['git', 'submodule', 'foreach', 'git', 'fetch'], cwd=POCKETNC_DIRECTORY)
           subprocess.call(['git', 'fetch', '--tags'], cwd=POCKETNC_DIRECTORY)
           subprocess.call(['git', 'fetch', '--prune', 'origin', '+refs/tags/*:refs/tags/*'], cwd=POCKETNC_DIRECTORY)
           all_versions = subprocess.check_output(['git', 'tag', '-l'], cwd=POCKETNC_DIRECTORY).split()
           all_versions.sort(key=natural_keys)
        except:
            return { "code": LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

        return { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK, 'data': all_versions, 'id': 'versions' }

    def put_compensation(self, data):
        reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK }

        a = data['data']['a']
        b = data['data']['b']

        if len(a) > 256:
            reply['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND_PARAMETER
            reply['error'] = "Too many entries in A compensation table. Attempting to set %s entries. Compensation tables can only have 256 entries." % len(a)
        elif len(b) > 256:
            reply['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND_PARAMETER
            reply['error'] = "Too many entries in B compensation table. Attempting to set %s entries. Compensation tables can only have 256 entries." % len(b)
        else:
            try:
                af = open(A_COMP_FILE, 'w')
                bf = open(B_COMP_FILE, 'w')

                for row in a:
                    af.write(" ".join([ str(v) for v in row ]))
                    af.write("\n")

                for row in b:
                    bf.write(" ".join([ str(v) for v in row ]))
                    bf.write("\n")

            except Exception as e:
                reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
                print e
            finally:
              try:
                  af.close()
                  bf.close()
              except:
                  pass

        return reply

    def put_client_config( self, key, value ):
        global CONFIG_FILENAME
        reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}

        try:
            fo = open( CONFIG_FILENAME, 'r' )
            jsonobj = json.loads( fo.read() )
            jsonobj[key] = value
        except:
            jsonobj = {}
        finally:
            try:
		fo.close()
            except:
                pass
        
        try:    
            fo = open( CONFIG_FILENAME, 'w' )
            fo.write( json.dumps(jsonobj) )
        except:
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        finally:
            try:
                fo.close()
            except:
                reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
                
        return reply
           

    def del_gcode_file(self, filename, linuxcnc_status_poller):
        global linuxcnc_command

        reply = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK }

        try:
            # strip off just the filename, if a path was given
            # we will only look in the config directory, so we ignore path
            [h,f] = os.path.split( filename )

            [openFilePath,openFile] = os.path.split( linuxcnc_status_poller.linuxcnc_status.file )
            
            path = StatusItem.get_ini_data( only_section='DISPLAY', only_name='PROGRAM_PREFIX' )['data']['parameters'][0]['values']['value']

            openDefault = StatusItem.get_ini_data( only_section='DISPLAY', only_name='OPEN_FILE' )['data']['parameters'][0]['values']['value']

            if openFilePath and os.path.samefile(openFilePath,path) and openFile == f:
                linuxcnc_command.program_open(openDefault)
            try:
                os.remove(os.path.join(path, f))
            except:
                reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        except Exception as ex:
            print ex
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        return reply         


    def clean_gcode( self, data ):
        lines = data.split('\n')
        for lineIdx, line in enumerate(lines):
            commentIdx = line.find('(py,')
            while commentIdx != -1:
                print commentIdx
                closeIdx = line.find(')', commentIdx)
                closeIdx = closeIdx if ( closeIdx != -1 ) else ( len(line) - 1 )
                line = line[:commentIdx] + line[closeIdx + 1:]
                lines[lineIdx] = line
                commentIdx = line.find('(py,')
            commentIdx = line.find(';py,')
            if commentIdx != -1:
                lines[lineIdx] = line[:commentIdx]
        
        return '\n'.join(lines)


    def put_gcode_file( self, filename, data ):
        global linuxcnc_command
 
        reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        try:
            
            # strip off just the filename, if a path was given
            # we will only look in the config directory, so we ignore path
            [h,f] = os.path.split( filename )

            path = StatusItem.get_ini_data( only_section='DISPLAY', only_name='PROGRAM_PREFIX' )['data']['parameters'][0]['values']['value']
            
            try:
                fo = open( os.path.join( path, f ), 'w' )
                data = self.clean_gcode(data);
                fo.write(data.encode('utf8'))
            except:
                reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            finally:
                try:
                    fo.close()
                except:
                    reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND

            if (reply['code'] == LinuxCNCServerCommand.REPLY_COMMAND_OK):
                (linuxcnc_command.program_open( os.path.join( path, f ) ) )
            
        except Exception as ex:
            print ex
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        return reply


    #start: T for initial chunk of file
    #end: T for final chunk of file
    #ovw: T if overwrite permission given by user
    def put_chunk_gcode_file( self, filename, data, start, end, ovw ):
        global linuxcnc_command
        global uploadingFile
        reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        try:
            # strip off just the filename, if a path was given
            # we will only look in the config directory, so we ignore path
            [h,f] = os.path.split( filename )
            path = StatusItem.get_ini_data( only_section='DISPLAY', only_name='PROGRAM_PREFIX' )['data']['parameters'][0]['values']['value']
            if( start ):
                if ( ( not ovw ) and ( os.path.isfile( os.path.join( path, f ) ) ) ):
                    reply['data'] = 'occupied'
                    return reply
                
                try:
                    shutil.rmtree( os.path.join( tempfile.gettempdir(), 'ncfiles' ) )
                except OSError:
                    pass
                os.mkdir( os.path.join( tempfile.gettempdir(), 'ncfiles' ) )
                uploadingFile = open( os.path.join( tempfile.gettempdir(), 'ncfiles', f ), 'a' )

            data = self.clean_gcode( data )
            uploadingFile.write( data.encode('utf8') ) 
            if( end ):
                if( ovw ):
                    try:
                        os.remove(os.path.join(path,f))
                    except OSError:
                        pass
                os.rename(os.path.join( tempfile.gettempdir(), 'ncfiles',  f ), os.path.join( path, f))
                uploadingFile.close()
                linuxcnc_command.program_open( os.path.join( path, f ) ) 
         
        except Exception as ex:
            print ex
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        return reply         
   

    def get_chunk_gcode_file( self, idx, size, linuxcnc_status_poller ):
        reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        try:
            f = open(linuxcnc_status_poller.linuxcnc_status.file, 'r')
            f.seek(idx)
            data = f.read(size)
            reply['data'] = data
        except ex:
            print ex
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        finally:
            f.close()
        return reply
    

    def get_gcode_file_size( self, linuxcnc_status_poller ):
        reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        try:
            reply['data'] = os.path.getsize(linuxcnc_status_poller.linuxcnc_status.file)
        except ex:
            print ex
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        return reply


    # stop the run_time_clock HAL component and set it to 0 seconds
    def reset_run_time_clock( self ):
        global HAL_INTERFACE
        reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        try:
            HAL_INTERFACE.set_p('run_time_clock.reset', 'TRUE')
        except Exception as ex:
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND

        return reply 


    # writes the specified HAL file to disk
    def put_hal_file( self, filename, data ):
        global INI_FILENAME
        global INI_FILE_PATH
        reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        try:
            # strip off just the filename, if a path was given
            # we will only look in the config directory, so we ignore path
            [h,f] = os.path.split( filename )
            if not StatusItem.check_hal_file_listed_in_ini( f ):
                reply['code']=LinuxCNCServerCommand.REPLY_ERROR_INVALID_PARAMETER
                return reply

            try:
                fo = open( os.path.join( INI_FILE_PATH, f ), 'w' )
                fo.write(data)
            except:
                reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            finally:
                try:
                    fo.close()
                except:
                    reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            
        except Exception as ex: 
            reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
        
        return reply 

    # If any USB drive is mounted, stop any processes which are accessing the drive, then unmount it.
    # The mountSlot is an integer corresponding to one of the 8 usbmount directories ('/media/usb[0,8)')
    def eject_usb( self ):
      global lastLCNCerror
      reply = {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
      try:
        usbDirBase = "/media/usb"
        usbMountPath = ""
        # On our older image (3.8-1 kernel), if using a drive with a NTFS format, physically removing the drive without first 
        # unmounting will result in usbmount failing to remove the entry from the file system, and then re-inserting the drive
        # will result in usbmount incrementing the slot. So we'll check for files in all 8 slots.
        for mountDirIdx in range(8):
          usbMountPath = usbDirBase + str( mountDirIdx )
          if ( os.path.exists(usbMountPath) and len(os.listdir(usbMountPath)) > 0 ):
            try:
              subprocess.check_output(['sudo', 'fuser', '-vmk', usbMountPath], stderr=subprocess.STDOUT )
            except subprocess.CalledProcessError as fuserExc:
              print fuserExc
              lastLCNCerror = {
                  "kind": "eject_usb",
                  "type":"error",
                  "text": "Failed to kill processes using USB drive. Output of process-kill command:\n %s" % (fuserExc.output),
                  "time": strftime("%Y-%m-%d %H:%M:%S"),
                  "id": LINUXCNCSTATUS.errorid + 1
              }
              LINUXCNCSTATUS.errorid += 1
            try:
              subprocess.check_output(['sudo', 'umount', usbMountPath], stderr=subprocess.STDOUT )
              lastLCNCerror = {
                  "kind": "eject_usb",
                  "type":"success",
                  "text": "USB drive safe to remove.",
                  "time": strftime("%Y-%m-%d %H:%M:%S"),
                  "id": LINUXCNCSTATUS.errorid + 1
              }
              LINUXCNCSTATUS.errorid += 1
            except subprocess.CalledProcessError as umountExc:
              print umountExc
              lastLCNCerror = {
                  "kind": "eject_usb",
                  "type":"error",
                  "text": "Failed to unmount USB drive. Output of unmount command:\n %s" % (umountExc.output),
                  "time": strftime("%Y-%m-%d %H:%M:%S"),
                  "id": LINUXCNCSTATUS.errorid + 1
              }
              LINUXCNCSTATUS.errorid += 1
              reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
      except Exception as ex:
        print ex
        lastLCNCerror = {
          "kind": "eject_usb",
          "type":"error",
          "text": "Failed to unmount USB drive. Exception message:\n %s" % (ex.output),
          "time": strftime("%Y-%m-%d %H:%M:%S"),
          "id": LINUXCNCSTATUS.errorid + 1
        }
        LINUXCNCSTATUS.errorid += 1
        reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
          
      return reply

    def restart_linuxcnc_and_rockhopper( self ):
        global POCKETNC_DIRECTORY
        try:
            p = subprocess.Popen( ['%s/restartPocketNC.sh' % POCKETNC_DIRECTORY] , stderr=subprocess.STDOUT )
            return {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK }
        except:
            return {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

    def interlock_release( self ):
        try:
            machinekit.hal.Pin("interlock.release").set(1)
            return {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK }
        except Exception as e:
            print e
            return {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

    def shutdown_linuxcnc( self ):
        try:
            displayname = StatusItem.get_ini_data( only_section='DISPLAY', only_name='DISPLAY' )['data']['parameters'][0]['values']['value']
            p = subprocess.Popen( ['pkill', displayname] , stderr=subprocess.STDOUT )
            return {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK }
        except:
            return {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

    def shutdown_computer( self ):
        try:
            p = subprocess.Popen( [ os.path.join(application_path, 'shutdown_computer.sh') ] , stderr=subprocess.STDOUT )
            return {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK }
        except:
            return {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }
        
    def start_linuxcnc( self ):
        global INI_FILENAME
        global INI_FILE_PATH
        p = subprocess.Popen(['pidof', '-x', 'linuxcnc'], stdout=subprocess.PIPE )
        result = p.communicate()[0]
        if len(result) > 0:
            return {'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND}
        subprocess.Popen(['linuxcnc', INI_FILENAME], stderr=subprocess.STDOUT )
        return {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}

    def add_user( self, username, password ):
        try:
            proc = subprocess.Popen(['python', 'AddUser.py', username, password], stderr=subprocess.STDOUT )
            proc.communicate()
            readUserList()
            return {'code':LinuxCNCServerCommand.REPLY_COMMAND_OK}
        except:
            pass

    def execute( self, passed_command_dict, linuxcnc_status_poller ):
        global INI_FILENAME
        global INI_FILE_PATH
        global lastLCNCerror
        global linuxcnc_command

        try:
            paramcnt = 0
            params = []

            if ((linuxcnc_command is None or (not linuxcnc_status_poller.linuxcnc_is_alive)) and not (self.type == CommandItem.SYSTEM)):
                return { 'code':LinuxCNCServerCommand.REPLY_LINUXCNC_NOT_RUNNING } 
            
            for paramDesc in self.paramTypes:
                paramval = passed_command_dict.get( paramDesc['pname'], None )
                if paramval is None:
                    paramval = passed_command_dict.get( paramDesc['ordinal'], None )
                paramtype = paramDesc['ptype']

                if (paramval is not None):
                    if (paramtype == 'lookup'):
                        params.append( linuxcnc.__getattribute__( paramval.strip() ) )
                    elif (paramtype == 'float'):
                        params.append( float( paramval ) )
                    elif (paramtype == 'int'):
                        params.append( int( paramval ) )
                    else:
                        params.append(paramval)
                else:
                    if not paramDesc['optional']:
                        return { 'code':LinuxCNCServerCommand.REPLY_MISSING_COMMAND_PARAMETER + ' ' + paramDesc['name'] }
                    else:
                        break

            if (self.type == CommandItem.MOTION):
                # Some values need to be clamped
                if (self.name == 'maxvel'):
                    params[0] = max(min(params[0], 1), 0)
                elif (self.name == 'spindleoverride'):
                    params[0] = max(min(params[0], 2), 0)
                elif (self.name == 'feedrate'):
                    params[0] = max(min(params[0], 2), 0)

                # execute command as a linuxcnc module call
                (linuxcnc_command.__getattribute__( self.name ))( *params )

            elif (self.type == CommandItem.HAL):
                # implement the command as a halcommand
                p = subprocess.Popen( ['halcmd'] + filter( lambda a: a != '', [x.strip() for x in params[0].split(' ')]), stderr=subprocess.PIPE, stdout=subprocess.PIPE, bufsize=(1024*64) )
                stdouterr = p.communicate()
                reply = {}
                reply['code'] = LinuxCNCServerCommand.REPLY_COMMAND_OK
                reply['data'] = {}
                reply['data']['out']=stdouterr[0]
                reply['data']['err']=stdouterr[1]
                return reply
            elif (self.type == CommandItem.SYSTEM):
                # command is a special system command
                reply = {}
                
                if (self.name == 'ini_file_name'):
                    INI_FILENAME = passed_command_dict.get( 'ini_file_name', INI_FILENAME )
                    [INI_FILE_PATH, x] = os.path.split( INI_FILENAME )
                    reply['code'] = LinuxCNCServerCommand.REPLY_COMMAND_OK
                elif (self.name == 'config'): 
                    reply = self.put_ini_data(passed_command_dict)
                elif (self.name == 'temp_set_config_item'): 
                    reply = self.temp_set_ini_data(passed_command_dict, linuxcnc_status_poller)
                elif (self.name == 'clear_error'):
                    lastLCNCerror = ""
                elif (self.name == 'halfile'):
                    reply = self.put_hal_file( filename=passed_command_dict.get('filename',passed_command_dict['0']).strip(), data=passed_command_dict.get('data', passed_command_dict.get['1']) )
                elif (self.name == 'shutdown'):
                    reply = self.shutdown_linuxcnc()
                elif (self.name == 'shutdown_computer'):
                    reply = self.shutdown_computer()
                elif (self.name == 'restart'):
                    reply = self.restart_linuxcnc_and_rockhopper()
                elif (self.name == 'interlock_release'):
                    reply = self.interlock_release() 
                elif (self.name == 'startup'):
                    reply = self.start_linuxcnc()
                elif (self.name == 'program_upload'):
                    reply = self.put_gcode_file(filename=passed_command_dict.get('filename',passed_command_dict['0']).strip(), data=passed_command_dict.get('data', passed_command_dict['1']))
                elif (self.name == 'program_upload_chunk'):
                    reply = self.put_chunk_gcode_file(filename=passed_command_dict.get('filename',passed_command_dict['0']).strip(), data=passed_command_dict.get('data', passed_command_dict['1']), start=passed_command_dict.get('start', passed_command_dict['2']), end=passed_command_dict.get('end', passed_command_dict['3']), ovw=passed_command_dict.get('ovw', passed_command_dict['4']) )
                elif (self.name == 'program_download_chunk'):
                    reply = self.get_chunk_gcode_file(idx=passed_command_dict.get('idx', passed_command_dict['0']), size=passed_command_dict.get('size', passed_command_dict['1']), linuxcnc_status_poller=linuxcnc_status_poller) 
                elif (self.name == 'program_get_size'):
                    reply = self.get_gcode_file_size(linuxcnc_status_poller=linuxcnc_status_poller) 
                elif (self.name == 'program_delete'):
                    reply = self.del_gcode_file(filename=passed_command_dict.get('filename',passed_command_dict['0']).strip(), linuxcnc_status_poller=linuxcnc_status_poller)
                elif (self.name == 'save_client_config'):
                    reply = self.put_client_config( (passed_command_dict.get('key', passed_command_dict.get('0'))), (passed_command_dict.get('value', passed_command_dict.get('1'))) )
                elif (self.name == 'set_compensation'):
                    reply = self.put_compensation(passed_command_dict)
                elif (self.name == 'check_for_updates'):
                    reply = self.check_for_updates(passed_command_dict)
                elif (self.name == 'create_swap'):
                    reply = self.create_swap(passed_command_dict)
                elif (self.name == 'delete_swap'):
                    reply = self.delete_swap(passed_command_dict)
                elif (self.name == 'enable_swap'):
                    reply = self.enable_swap(passed_command_dict)
                elif (self.name == 'disable_swap'):
                    reply = self.disable_swap(passed_command_dict)
                elif (self.name == 'clear_logs'):
                    reply = self.clear_logs(passed_command_dict)
                elif (self.name == 'set_date'):
                    reply = self.set_date(passed_command_dict['0'])
                elif (self.name == 'clear_ncfiles'):
                    reply = self.clear_ncfiles(passed_command_dict)
                elif (self.name == 'set_version'):
                    reply = self.set_version( passed_command_dict.get('version', passed_command_dict['0']).strip() )
                elif (self.name == 'toggle_v1_v2revP'):
                    reply = self.toggle_v1_v2revP()
                elif (self.name == 'add_user'):
                    reply = self.add_user( passed_command_dict.get('username',passed_command_dict['0']).strip(), passed_command_dict.get('password',passed_command_dict['1']).strip() )
                elif (self.name == 'reset_clock'):
                    reply = self.reset_run_time_clock()
                elif (self.name == 'eject_usb'):
                    reply = self.eject_usb()
                else:
                    reply['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
                return reply
            else:
                return { 'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }

            return { 'code':LinuxCNCServerCommand.REPLY_COMMAND_OK }
        except:
            return { 'code':LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND }




# Custom Command Items
CommandItems = {}
CommandItem( name='halcmd',                  paramTypes=[ {'pname':'param_string', 'ptype':'string', 'optional':False} ],  help='Call halcmd. Results returned in a string.', command_type=CommandItem.HAL ).register_in_dict( CommandItems )
CommandItem( name='ini_file_name',           paramTypes=[ {'pname':'ini_file_name', 'ptype':'string', 'optional':False} ],  help='Set the INI file to use on next linuxCNC load.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='reset_clock',             paramTypes=[], help='Set the run time clock to 0 seconds', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='eject_usb',               paramTypes=[], help="Safely unmount a device that is plugged in to USB host port.", command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='interlock_release',       paramTypes=[  ], help='Stop inhibiting spindle and feed in interlock component.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )

# Pre-defined Command Items
CommandItem( name='abort',                   paramTypes=[],      help='send EMC_TASK_ABORT message' ).register_in_dict( CommandItems )
CommandItem( name='auto',                    paramTypes=[ {'pname':'auto', 'ptype':'lookup', 'lookup-vals':['AUTO_RUN','AUTO_STEP','AUTO_RESUME','AUTO_PAUSE'], 'optional':False }, {'pname':'run_from', 'ptype':'int', 'optional':True} ],      help='run, step, pause or resume a program.  auto legal values: AUTO_RUN, AUTO_STEP, AUTO_RESUME, AUTO_PAUSE' ).register_in_dict( CommandItems )
CommandItem( name='brake',                   paramTypes=[ {'pname':'onoff', 'ptype':'lookup', 'lookup-vals':['BRAKE_ENGAGE','BRAKE_RELEASE'], 'optional':False} ],      help='engage or release spindle brake.  Legal values: BRAKE_ENGAGE or BRAKE_RELEASE' ).register_in_dict( CommandItems )
CommandItem( name='debug',                   paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='set debug level bit-mask via EMC_SET_DEBUG message' ).register_in_dict( CommandItems )
CommandItem( name='feedrate',                paramTypes=[ {'pname':'rate', 'ptype':'float', 'optional':False} ],      help='set the feedrate' ).register_in_dict( CommandItems )
CommandItem( name='flood',                   paramTypes=[ {'pname':'onoff', 'ptype':'lookup', 'lookup-vals':['FLOOD_ON','FLOOD_OFF'], 'optional':False} ],      help='turn on/off flood coolant.  Legal values: FLOOD_ON, FLOOD_OFF' ).register_in_dict( CommandItems )
CommandItem( name='home',                    paramTypes=[ {'pname':'axis', 'ptype':'int', 'optional':False} ],       help='home a given axis' ).register_in_dict( CommandItems )
CommandItem( name='jog',                     paramTypes=[ {'pname':'jog', 'ptype':'lookup', 'lookup-vals':['JOG_STOP','JOG_CONTINUOUS','JOG_INCREMENT'], 'optional':False}, { 'pname':'axis', 'ptype':'int', 'optional':False }, { 'pname':'velocity', 'ptype':'float', 'optional':True }, {'pname':'distance', 'ptype':'float', 'optional':True } ],      help='jog(command, axis[, velocity[, distance]]).  Legal values: JOG_STOP, JOG_CONTINUOUS, JOG_INCREMENT' ).register_in_dict( CommandItems )
CommandItem( name='load_tool_table',         paramTypes=[],      help='reload the tool table' ).register_in_dict( CommandItems )
CommandItem( name='maxvel',                  paramTypes=[ {'pname':'rate', 'ptype':'float', 'optional':False} ],      help='set maximum velocity' ).register_in_dict( CommandItems )
CommandItem( name='mdi',                     paramTypes=[ {'pname':'mdi', 'ptype':'string', 'optional':False} ],      help='send an MDI command. Maximum 255 chars' ).register_in_dict( CommandItems )
CommandItem( name='mist',                    paramTypes=[ {'pname':'onoff', 'ptype':'lookup', 'lookup-vals':['MIST_ON','MIST_OFF'], 'optional':False} ],       help='turn on/off mist.  Legal values: MIST_ON, MIST_OFF' ).register_in_dict( CommandItems )
CommandItem( name='mode',                    paramTypes=[ {'pname':'mode', 'ptype':'lookup', 'lookup-vals':['MODE_AUTO','MODE_MANUAL','MODE_MDI'], 'optional':False} ],      help='Set mode. Legal values: MODE_AUTO, MODE_MANUAL, MODE_MDI).' ).register_in_dict( CommandItems )
CommandItem( name='override_limits',         paramTypes=[],      help='set the override axis limits flag.' ).register_in_dict( CommandItems )
CommandItem( name='program_open',            paramTypes=[ {'pname':'filename', 'ptype':'string', 'optional':False}],      help='Open an NGC file.' ).register_in_dict( CommandItems )
CommandItem( name='program_upload',          paramTypes=[ {'pname':'filename', 'ptype':'string', 'optional':False}, {'pname':'data', 'ptype':'string', 'optional':False} ], command_type=CommandItem.SYSTEM, help='Create and open an NGC file.' ).register_in_dict( CommandItems )
CommandItem( name='program_upload_chunk',    paramTypes=[ {'pname':'filename', 'ptype':'string', 'optional':False}, {'pname':'data', 'ptype':'string', 'optional':False}, {'pname':'start', 'ptype':'bool', 'optional':False}, {'pname':'end', 'ptype':'bool', 'optional':False}, {'pname':'ovw', 'ptype':'bool', 'optional':False} ], command_type=CommandItem.SYSTEM, help='Create and open an NGC file.' ).register_in_dict( CommandItems )
CommandItem( name='program_download_chunk',  paramTypes=[ {'pname':'idx', 'ptype':'int', 'optional':False}, {'pname':'size', 'ptype':'int', 'optional':False} ], command_type=CommandItem.SYSTEM, help='Send a chunk of the open NGC file back to the front end.' ).register_in_dict( CommandItems )
CommandItem( name='program_get_size',        paramTypes=[], command_type=CommandItem.SYSTEM, help='Send the size of the open NGC file back to the front end.' ).register_in_dict( CommandItems )
CommandItem( name='program_delete',          paramTypes=[ {'pname':'filename', 'ptype':'string', 'optional':False} ], command_type=CommandItem.SYSTEM, help='Delete a file from the programs directory.' ).register_in_dict( CommandItems )
CommandItem( name='reset_interpreter',       paramTypes=[],      help='reset the RS274NGC interpreter' ).register_in_dict( CommandItems )
CommandItem( name='set_adaptive_feed',       paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='set adaptive feed flag ' ).register_in_dict( CommandItems )
CommandItem( name='set_analog_output',       paramTypes=[ {'pname':'index', 'ptype':'int', 'optional':False}, {'pname':'value', 'ptype':'float', 'optional':False} ],      help='set analog output pin to value' ).register_in_dict( CommandItems )
CommandItem( name='set_block_delete',        paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='set block delete flag' ).register_in_dict( CommandItems )
CommandItem( name='set_digital_output',      paramTypes=[ {'pname':'index', 'ptype':'int', 'optional':False}, {'pname':'value', 'ptype':'int', 'optional':False} ],      help='set digital output pin to value' ).register_in_dict( CommandItems )
CommandItem( name='set_feed_hold',           paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='set feed hold on/off' ).register_in_dict( CommandItems )
CommandItem( name='set_feed_override',       paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='set feed override on/off' ).register_in_dict( CommandItems )
CommandItem( name='set_max_limit',           paramTypes=[ {'pname':'axis', 'ptype':'int', 'optional':False}, {'pname':'limit', 'ptype':'float', 'optional':False} ],      help='set max position limit for a given axis' ).register_in_dict( CommandItems )
CommandItem( name='set_max_limit',           paramTypes=[ {'pname':'axis', 'ptype':'int', 'optional':False}, {'pname':'limit', 'ptype':'float', 'optional':False} ],      help='set min position limit for a given axis' ).register_in_dict( CommandItems )
CommandItem( name='set_optional_stop',       paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='set optional stop on/off ' ).register_in_dict( CommandItems )
CommandItem( name='set_spindle_override',    paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='set spindle override flag' ).register_in_dict( CommandItems )
CommandItem( name='spindle',                 paramTypes=[ {'pname':'spindle', 'ptype':'lookup', 'lookup-vals':['SPINDLE_FORWARD','SPINDLE_REVERSE','SPINDLE_OFF','SPINDLE_INCREASE','SPINDLE_DECREASE','SPINDLE_CONSTANT'], 'optional':False} ],      help='set spindle direction.  Legal values: SPINDLE_FORWARD, SPINDLE_REVERSE, SPINDLE_OFF, SPINDLE_INCREASE, SPINDLE_DECREASE, SPINDLE_CONSTANT' ).register_in_dict( CommandItems )
CommandItem( name='spindleoverride',         paramTypes=[ {'pname':'factor', 'ptype':'float', 'optional':False} ],      help='set spindle override factor' ).register_in_dict( CommandItems )
CommandItem( name='state',                   paramTypes=[ {'pname':'state', 'ptype':'lookup', 'lookup-vals':['STATE_ESTOP','STATE_ESTOP_RESET','STATE_ON','STATE_OFF'], 'optional':False} ],      help='set the machine state.  Legal values: STATE_ESTOP_RESET, STATE_ESTOP, STATE_ON, STATE_OFF' ).register_in_dict( CommandItems )
CommandItem( name='teleop_enable',           paramTypes=[ {'pname':'onoff', 'ptype':'int', 'optional':False} ],      help='enable/disable teleop mode' ).register_in_dict( CommandItems )
CommandItem( name='teleop_vector',           paramTypes=[ {'pname':'p1', 'ptype':'float', 'optional':False}, {'pname':'p2', 'ptype':'float', 'optional':False}, {'pname':'p3', 'ptype':'float', 'optional':False}, {'pname':'p4', 'ptype':'float', 'optional':True}, {'pname':'p5', 'ptype':'float', 'optional':True}, {'pname':'p6', 'ptype':'float', 'optional':True} ],      help='set teleop destination vector' ).register_in_dict( CommandItems )
CommandItem( name='tool_offset',             paramTypes=[ {'pname':'toolnumber', 'ptype':'int', 'optional':False}, {'pname':'z_offset', 'ptype':'float', 'optional':False}, {'pname':'x_offset', 'ptype':'float', 'optional':False}, {'pname':'diameter', 'ptype':'float', 'optional':False}, {'pname':'frontangle', 'ptype':'float', 'optional':False}, {'pname':'backangle', 'ptype':'float', 'optional':False}, {'pname':'orientation', 'ptype':'float', 'optional':False} ],      help='set the tool offset' ).register_in_dict( CommandItems )
CommandItem( name='traj_mode',               paramTypes=[ {'pname':'mode', 'ptype':'lookup', 'lookup-vals':['TRAJ_MODE_FREE','TRAJ_MODE_COORD','TRAJ_MODE_TELEOP'], 'optional':False} ],      help='set trajectory mode.  Legal values: TRAJ_MODE_FREE, TRAJ_MODE_COORD, TRAJ_MODE_TELEOP' ).register_in_dict( CommandItems )
CommandItem( name='unhome',                  paramTypes=[ {'pname':'axis', 'ptype':'int', 'optional':False} ],       help='unhome a given axis' ).register_in_dict( CommandItems )
CommandItem( name='wait_complete',           paramTypes=[ {'pname':'timeout', 'ptype':'float', 'optional':True} ],       help='wait for completion of the last command sent. If timeout in seconds not specified, default is 1 second' ).register_in_dict( CommandItems )

CommandItem( name='config',                  paramTypes=[ {'pname':'data', 'ptype':'dict', 'optional':False} ],       help='Overwrite the config overlay file.  Parameter is a dictionary with the same format as returned from "get config"', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='temp_set_config_item',    paramTypes=[ {'pname':'data', 'ptype':'dict', 'optional':False} ],       help='Temporarily set a single INI config item so that the change takes effect in linuxcnc, but is not saved to the INI file.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='halfile',                 paramTypes=[ {'pname':'filename', 'ptype':'string', 'optional':False}, {'pname':'data', 'ptype':'string', 'optional':False} ],       help='Overwrite the specified file.  Parameter is a filename, then a string containing the new hal file contents.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='clear_error',             paramTypes=[  ],       help='Clear the last error condition.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='save_client_config',      paramTypes=[ {'pname':'key', 'ptype':'string', 'optional':False}, {'pname':'value', 'ptype':'string', 'optional':False} ],     help='Save a JSON object representing client configuration.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='set_compensation',      paramTypes=[ {'pname':'data', 'ptype':'dict', 'optional':False} ],     help='Save a and b axis compensation tables', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )

CommandItem( name='set_date', isasync=False, paramTypes=[], help='Set the system time', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )

CommandItem( name='clear_logs', isasync=False, paramTypes=[], help='Truncate log files found in /var/log to 0 bytes.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='clear_ncfiles', isasync=False, paramTypes=[], help='Clear files in the PROGRAM_PREFIX directory.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='check_for_updates',      isasync=True, paramTypes=[ ],     help='Use git fetch to retrieve any updates', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='create_swap', isasync=False, paramTypes=[], help='Create a swap file, allocate disk space, and add necessary entry to /etc/fstab.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='delete_swap', isasync=False, paramTypes=[], help='Delete an existing swap file and /etc/fstab entry.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='enable_swap', isasync=False, paramTypes=[], help='Enable an existing swap file.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='disable_swap', isasync=False, paramTypes=[], help='Disable an existing swap file.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='set_version',      isasync=True, paramTypes=[ { 'pname':'version', 'ptype':'string', 'optional':False} ],     help='Check out the provided version as a git tag', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='toggle_v1_v2revP',          isasync=True, paramTypes=[ ],       help='Toggle between the v1 and the v2revP. The v1 and v2revP have no way to detect the current hardware so this command allows users to toggle between them.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )

CommandItem( name='add_user',                paramTypes=[ {'pname':'username', 'ptype':'string', 'optional':False}, {'pname':'password', 'ptype':'string', 'optional':False} ], help='Add a user to the web server.  Set password to - to delete the user.  If all users are deleted, then a user named default, password=default will be created.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )

CommandItem( name='shutdown_computer',                paramTypes=[ ],       help='Shutdown the computer.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='shutdown',                paramTypes=[ ],       help='Shutdown LinuxCNC system.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='restart',          isasync=True, paramTypes=[ ],       help='Restart LinuxCNC and Rockhopper using systemctl.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )
CommandItem( name='startup',                 paramTypes=[ ],       help='Start LinuxCNC system.', command_type=CommandItem.SYSTEM ).register_in_dict( CommandItems )

# *****************************************************
# HAL Interface
#
# Puts pins on this python module for interaction with
# the HAL.


# PROBLEM:  it works if you load it
# once, but if linuxcnc goes down and restarts, this
# needs to re-set the HAL pins in the new linuxcnc instance
# *****************************************************
class HALInterface( object ):
    def __init__(self):
        self.h = None
        i = 0
        while self.h is None:
            try:
            # hal seems to want to create a component before letting us set hal pins
            # When the Rockhopper server restarts, we still need to create a component, but we've already created one before so we have to cycle until we get a unique one
            # TODO, do this a better way?
                self.h = hal.component("LinuxCNCWebSktSvr%s" % i)

            #    # create hal pins
            #    self.h.newpin("keepalive_counter", hal.HAL_U32, hal.HAL_OUT)
            #    self.h.newpin("time_since_keepalive", hal.HAL_FLOAT, hal.HAL_OUT)
            #    self.h['keepalive_counter'] = 0
            #    self.h['time_since_keepalive'] = 0
            #    self.keepalive_counter = 0
            #    self.time_of_last_keepalive = time.time()
            #    self.time_elapsed = 0

                # begin the poll-update loop of the linuxcnc system
            #    self.scheduler = tornado.ioloop.PeriodicCallback( self.poll_update, UpdateHALOutputsPollPeriodInMilliSeconds, io_loop=main_loop )
            #    self.scheduler.start()

            #    self.h.ready()
            except hal.error as e:
                print "Failed to create hal component, LinuxCNCWebSktSvr%s, already created it? " % i, e
                i += 1
        
    # def Tick( self ):
    #     if ( self.h is not None ):
    #         self.keepalive_counter = self.keepalive_counter + 1
    #         self.h['keepalive_counter'] = self.keepalive_counter
    #         previous_time = self.time_of_last_keepalive
    #         self.time_of_last_keepalive = time.time()
    #         self.time_elapsed = self.time_of_last_keepalive - previous_time
    #         self.h['time_since_keepalive'] = self.time_elapsed

    # def poll_update( self ):
    #     if ( self.h is not None ):
    #         previous_time = self.time_of_last_keepalive
    #         now_time = time.time()
    #         self.time_elapsed = now_time - previous_time
    #         self.h['time_since_keepalive'] = self.time_elapsed

    def set_p( self, name, value ):
        if self.h is not None:
            hal.set_p(name, value)

HAL_INTERFACE = HALInterface()        

# Config File Editor
INIFileDataTemplate = {
    "parameters":[],
    "sections":{}
    }


# *****************************************************
# Process a command sent from the client
# commands come in as json objects, and are converted to dict python objects
# *****************************************************
class LinuxCNCServerCommand( object ):

    # Error codes
    REPLY_NAK = '?ERR'
    REPLY_STATUS_NOT_FOUND = '?Status Item Not Found'
    REPLY_INVALID_COMMAND = '?Invalid Command'
    REPLY_INVALID_COMMAND_PARAMETER = '?Invalid Parameter'
    REPLY_ERROR_EXECUTING_COMMAND = '?Error executing command'
    REPLY_MISSING_COMMAND_PARAMETER = '?Missing Parameter'
    REPLY_LINUXCNC_NOT_RUNNING = '?LinuxCNC is not running'
    REPLY_COMMAND_OK = '?OK'
    REPLY_INVALID_USERID = '?Invalid User ID'

    def __init__( self, statusItems, commandItems, server_command_handler, status_poller, command_message='{"command": "invalid"}', command_dict=None ):
        self.linuxcnc_status_poller = status_poller
        self.command_message = command_message
        self.StatusItems = statusItems
        self.CommandItems = commandItems
        self.server_command_handler = server_command_handler
        self.async_reply_buf = []
        self.async_reply_buf_lock = threading.Lock() 
        
        if (command_dict is None):        
            try:
                self.commandDict = json.loads( command_message )
                self.command = self.commandDict['command'].strip()
            except:
                self.commandDict = {'command': 'invalid'}
                self.command = 'invalid'
        else:
            self.commandDict = command_dict
            self.command = command_dict.get('command','invalid')

    # Convert self.replyval into a JSON string suitable to return to the command originator
    def form_reply( self ):
        self.replyval['id'] = self.commandID
        if ( 'code' not in self.replyval ):
            self.replyval['code'] = LinuxCNCServerCommand.REPLY_NAK
        if ('data' not in self.replyval):
                self.replyval['data'] = self.replyval['code']
        val = json.dumps( self.replyval, cls=StatusItemEncoder )
        return val

    # update on a watched variable 
    def on_new_poll( self ):
        try:
            if (not self.statusitem.watchable):
                self.linuxcnc_status_poller.del_observer( self.on_new_poll )
                return
            if self.server_command_handler.isclosed:
                self.linuxcnc_status_poller.del_observer( self.on_new_poll )
                return
            newval = self.statusitem.get_cur_status_value(self.linuxcnc_status_poller, self.item_index, self.commandDict )
            if (self.replyval['data'] != newval['data']):
                self.replyval = newval
                self.server_command_handler.send_message( self.form_reply() )
                if ( newval['code'] != LinuxCNCServerCommand.REPLY_COMMAND_OK ):
                    self.linuxcnc_status_poller.del_observer( self.on_new_poll )
        except:
            pass

    def monitor_async(self):
        if (len(self.async_reply_buf) > 0):
            
            self.async_reply_buf_lock.acquire()

            self.replyval = self.async_reply_buf[0]         
            self.server_command_handler.send_message( self.form_reply() )
            self.async_reply_buf_lock.release()

            self.linuxcnc_status_poller.del_observer( self.monitor_async )
        
        return

    # this is the main interface to a LinuxCNCServerCommand.  This determines what the command is, and executes it.
    # Callbacks are made to the self.server_command_handler to write output to the websocket
    # The self.linuxcnc_status_poller is used to poll the linuxcnc status, which is used to watch status items and monitor for changes
    def execute( self ):
        global main_loop

        self.commandID = self.commandDict.get('id','none')
        self.replyval = {}
        self.replyval['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND
        if ( self.command == 'get'):
            try:
                self.item_index = 0
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND_PARAMETER
                self.statusItemName = self.commandDict['name'].strip()
                self.statusitem = StatusItem.from_name( self.statusItemName )
                if (self.statusitem is None):
                    self.replyval['code'] = LinuxCNCServerCommand.REPLY_STATUS_NOT_FOUND
                else:
                    if ( self.statusitem.isarray ):
                        self.item_index = self.commandDict['index']
                        self.replyval['index'] = self.item_index

                    if (self.statusitem.isasync):
                        self.linuxcnc_status_poller.add_observer( self.monitor_async )
                        
                    self.replyval = self.statusitem.get_cur_status_value(self.linuxcnc_status_poller, self.item_index, self.commandDict, async_buffer=self.async_reply_buf, async_lock=self.async_reply_buf_lock )
            except:
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_NAK

        elif (self.command == 'watch'):
            try:
                self.item_index = 0
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND_PARAMETER
                self.statusItemName = self.commandDict['name'].strip()
                self.statusitem = StatusItem.from_name( self.statusItemName )
                if (self.statusitem is None):
                    self.replyval['code'] = LinuxCNCServerCommand.REPLY_STATUS_NOT_FOUND
                else:
                    if ( self.statusitem.isarray ):
                        self.item_index = self.commandDict['index']
                        self.replyval['index'] = self.item_index
                    self.replyval = self.statusitem.get_cur_status_value(self.linuxcnc_status_poller, self.item_index, self.commandDict )
                    if (self.replyval['code'] == LinuxCNCServerCommand.REPLY_COMMAND_OK ):
                        self.linuxcnc_status_poller.add_observer( self.on_new_poll )
            except:
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_NAK
            

        elif (self.command == 'list_get'):
            try:
                self.replyval['data'] = StatusItems.values()
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_COMMAND_OK
            except:
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_NAK

        elif (self.command == 'list_put'):
            try:
                self.replyval['data'] = CommandItems.values()
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_COMMAND_OK
            except:
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_NAK

        elif (self.command == 'put'):
            self.replyval['code'] = LinuxCNCServerCommand.REPLY_NAK
            try:
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_INVALID_COMMAND_PARAMETER
                self.LinuxCNCCommandName = self.commandDict['name']
                self.commanditem = self.CommandItems.get( self.LinuxCNCCommandName )
                if self.commanditem.isasync:
                    def runOnIOLoop(server_command_handler, reply):
                        # write_message isn't thread safe, so we have to run this in the IOLoop
                        print "sending reply: %s" % reply
                        server_command_handler.write_message(reply)
                        
                    def runInThread(commanditem, commandDict, linuxcnc_status_poller, server_command_handler):
                        reply = commanditem.execute(commandDict, linuxcnc_status_poller)
                        json_reply = json.dumps(reply, cls=StatusItemEncoder)

                        main_loop.add_callback(runOnIOLoop, server_command_handler, json_reply)

                    thread = threading.Thread(target=runInThread, args=(self.commanditem, self.commandDict, self.linuxcnc_status_poller, self.server_command_handler ))
                    thread.start()
                    self.replyval = { 'code': LinuxCNCServerCommand.REPLY_COMMAND_OK }
                else:
                    self.replyval = self.commanditem.execute( self.commandDict, self.linuxcnc_status_poller )
            except:
                logging.debug( 'PUT Command: ERROR'  )
                
 
        elif (self.command == 'keepalive'):
            global HAL_INTERFACE
            try:
                HAL_INTERFACE.Tick()
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_COMMAND_OK
                self.replyval['counter'] = HAL_INTERFACE.keepalive_counter
                self.replyval['elapsed_time'] = HAL_INTERFACE.time_elapsed
            except:
                self.replyval['code'] = LinuxCNCServerCommand.REPLY_ERROR_EXECUTING_COMMAND
            
        # convert to JSON, and return the reply string
        return self.form_reply()





# *****************************************************
# *****************************************************
class LinuxCNCCommandWebSocketHandler(tornado.websocket.WebSocketHandler):

    def __init__(self, *args, **kwargs):
        global LINUXCNCSTATUS
        super( LinuxCNCCommandWebSocketHandler, self ).__init__( *args, **kwargs )
        self.user_validated = False
        print "New websocket Connection..."

    def check_origin(self, origin):

        # allow any connection from our own web interfaces
        for ifaceName in interfaces():
            addresses = ["http://%s" % (i['addr']) for i in ifaddresses(ifaceName).setdefault(AF_INET, [{'addr':'No IP addr'}] )]
            addresses8000 = ["http://%s:8000" % (i['addr']) for i in ifaddresses(ifaceName).setdefault(AF_INET, [{'addr':'No IP addr'}] )]
            if origin in addresses or origin in addresses8000:
                return True
        
        return True if originRE.match(origin) else False
    
    def open(self,arg):
        global LINUXCNCSTATUS
        self.isclosed = False
        self.stream.socket.setsockopt( socket.IPPROTO_TCP, socket.TCP_NODELAY, 1 )

    def allow_draft76(self):
        return False    

    def on_message(self, message): 
        global LINUXCNCSTATUS
        if int(options.verbose) > 2:
            if (message.find("\"HB\"") < 0):
                print "GOT: " + message
        if (self.user_validated):
            try:
                reply = LinuxCNCServerCommand( StatusItems, CommandItems, self, LINUXCNCSTATUS, command_message=message ).execute()
                self.write_message(reply)
                if int(options.verbose) > 3:
                    if (reply.find("\"HB\"") < 0) and (reply.find("backplot") < 0):
                        print "Reply: " + reply
            except Exception as ex:
                print "1:", ex
        else:
            try: 
                global userdict
                commandDict = json.loads( message )
                id = commandDict.get('id','Login').strip()
                user = commandDict['user'].strip()
                pw = hashlib.md5(commandDict['password'].strip()).hexdigest()
                dateString = commandDict.get('date', None)
                
                # Beaglebone Black can't keep time, so it uses NTP to set the time.
                # If there's no internet connection, or the NTP servers are down,
                # the date will be wrong. The UI sends the connected computers
                # current time on login, so we can use that to set a better-than-default
                # time.

                if dateString:
                  uiDateTime = datetime.datetime.strptime(dateString, "%Y-%m-%dT%H:%M:%S.%fZ")
                  serverDateTime = datetime.datetime.utcnow()

                  if (uiDateTime-serverDateTime).days >= 1:
                    print "UI time greater than a day ahead of server time. Setting server time to %s" % dateString
                    set_date_string(dateString)

                if ( ( user in userdict ) and ( userdict.get(user) == pw ) ):
                    self.user_validated = True
                    self.write_message(json.dumps( { 'id':id, 'code':'?OK', 'data':'?OK'}, cls=StatusItemEncoder ))
                    if int(options.verbose) > 2:
                        print "Logged in " + user
                else:
                    self.write_message(json.dumps( { 'id':id, 'code':'?User not logged in', 'data':'?User not logged in'}, cls=StatusItemEncoder ))
                    if int(options.verbose) > 2:
                        print "Logged FAILED " + user
            except:
                if int(options.verbose) > 2:
                    print "Logged FAILED (user unknown)"
                self.write_message(json.dumps( { 'id':id, 'code':'?User not logged in', 'data':'?User not logged in'}, cls=StatusItemEncoder ))

            
 
    def send_message( self, message_to_send ):
        self.write_message( message_to_send )
        if int(options.verbose) > 4:
            if (message_to_send.find("actual_position") < 0) and (message_to_send.find("\"HB\"") < 0) and (message_to_send.find("backplot") < 0) :
                print "SEND: " + message_to_send

    def on_close(self):
        self.isclosed = True
        logging.debug( "WebSocket closed" )

    def select_subprotocol(self, subprotocols):
        if ('linuxcnc' in subprotocols ):
            return 'linuxcnc'
        elif (subprotocols == ['']): # some websocket clients don't support subprotocols, so allow this if they just provide an empty string
            return '' 
        else:
            logging.warning('WEBSOCKET CLOSED: sub protocol linuxcnc not supported')
            logging.warning( 'Subprotocols: ' + subprotocols.__str__() )
            self.close()
            return None


def check_user( user, pw ):
    # check if the user/pw combo is in our dictionary
    user = user.strip()
    pw = hashlib.md5(pw.strip()).hexdigest()
    global userdict
    if ( ( user in userdict ) and ( userdict.get(user) == pw ) ):
        return True
    else:
        return False

# *****************************************************
# *****************************************************
# A decorator that lets you require HTTP basic authentication from visitors.
#
# Kevin Kelley <kelleyk@kelleyk.net> 2011
# Use however makes you happy, but if it breaks, you get to keep both pieces.
# Post with explanation, commentary, etc.:
# http://kelleyk.com/post/7362319243/easy-basic-http-authentication-with-tornado
# Usage example:
#@require_basic_auth
#class MainHandler(tornado.web.RequestHandler):
# def get(self, basicauth_user, basicauth_pass):
# self.write('Hi there, {0}! Your password is {1}.' \
# .format(basicauth_user, basicauth_pass))
# def post(self, **kwargs):
# basicauth_user = kwargs['basicauth_user']
# basicauth_pass = kwargs['basicauth_pass']
# self.write('Hi there, {0}! Your password is {1}.' \
# .format(basicauth_user, basicauth_pass))
# *****************************************************
# *****************************************************
def require_basic_auth(handler_class):
    def wrap_execute(handler_execute):
        def require_basic_auth(handler, kwargs):
            auth_header = handler.request.headers.get('Authorization')
            if auth_header is None or not auth_header.startswith('Basic '):
                handler.set_status(401)
                handler.set_header('WWW-Authenticate', 'Basic realm=Restricted')
                handler._transforms = []
                handler.finish()
                print "Authorization Challenge - login failed."
                return False
            auth_decoded = base64.decodestring(auth_header[6:])
            user, pw = auth_decoded.split(':', 2)

            # check if the user/pw combo is in our dictionary
            return check_user( user, pw )
        
        def _execute(self, transforms, *args, **kwargs):
            if not require_basic_auth(self, kwargs):
                return False
            return handler_execute(self, transforms, *args, **kwargs)
        return _execute

    handler_class._execute = wrap_execute(handler_class._execute)
    return handler_class



# *****************************************************
@require_basic_auth
class PollHandler(tornado.web.RequestHandler):
    def get(self, arg):

        # if this request is sending a callback, then assume jsonp for return type
        jsonp = self.get_argument("callback", None)
        if (jsonp is None):
            jsonp = self.get_argument("jsonp", None)
        
        args = arg.split("/")
        args = [tornado.escape.url_unescape(x) for x in args]
        command_dict = {'command':args[0]}
        for idx in range(1,len(args),2):
            try:
                val = args[idx+1]
                # try and convert anything that is a number to an actual number (not a string)
                # use int formatting if possible, otherwise use float
                v1 = float(val)
                v2 = int(val)
                if (v1 == v2):
                    val = v2
                else:
                    val = v1
            except:
                pass
            command_dict[args[idx]] = val

        self.set_header("Access-Control-Allow-Origin","*")
        if (jsonp is not None):
            self.set_header("Content-Type", "application/javascript")
            self.write( jsonp + '(' +  LinuxCNCServerCommand( StatusItems, CommandItems, self, LINUXCNCSTATUS, command_dict=command_dict ).execute() + ')' )
        else:
            self.set_header("Content-Type", "application/json")
            self.write(LinuxCNCServerCommand( StatusItems, CommandItems, self, LINUXCNCSTATUS, command_dict=command_dict ).execute())
        self.finish()

# *****************************************************  
@require_basic_auth
class CalibrationUpload(tornado.web.RequestHandler):
  def get(self):
    print "in get"
    self.render( 'LinuxCNCSandbox.html' )

  def post(self):
    
    # An 'enable swap file' checkbox has been added to the Calibration Upload form.
    # If it is checked when uploading, we will ensure that a swap file has been enabled and created
    # This was done primarily to remove the need to do this manually through the UI during calibration
    try:
      self.get_argument('enableSwap')
      createSwapCommandDict = {'0': '256', 'command': 'put', 'id': 'create_swap', 'name': 'create_swap'}
      CommandItems['create_swap'].execute( createSwapCommandDict, LINUXCNCSTATUS)
      enableSwapCommandDict = {'command': 'put', 'id': 'enable_swap', 'name': 'enable_swap'}
      CommandItems['enable_swap'].execute(enableSwapCommandDict, LINUXCNCSTATUS)
    except:
      pass

    try:
      fileinfo = self.request.files['calibration_data'][0]
      tmp = tempfile.NamedTemporaryFile(delete=False)
      tmp.file.write(fileinfo['body'])
      tmp.file.close()

      tmpDir = tempfile.mkdtemp()
      try:
        zip_ref = zipfile.ZipFile(tmp.name, 'r')
        zip_ref.extractall(tmpDir)
        zip_ref.close()

        calFilesUploaded = {}
        for calFile in ['CalibrationOverlay.inc', 'a.comp', 'b.comp', 'x.comp', 'y.comp', 'z.comp']:
          calFilesUploaded[calFile] = False

        for path, dirs, files in os.walk(tmpDir):
          for fileName, isUploaded in calFilesUploaded.iteritems():
            if ( not isUploaded ) and ( fileName in files ):
              calFilePath = os.path.join(path, fileName)
              shutil.copy( calFilePath, SETTINGS_PATH )
              calFilesUploaded[fileName] = True

        if calFilesUploaded['a.comp'] and calFilesUploaded['b.comp'] and calFilesUploaded['CalibrationOverlay.inc']:
          responseText = 'Success!'
        else:
          responseText = 'Warning! Files not found: '
          notFoundText = ""
          if not calFilesUploaded['CalibrationOverlay.inc']:
            notFoundText += 'CalibrationOverlay.inc'
          if not calFilesUploaded['a.comp']:
            notFoundText += 'a.comp' if len(notFoundText) == 0 else ', a.comp'
          if not calFilesUploaded['b.comp']:
            notFoundText += 'b.comp' if len(notFoundText) == 0 else ', b.comp'
          responseText += notFoundText
          responseText += '.'

        responseTextUploadedFiles = ''

        for fileName, isUploaded in calFilesUploaded.iteritems():
          if isUploaded:
            if responseTextUploadedFiles == '':
              responseTextUploadedFiles += ' Uploaded files: '
              responseTextUploadedFiles += fileName
            else:
              responseTextUploadedFiles += ', '
              responseTextUploadedFiles += fileName

        responseText += responseTextUploadedFiles
        self.write(responseText)
      except Exception as ex:
        self.write("ERROR: " + str(ex))
      finally:
        if os.path.isfile(tmp.name):
          os.remove(tmp.name)
        if os.path.isdir(tmpDir):
          shutil.rmtree(tmpDir)

    except Exception as ex:
      self.write("ERROR: " + str(ex))
      


# *****************************************************  
@require_basic_auth
class PollHandlerJSON(tornado.web.RequestHandler):
    def get(self, arg):
        
        arg = tornado.escape.url_unescape(arg)
        jsonp = self.get_argument("callback", None)
        if (jsonp is None):
            jsonp = self.get_argument("jsonp", None)

        self.set_header("Access-Control-Allow-Origin","*")            
        if (jsonp is not None):
            self.set_header("Content-Type", "application/javascript")
            self.write( jsonp + '(' + LinuxCNCServerCommand( StatusItems, CommandItems, self, LINUXCNCSTATUS, command_message=arg ).execute() + ')' )
        else:
            self.set_header("Content-Type", "application/json")
            self.write(LinuxCNCServerCommand( StatusItems, CommandItems, self, LINUXCNCSTATUS, command_message=arg ).execute())
        self.finish()
  
# *****************************************************
class PollHeaderLogin(tornado.web.RequestHandler):
    def get(self, arg):
        self.write( json.dumps({'code':'?OK'}) )
        self.finish()
        return

        login = False
        if "user" in self.request.headers:
            if "pw" in self.request.headers:
                if check_user( self.request.headers["user"], self.request.headers["pw"] ):
                    login = True
        if not login:
            print "Login Failed in query."
            self.set_header("Content-Type", "application/json")
            self.write( json.dumps({'code':'?Invalid User ID'}) )
            self.finish()
            return

        command_dict = {}
        for k in self.request.arguments:
            try:
                val = self.get_argument(k)
                # try and convert anything that is a number to an actual number (not a string)
                # use int formatting if possible, otherwise use float
                v1 = float(val)
                v2 = int(val)
                if (v1 == v2):
                    val = v2
                else:
                    val = v1
            except:
                pass
            command_dict[k] = val

        jsonp = self.get_argument("callback", None)
        if (jsonp is None):
            jsonp = self.get_argument("jsonp", None)

        self.set_header("Access-Control-Allow-Origin","*")    
        if (jsonp is not None):
            self.set_header("Content-Type", "application/javascript")
            self.write( jsonp + '(' + LinuxCNCServerCommand( StatusItems, CommandItems, self, LINUXCNCSTATUS, command_dict=command_dict ).execute() + ')' )
        else:
            self.set_header("Content-Type", "application/json")
            self.write(LinuxCNCServerCommand( StatusItems, CommandItems, self, LINUXCNCSTATUS, command_dict=command_dict ).execute())
            
        self.finish()

def readUserList():
    global userdict
    global application_path

    logging.info("Reading user list...")
    userdict = {}
    try:
        parser = SafeConfigParser() 
        parser.read(os.path.join(application_path,'users.ini'))
        for name, value in parser.items('users'):
            userdict[name] = value
    except Exception as ex:
        print "Error reading users.ini:", ex

# *****************************************************
# *****************************************************
class MainHandler(tornado.web.RequestHandler):
    def get(self, arg):
        if (arg.upper() in [ '', 'INDEX.HTML', 'INDEX.HTM', 'INDEX']):
            self.render( 'LinuxCNCConfig.html' )
        else:
            self.render( arg ) 

# ********************************
# ********************************
#  Initialize global variables
# ********************************
# ********************************

# determine current path to executable
# determine if application is a script file or frozen exe
global application_path
if getattr(sys, 'frozen', False):
    application_path = os.path.dirname(sys.executable)
elif __file__:
    application_path = os.path.dirname(__file__)

# The main application object:
# the /command/ and /polljason/ use HTTP Basic Authorization to log in.
# the /pollhl/ use HTTP header arguments to log in
application = tornado.web.Application([
    (r"/([^\\/]*)", MainHandler, {} ),
    (r"/command/(.*)", PollHandler, {} ),  
    (r"/polljson/(.*)", PollHandlerJSON, {} ),
    (r"/query/(.*)", PollHeaderLogin, {} ),
    (r"/websocket/(.*)", LinuxCNCCommandWebSocketHandler, {} ),
    (r"/upload/calibration", CalibrationUpload, {})
    ],
    debug=True,
    template_path=os.path.join(application_path, "templates"),
    static_path=os.path.join(application_path, "static"),
    )

# ********************************
# ********************************
# main()
# ********************************
# ******************************** 
def main():
    global POCKETNC_DIRECTORY
    global INI_FILENAME
    global INI_FILE_PATH
    global userdict
    global instance_number
    global LINUXCNCSTATUS
    global options
    global userdict

    def fn():
        instance_number = random()
        print "Webserver reloading..."

    parser = OptionParser()
    parser.add_option("-v", "--verbose", dest="verbose", default=0,
                      help="Verbosity level.  Default to 0 for quiet.  Set to 5 for max.")

    (options, args) = parser.parse_args()

    if ( int(options.verbose) > 4):
        print "Options: ", options
        print "Arguments: ", args[0]

    if len(args) < 1:
        INI_FILENAME = "%s/Settings/PocketNC.ini" % POCKETNC_DIRECTORY
    else:
        INI_FILENAME = args[0]
    [INI_FILE_PATH, x] = os.path.split( INI_FILENAME )

    if ( int(options.verbose) > 4):
        print "INI File: ", INI_FILENAME

    if ( int(options.verbose) > 4):
        print "Parsing INI File Name"

    instance_number = random()
    LINUXCNCSTATUS = LinuxCNCStatusPoller(main_loop, UpdateStatusPollPeriodInMilliSeconds)

    log_exists = os.path.isfile("/var/log/linuxcnc_webserver.log")
    if not log_exists:
        subprocess.call(['sudo', 'touch', "/var/log/linuxcnc_webserver.log"])
        subprocess.call(['sudo', 'chmod', '666', "/var/log/linuxcnc_webserver.log"])
    logging.basicConfig(filename=os.path.join("/var/log/linuxcnc_webserver.log"),format='%(asctime)sZ pid:%(process)s module:%(module)s %(message)s', level=logging.ERROR)
 
    #rpdb2.start_embedded_debugger("password")

    readUserList()

    logging.info("Starting linuxcnc http server...")
    print "Starting Rockhopper linuxcnc http server."

    # see http://www.akadia.com/services/ssh_test_certificate.html to learn how to generate a new server SSL certificate
    # for httpS protocol:
    #application.listen(8000, ssl_options=dict(
    #    certfile="server.crt",
    #    keyfile="server.key",
    #    ca_certs="/etc/ssl/certs/ca-certificates.crt",
    #    cert_reqs=ssl.CERT_NONE) )

    # for non-httpS (plain old http):
    application.listen(8000)

    # cause tornado to restart if we edit this file.  Usefull for debugging
    tornado.autoreload.add_reload_hook(fn)
    tornado.autoreload.start()

    # start up the webserver loop
    main_loop.start() 

# auto start if executed from the command line
if __name__ == "__main__":

    main()


