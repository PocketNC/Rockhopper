from LinuxCNCWebSktSvr import StatusItems, CommandItems
import json

statusItems = []
for name in StatusItems:
  statusItem = StatusItems[name]
  
  statusItems.append(statusItem)

statusItems.sort(key=lambda item: item.name)

commandItems = []
for name in CommandItems:
  commandItem = CommandItems[name]
  commandItems.append(commandItem)

commandItems.sort(key=lambda item: item.name)

print(
"""
//****************************************************************************************
//
// AUTOGENERATED by generateRockhopperClientAPI.py in Rockhopper repository, DO NOT EDIT.
// If changes were made to the StatusItems or CommandItems data structures, run 
// generateRockhopperClientAPI.py again and replace this file with its output.
//
//*****************************************************************************************
""")

print("export const StatusItems = [")
numStatusItems = len(statusItems)
for (i,statusItem) in enumerate(statusItems):
  isLast = i == numStatusItems-1
  print('  { name: "%s", watchable: %s%s }%s' % (statusItem.name, 
                                                   "true" if statusItem.watchable else "false", 
                                                   (', requiresFeature: "%s"' % (statusItem.requiresFeature,) if statusItem.requiresFeature else ""),
                                                   "" if isLast else ","))
print("];")
print("")

print("export const CommandItems = [")
numCommandItems = len(commandItems)
for (i,item) in enumerate(commandItems):
  isLast = i == numCommandItems-1
  print('  { name: "%s", paramTypes: %s }%s' % (item.name, json.dumps(item.paramTypes), "" if isLast else ","))
print("];")
