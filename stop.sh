#!/bin/bash

pgrep -f LinuxCNCWebSktSvr | while read -r pid ; do
  echo "killing $pid"
  kill -9 $pid
done
