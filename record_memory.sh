#!/bin/bash
while true; do (free | grep -E "Mem: +[0-9]+ +[0-9]+ +[0-9]+" -o) >> memory.log; sleep 60; done