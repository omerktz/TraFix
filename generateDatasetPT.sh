#!/bin/bash
python codenator.py -n 100000 -o train -pt $@
python codenator.py -n 10000 -o test -pt $@
python codenator.py -n 1000 -o validate -pt $@
