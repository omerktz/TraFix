#!/bin/bash
python codenator.py -n 100000 -o train -ll
python codenator.py -n 10000 -o test -ll
python codenator.py -n 1000 -o validate -ll
