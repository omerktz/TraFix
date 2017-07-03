#!/bin/bash
python codenator.py -n 100000 -o train
python codenator.py -n 10000 -o test
python codenator.py -n 1000 -o validate
