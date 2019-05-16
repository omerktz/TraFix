#!/bin/bash
python aws.py $1 $2 $3 -v ${@:4}
python analysis.py $2 $2/analysis.csv