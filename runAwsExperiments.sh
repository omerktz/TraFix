#!/bin/bash
python aws.py $1 $2 $3 -v
python analysis.py $2 $2/analysis.csv