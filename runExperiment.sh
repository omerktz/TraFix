#!/bin/bash
mkdir $1 &> /dev/null
(python active_learner.py input $1 -v -e) &> $1/activelearner.log
tar -czf $1.tar.gz $1/
