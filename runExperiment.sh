#!/bin/bash
echo "(python active_learner.py input $1 $3 ${@:4} -v -e) &> $2"
#tar -czf $1.tar.gz $1/ $2
