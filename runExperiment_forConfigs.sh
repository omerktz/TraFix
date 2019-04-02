#!/bin/bash
(python active_learner.py input $1 $3 -v -e -s 1) &> $2
tar -czf $1.tar.gz $1/ $2
