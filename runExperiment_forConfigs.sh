#!/bin/bash
(python active_learner.py input $1 $3 -v -e -s 5) &> $2
tar -czf $1.tar.gz $1/ $2
