#!/bin/bash
(python active_learner.py input $1 -v -e -m $3) &> $2
tar -czf $1.tar.gz $1/ $2
