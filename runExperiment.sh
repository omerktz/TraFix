#!/bin/bash
(python active_learner_openNmt.py input $1 $3 -v -e) &> $2
tar -czf $1.tar.gz $1/ $2
