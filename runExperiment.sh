#!/bin/bash
(python active_learner.py input $1 -v -e) &> $2
tar -czf $1.tar.gz $1/ $2
