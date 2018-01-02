#!/bin/bash
mkdir $3 &> /dev/null
(python codenator.py -n $1 -c configs/codenator4active.config -o $2 -po) &> $3/activelearner.log
(python active_learner.py $2 $3 -v) &> $3/activelearner.log
rm $2.* &> /dev/null
tar -czf $3.tar.gz $3/
