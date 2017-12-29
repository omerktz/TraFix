#!/bin/bash
python codenator.py -n $1 -c configs/codenator4active.config -o $2 -po &> /dev/null
mkdir $3
python active_learner.py $2 $3 -v &> $3/activelearner.log
rm $2.*
tar -czf $3.tar.gz $3/

