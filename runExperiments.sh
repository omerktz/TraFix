#!/bin/bash
for ((i=0;i<$1;i++))
do
    ./runExperiment.sh 1000 dataset$i output$i &
done
sleep 5
wait