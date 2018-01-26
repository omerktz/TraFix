#!/bin/bash
mkdir $2
for ((i=0;i<$1;i++))
do
    ./runExperiment.sh $2/output$i &
done
sleep 5
wait
