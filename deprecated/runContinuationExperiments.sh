#!/bin/bash
mkdir $2
for ((i=0;i<$1;i++))
do
    runContinuationExperiment.sh $2/output$i $2/log$i $3/output$i/models/model0.dynmt_bestmodel.txt &
done
sleep 5
wait
