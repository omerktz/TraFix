#!/bin/bash
THEANO_FLAGS=device=cpu python externalN.py validate1 . model1.ll-c 10 history1 5
#python external.py validate . model.ll-c 10 history
