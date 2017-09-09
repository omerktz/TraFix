#!/bin/bash
THEANO_FLAGS=device=cpu python externalN.py validate . model.pt-c 10 history 5 -pt -r 5
#python external.py validate . model.ll-c 10 history
