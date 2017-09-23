#!/bin/bash
THEANO_FLAGS=device=cpu python externalN.py validate . model.ll-c 10 history 5 -ll -r 5 -po
#python external.py validate . model.ll-c 10 history
