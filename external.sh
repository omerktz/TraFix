#!/bin/bash
THEANO_FLAGS=device=cpu python external.py validate . model.ll-c 10 history
#python external.py validate . model.ll-c 10 history
