#!/bin/bash
THEANO_FLAGS=device=cpu python external.py validate . model.ll-c.npz 10 validationHistory