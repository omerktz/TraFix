#!/bin/bash
python train.py train validate . model.ll-c.npz ./external.sh
THEANO_FLAGS=device=cpu python translate.py test . model.ll-c.npz
python evaluate.py test