#!/bin/bash
echo source activate tensorflow_p27
echo python api_tfnmt.py realcode realcode realcode output$1/datasets/vocabs$2 -m output$1/models/model$2 -c configs/nmt.config --translate -n 5
echo python evaluate.py input 5 x86Util.py -v 