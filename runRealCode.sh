#!/bin/bash
source activate tensorflow_p27
python api_tfnmt.py realcode realcode realcode output$1/datasets/vocabs$2 -m output$1/models/model$2 -c configs/nmt.config --translate -n 5
python evaluate.py realcode 5 x86Util.py -v 