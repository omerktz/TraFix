# dynmt-py

Neural machine translation implementation using [dynet](https://github.com/clab/dynet)'s python bindings.

Example Usage:
~~~~
python dynmt.py --dynet-autobatch 0 --dynet-gpu-ids 1 --dynet-mem 12000 \
--input-dim=500 --hidden-dim=1024 --epochs=100 --lstm-layers=1 --optimization=ADADELTA \
--batch-size=60 --beam-size=5 --vocab 30000 --plot --eval-after=10000  \
train_source.txt train_target.txt dev_source.txt dev_target.txt test_source.txt test_target.txt path/to/model/dir
~~~~

Options:

Name|Description
--- | ---
  -h --help        |             shows a help message and exits
  --dynet-mem MEM      |         allocates MEM bytes for dynet
  --dynet-gpu-ids IDS  |         GPU ids to use
  --dynet-autobatch AUTO   |     switch auto-batching on
  --input-dim=INPUT      |       input embeddings dimension [default: 300]
  --hidden-dim=HIDDEN     |      LSTM hidden layer dimension [default: 100]
  --epochs=EPOCHS         |      amount of training epochs [default: 1]
  --layers=LAYERS         |      amount of layers in LSTM [default: 1]
  --optimization=OPTIMIZATION  | chosen optimization method (ADAM/SGD/ADAGRAD/MOMENTUM/ADADELTA) [default: ADADELTA]
  --reg=REGULARIZATION       |   regularization parameter for optimization [default: 0]
  --learning=LEARNING         |  learning rate parameter for optimization [default: 0.0001]
  --batch-size=BATCH           | batch size [default: 1]
  --beam-size=BEAM             | beam size in beam search [default: 5]
  --vocab-size=VOCAB          |  max vocabulary size [default: 99999]
  --eval-after=EVALAFTER      |  amount of train batches to wait before evaluation [default: 1000]
  --max-len=MAXLEN            |  max train sequence length [default: 50]
  --max-pred=MAXPRED          |  max predicted sequence length [default: 50]
  --grad-clip=GRADCLIP        |  gradient clipping threshold [default: 5.0]
  --max-patience=MAXPATIENCE  |  amount of checkpoints without improvement on dev before early stopping [default: 100]
  --plot                      |  plot a learning curve while training each model
  --override                  |  override existing model with the same name, if exists
  --ensemble=ENSEMBLE         |  ensemble model paths separated by a comma
  --last-state                |  only use last encoder state
  --eval                      |  skip training, do only evaluation
  
Arguments (must be given in this order):

Name|Description
--- | ---
  TRAIN_INPUTS_PATH |   train inputs path
  TRAIN_OUTPUTS_PATH |  train outputs path
  DEV_INPUTS_PATH    |  development inputs path
  DEV_OUTPUTS_PATH    | development outputs path
  TEST_INPUTS_PATH     |test inputs path
  TEST_OUTPUTS_PATH    |test outputs path
  RESULTS_PATH | results file path
