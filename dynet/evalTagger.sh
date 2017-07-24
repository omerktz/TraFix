#!/bin/bash
set -x
python $1 validate
python $1 test
python $1 train
python trainTagger.py -d train -f validate -v
python tagger.py -d validate
python tagger.py -d test
python tagger.py -d train
diff validate.tags validate.out >> validate.diff
diff test.tags test.out >> test.diff
diff train.tags train.out >> train.diff