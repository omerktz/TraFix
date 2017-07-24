#!/bin/bash
set -x
python $1 validate
python $1 test
python $1 train
python trainClassifier.py -d train -f validate -v
python classifierr.py -d validate
python classifierr.py -d test
python classifierr.py -d train
diff validate.tags validate.out >> validate.diff
diff test.tags test.out >> test.diff
diff train.tags train.out >> train.diff