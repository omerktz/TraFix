#!/bin/bash
set -x

cd dynmt/src
(time python dynmt.py --dynet-autobatch 0 ~/train.corpus.ll ~/train.corpus.po ~/validate.corpus.ll ~/validate.corpus.po ~/test.corpus.ll ~/test.corpus.po ~/results.ll-po.dynmt --plot --epochs=5000 --batch-size=32 --eval-after=500 --max-len=500 --max-pred=500 --max-patience=10 --beam-size=1) &> ~/dynmtPO.out
#(time python dynmt.py --dynet-autobatch 0 ~/train.corpus.ll ~/train.corpus.c ~/validate.corpus.ll ~/validate.corpus.c ~/test.corpus.ll ~/test.corpus.c ~/results.ll-c.dynmt --plot --epochs=5000 --batch-size=32 --eval-after=500 --max-len=500 --max-pred=500 --max-patience=10 --beam-size=1) &> ~/dynmtC.out
cd-

