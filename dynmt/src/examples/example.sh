#!/usr/bin/env bash
#install_name_tool -change libboost_program_options.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_program_options.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
#install_name_tool -change libboost_serialization.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_serialization.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
#base_path=/home/nlp/aharonr6
base_path=/Users/roeeaharoni

export LC_ALL=en_US.UTF-8
export LANG=en_US.UTF-8

python $base_path/git/dynet-seq2seq-attn/src/dynmt.py --dynet-mem 2000 --input-dim=50 --hidden-dim=100 --epochs=100 --lstm-layers=1 \
--optimization=ADADELTA --batch-size=1 --beam-size=1 --plot \
$base_path/git/dynet-seq2seq-attn/data/input.txt \
$base_path/git/dynet-seq2seq-attn/data/output.txt \
$base_path/git/dynet-seq2seq-attn/data/input.txt \
$base_path/git/dynet-seq2seq-attn/data/output.txt \
$base_path/git/dynet-seq2seq-attn/data/input.txt \
$base_path/git/dynet-seq2seq-attn/data/output.txt \
$base_path/git/dynet-seq2seq-attn/results/test_numchar_new

