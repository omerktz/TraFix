#!/usr/bin/env bash
#install_name_tool -change libboost_program_options.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_program_options.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
#install_name_tool -change libboost_serialization.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_serialization.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
base_path=/home/nlp/aharonr6
#base_path=/Users/roeeaharoni

export LC_ALL=en_US.UTF-8
export LANG=en_US.UTF-8
python $base_path/git/dynet-seq2seq-attn/src/dynmt.py --dynet-gpu-ids 2 --dynet-mem 12000 --input-dim=500 --hidden-dim=1024 --epochs=100 --lstm-layers=1 \
--optimization=ADADELTA --batch-size=60 --beam-size=12 --plot --eval-after=10000 --vocab 90000 \
$base_path/git/research/string-to-tree-nmt/data/WMT16/de-en-raw/train/wmt16.train.tok.clean.true.bpe.de \
$base_path/git/research/string-to-tree-nmt/data/WMT16/de-en-raw/train/wmt16.train.tok.clean.true.bpe.en \
$base_path/git/research/string-to-tree-nmt/data/WMT16/de-en-raw/dev/newstest-2013-2014-deen.tok.clean.true.bpe.de \
$base_path/git/research/string-to-tree-nmt/data/WMT16/de-en-raw/dev/newstest-2013-2014-deen.tok.clean.true.bpe.en \
$base_path/git/research/string-to-tree-nmt/data/news-de-en/test/newstest2016-deen.tok.penntrg.clean.true.bpe.de \
$base_path/git/research/string-to-tree-nmt/data/news-de-en/test/newstest2016-deen.tok.penntrg.clean.true.bpe.en \
$base_path/git/dynet-seq2seq-attn/results/test_de_en_wmt16

# small train files
#$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.de \
#$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.en \