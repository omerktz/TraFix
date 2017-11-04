#!/usr/bin/env bash
#install_name_tool -change libboost_program_options.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_program_options.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
#install_name_tool -change libboost_serialization.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_serialization.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
base_path=/home/nlp/aharonr6
#base_path=/Users/roeeaharoni

export LC_ALL=en_US.UTF-8
export LANG=en_US.UTF-8
python ../dynmt.py --dynet-gpu-ids 1 --dynet-mem 4000 --input-dim=256 --hidden-dim=256 --epochs=100 --lstm-layers=1 \
--optimization=ADADELTA --batch-size=64 --beam-size=10 --plot --eval-after=1000 \
$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.de \
$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.en \
$base_path/git/research/nmt/data/news-de-en-50/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.de \
$base_path/git/research/nmt/data/news-de-en-50/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.en \
$base_path/git/research/nmt/data/news-de-en-50/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.de \
$base_path/git/research/nmt/data/news-de-en-50/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.en \
$base_path/git/dynet-seq2seq-attn/results/test_de_en_large

# test files
#$base_path/git/research/nmt/data/news-de-en/test/newstest2016-deen.tok.penntrg.clean.true.bpe.de \
#$base_path/git/research/nmt/data/news-de-en/test/newstest2016-deen.tok.penntrg.clean.true.bpe.en \

# large train files
#$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.de \
#$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.en \