#!/usr/bin/env bash
#install_name_tool -change libboost_program_options.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_program_options.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
#install_name_tool -change libboost_serialization.dylib /Users/roeeaharoni/boost_1_55_0/stage/lib/libboost_serialization.dylib /Users/roeeaharoni/git/dynet/build/dynet/libdynet.dylib
base_path=/home/nlp/aharonr6

export LC_ALL=en_US.UTF-8
export LANG=en_US.UTF-8

python ../dynmt.py --dynet-mem 8000 --dynet-gpu-ids 3 --input-dim=100 --hidden-dim=500 --epochs=100 --lstm-layers=1 \
--optimization=ADADELTA --batch-size=32 --beam-size=10 \
$base_path/git/research/nmt/data/news-de-en/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.de \
$base_path/git/research/nmt/data/news-de-en/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.en \
$base_path/git/research/nmt/data/news-de-en/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.de \
$base_path/git/research/nmt/data/news-de-en/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.en \
$base_path/git/research/nmt/data/news-de-en/test/newstest2016-deen.tok.penntrg.clean.true.bpe.de \
$base_path/git/research/nmt/data/news-de-en/test/newstest2016-deen.tok.penntrg.clean.true.bpe.en \
$base_path/git/dynet-seq2seq-attn/results/test_gpu_batch

# large train files
#$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.de \
#$base_path/git/research/nmt/data/news-de-en-50/train/news-commentary-v8.de-en.tok.penntrg.clean.true.bpe.en \

# he-en files
# /Users/roeeaharoni/git/dynet-seq2seq-attn/data/he_en_clean/train.tags.he-en.he.clean \
#/Users/roeeaharoni/git/dynet-seq2seq-attn/data/he_en_clean/train.tags.he-en.en.clean \
#/Users/roeeaharoni/git/dynet-seq2seq-attn/data/he_en_clean/IWSLT14.TED.dev2010.he-en.he.xml.clean \
#/Users/roeeaharoni/git/dynet-seq2seq-attn/data/he_en_clean/IWSLT14.TED.dev2010.he-en.en.xml.clean \
#/Users/roeeaharoni/git/dynet-seq2seq-attn/data/he_en_clean/IWSLT14.TED.tst2010.he-en.he.xml.clean \
#/Users/roeeaharoni/git/dynet-seq2seq-attn/data/he_en_clean/IWSLT14.TED.tst2010.he-en.he.xml.clean \


