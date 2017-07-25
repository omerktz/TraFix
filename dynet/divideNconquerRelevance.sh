#!/bin/bash
set -x
# prepare
python relevanceTags.py train
python relevanceTags.py test
python relevanceTags.py validate
# split
python splitByRelevance.py train
python splitByRelevance.py test
python splitByRelevance.py validate
# train
python trainTagger.py -d train1 -f validate1 -m model1 -w vocabs1 -v
python trainTagger.py -d train2 -f validate2 -m model2 -w vocabs2 -v
python trainTagger.py -d train3 -f validate3 -m model3 -w vocabs3 -v
python trainTagger.py -d train4 -f validate4 -m model4 -w vocabs4 -v
python trainTagger.py -d train5 -f validate5 -m model5 -w vocabs5 -v
# tag
python tagger.py -d train1 -m model1 -w vocabs1 -v
python tagger.py -d train2 -m model2 -w vocabs2 -v
python tagger.py -d train3 -m model3 -w vocabs3 -v
python tagger.py -d train4 -m model4 -w vocabs4 -v
python tagger.py -d train5 -m model5 -w vocabs5 -v
python tagger.py -d test1 -m model1 -w vocabs1 -v
python tagger.py -d test2 -m model2 -w vocabs2 -v
python tagger.py -d test3 -m model3 -w vocabs3 -v
python tagger.py -d test4 -m model4 -w vocabs4 -v
python tagger.py -d test5 -m model5 -w vocabs5 -v
python tagger.py -d validate1 -m model1 -w vocabs1 -v
python tagger.py -d validate2 -m model2 -w vocabs2 -v
python tagger.py -d validate3 -m model3 -w vocabs3 -v
python tagger.py -d validate4 -m model4 -w vocabs4 -v
python tagger.py -d validate5 -m model5 -w vocabs5 -v
# rebuild
python rebuildRelevance.py train
python rebuildRelevance.py test
python rebuildRelevance.py validate
# diff
diff validate.tags validate.out >> validate.diff
diff test.tags test.out >> test.diff
diff train.tags train.out >> train.diff