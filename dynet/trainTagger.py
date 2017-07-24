import timeit
start = timeit.default_timer()

import os
import sys
import random
import argparse
import ConfigParser

parser = argparse.ArgumentParser(description="Train a tagging model")
parser.add_argument('-d', '--dataset', dest='d', type=str, help="name of dataset to use for training", required=True)
parser.add_argument('-m', '--model', dest='m', type=str, default='modelTagger', help="output model file name (default: \'%(default)s\')")
parser.add_argument('-w', '--vocabularies', dest='w', type=str, default='vocabsTagger', help="output file for vocabularies (default: \'%(default)s\')")
parser.add_argument('-e', '--epochs', dest='e', type=int, default=100, help="max number of epochs (default: %(default)s)")
parser.add_argument('-f', '--validation', dest='f', type=None, default=None, help="name of dataset to use for validation (validation disabled if no dataset is given)")
parser.add_argument('-p', '--patience', dest='p', type=int, default=10, help="number of validations with no improvement before training is halted (default: %(default)s)")
parser.add_argument('-i', '--intervals', dest='i', type=int, default=1000, help="number of trained samples between validations (default: %(default)s)")
parser.add_argument('-c', '--config', dest='c', type=str, default='tagger.config', help="configuration file (default: \'%(default)s\')")
parser.add_argument('-v', '--verbose', dest='v', help="print progress information during training", action='count')
parser.add_argument('-r', '--report', dest='r', type=int, default=1000, help="number of samples between progress reports (default: %(default)s)")
args = parser.parse_args()

config = ConfigParser.ConfigParser()
config.read(args.c)

import dynet as dy
import numpy as np

class Vocabulary:
    def __init__(self):
        self.w2i = {}
        self.i2w = {}
    def size(self):
        return len(self.w2i.keys())
    def add(self,w):
        if w not in self.w2i.keys():
            i = len(self.w2i.keys())
            self.w2i[w] = i
            self.i2w[i] = w
    def geti(self,w):
        if w in self.w2i.keys():
            return self.w2i[w]
        return -1
    def getw(self,i):
        if i in self.i2w.keys():
            return self.i2w[i]
        return None
    @staticmethod
    def from_corpus(corpus):
        v = Vocabulary()
        for w in corpus:
            v.add(w)
        return v
    def save(self,f):
        for i in sorted(self.i2w.keys()):
            f.write(self.i2w[i]+'\t'+str(i)+'\n')
        f.write('\n')

if (not os.path.exists(args.d+'.words')) or (not os.path.exists(args.d+'.tags')):
    parser.error('train dataset is missing essential files')
with open(args.d+'.words','r') as f:
    trainWords = [l.strip().split(' ') for l in f.readlines()]
with open(args.d+'.tags','r') as f:
    trainTags = [l.strip().split(' ') for l in f.readlines()]
if args.f:
    if (not os.path.exists(args.f + '.words')) or (not os.path.exists(args.f + '.tags')):
        parser.error('validation dataset is missing essential files')
    with open(args.f + '.words', 'r') as f:
        validationWords = [l.strip().split(' ') for l in f.readlines()]
    with open(args.f + '.tags', 'r') as f:
        validationTags = [l.strip().split(' ') for l in f.readlines()]
words = list(reduce(lambda x,y: x.union(y), map(lambda w:set(w), trainWords), set()))
tags = list(reduce(lambda x, y: x.union(y), map(lambda t:set(t), trainTags), set()))

if args.v:
    print 'Loaded datasets'

wordCount = {}
for t in trainWords:
    for w in t:
        if w not in wordCount.keys():
            wordCount[w] = 1
        else:
            wordCount[w] += 1

vw = Vocabulary.from_corpus(words)
vt = Vocabulary.from_corpus(tags)

if args.v:
    print 'Vocabularies created'

model = dy.Model()
trainer = dy.AdamTrainer(model)

wordsLookup = model.add_lookup_parameters((vw.size(),config.getint('Model', 'WordEmbeddingSize')))

pH = model.add_parameters((config.getint('MLP', 'LayerSize'), config.getint('Model', 'HiddenLayerHalfSize')*2))
pO = model.add_parameters((vt.size(), config.getint('MLP', 'LayerSize')))

fwd = dy.LSTMBuilder(1, config.getint('Model', 'WordEmbeddingSize'), config.getint('Model', 'HiddenLayerHalfSize'), model)
bwd = dy.LSTMBuilder(1, config.getint('Model', 'WordEmbeddingSize'), config.getint('Model', 'HiddenLayerHalfSize'), model)

if args.v:
    print 'Training'

def get_graph(ws):
    dy.renew_cg()
    h = dy.parameter(pH)
    o = dy.parameter(pO)
    fi = fwd.initial_state()
    bi = bwd.initial_state()
    word_embs = [wordsLookup[vw.geti(w)] for w in ws]
    fexps = fi.transduce(word_embs)
    bexps = bi.transduce(reversed(word_embs))
    exps = [dy.concatenate([f,b]) for f,b in zip(fexps,reversed(bexps))]
    return map(lambda x: o*dy.tanh(h*x), exps)

def train(words,tags):
    return dy.esum([dy.pickneglogsoftmax(w,vt.geti(t)) for w,t in zip(get_graph(words),tags)])

def tag(words):
    return [vt.getw(np.argmax(dy.softmax(w).npvalue())) for w in (get_graph(words))]

def validate(words,expected):
    good = 0
    bad = 0
    wgood = 0
    wbad = 0
    for i in xrange(len(words)):
        w = words[i]
        e = expected[i]
        t = tag(w)
        if t == e:
            good += 1
        else:
            bad += 1
        wvalidate = map(lambda j: e[j] == t[j], xrange(max(len(e),len(t))))
        wgood += wvalidate.count(True)
        wbad += wvalidate.count(False)
    return (good,bad,wgood,wbad)

def save():
    try:
        os.remove(args.m)
    except OSError:
        pass
    model.save_all(args.m)
    with open(args.w,'w') as f:
        vw.save(f)
        vt.save(f)

words_tagged = 0.0
total_loss = 0.0
indexes = range(len(trainWords))
patience = 0
best_good = 0
best_bad = 0
best_wgood = 0
best_wbad = 0
for j in xrange(args.e):
    random.shuffle(indexes)
    for i in xrange(len(indexes)):
        s = indexes[i]
        if args.v:
            if i > 0 and i % args.r == 0:
                trainer.status()
                print 'Loss: '+"{0:.2f}".format(total_loss / words_tagged)
                total_loss = 0.0
                words_tagged = 0.0
        if args.f:
            if i % args.i == 0 or i == len(indexes)-1:
                good, bad, wgood, wbad = validate(validationWords,validationTags)
                if args.v:
                    print 'Validation:'
                    print '\tSentences: '+str(good)+' ('+"{0:.2f}".format(100.0 * good / (good + bad))+')'
                    print '\tWords: '+str(wgood)+' ('+"{0:.2f}".format(100.0 * wgood / (wgood + wbad))+')'
                if (wgood > best_wgood) or ((wgood == best_wgood) and (good >= best_good)):
                    if (wgood > best_wgood) or ((wgood == best_wgood) and (good > best_good)):
                        best_wgood = wgood
                        best_wbad = wbad
                        best_good = good
                        best_bad = bad
                        patience = 0
                    else:
                        patience += 1
                    save()
                else:
                    patience += 1
                if patience >= args.p:
                    print 'No progress for the last '+str(args.p)+' validations. Training stopped'
                    print 'Done!'
                    sys.exit(0)
        words = trainWords[s]
        expected = trainTags[s]
        loss = train(words, expected)
        total_loss += loss.scalar_value()
        words_tagged += len(words)
        loss.backward()
        trainer.update()
    if args.v:
        print "epoch %r finished" % j
    trainer.update_epoch(1.0)
    if not args.f:
        save()

if args.v:
    print 'Reached max epochs. Training stopped'

if args.f:
    good, bad, wgood, wbad = validate(validationWords, validationTags)
    if (wgood > best_wgood) or ((wgood == best_wgood) and (good > best_good)):
        save()

end = timeit.default_timer()

print 'Done!\t('+"{0:.2f}".format(end-start)+' seconds)'