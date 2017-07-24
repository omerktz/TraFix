import timeit
start = timeit.default_timer()

import os
import sys
import random
import argparse
import ConfigParser

parser = argparse.ArgumentParser(description="Train a tagging model")
parser.add_argument('-d', '--dataset', dest='d', type=str, help="name of dataset to use for training", required=True)
parser.add_argument('-m', '--model', dest='m', type=str, default='modelClassifier', help="output model file name (default: \'%(default)s\')")
parser.add_argument('-w', '--vocabularies', dest='w', type=str, default='vocabsClassifier', help="output file for vocabularies (default: \'%(default)s\')")
parser.add_argument('-e', '--epochs', dest='e', type=int, default=100, help="max number of epochs (default: %(default)s)")
parser.add_argument('-f', '--validation', dest='f', type=None, default=None, help="name of dataset to use for validation (validation disabled if no dataset is given)")
parser.add_argument('-p', '--patience', dest='p', type=int, default=10, help="number of validations with no improvement before training is halted (default: %(default)s)")
parser.add_argument('-i', '--intervals', dest='i', type=int, default=1000, help="number of trained samples between validations (default: %(default)s)")
parser.add_argument('-c', '--config', dest='c', type=str, default='classifier.config', help="configuration file (default: \'%(default)s\')")
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
    trainTags = [l.strip() for l in f.readlines()]
if args.f:
    if (not os.path.exists(args.f + '.words')) or (not os.path.exists(args.f + '.tags')):
        parser.error('validation dataset is missing essential files')
    with open(args.f + '.words', 'r') as f:
        validationWords = [l.strip().split(' ') for l in f.readlines()]
    with open(args.f + '.tags', 'r') as f:
        validationTags = [l.strip() for l in f.readlines()]

if args.v:
    print 'Loaded datasets'

wordCount = {}
for t in trainWords:
    for w in t:
        if w not in wordCount.keys():
            wordCount[w] = 1
        else:
            wordCount[w] += 1

vw = Vocabulary.from_corpus(list(reduce(lambda x,y: x.union(y), map(lambda w:set(w), trainWords), set())))
vt = Vocabulary.from_corpus(trainTags)

if args.v:
    print 'Vocabularies created'

model = dy.Model()
trainer = dy.AdamTrainer(model)

wordsLookup = model.add_lookup_parameters((vw.size(),config.getint('Model', 'WordEmbeddingSize')))

pH = model.add_parameters((config.getint('MLP', 'LayerSize'), config.getint('Model', 'HiddenLayerSize')))
pO = model.add_parameters((vt.size(), config.getint('MLP', 'LayerSize')))

# for classify we want summary of sentence, not context of word in sentence, so backward lstm is not needed
lstm = dy.LSTMBuilder(layers=1, input_dim=config.getint('Model', 'WordEmbeddingSize'), hidden_dim=config.getint('Model', 'HiddenLayerSize'), model=model)

if args.v:
    print 'Training'

def get_graph(ws):
    dy.renew_cg()
    h = dy.parameter(pH)
    o = dy.parameter(pO)
    l = lstm.initial_state()
    word_embs = [wordsLookup[vw.geti(w)] for w in ws]
    exps = l.transduce(word_embs)
    # only use summary of sentence (last value from transduce)
    return o*dy.tanh(h*exps[-1])

def train(words,tag):
    return dy.pickneglogsoftmax(get_graph(words),vt.geti(tag))

def classify(words):
    return vt.getw(np.argmax(dy.softmax(get_graph(words)).npvalue()))

def validate(words,expected):
    good = 0
    bad = 0
    for i in xrange(len(words)):
        w = words[i]
        e = expected[i]
        t = classify(w)
        if t == e:
            good += 1
        else:
            bad += 1
    return (good,bad)

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
                good, bad = validate(validationWords,validationTags)
                if args.v:
                    print 'Validation:'
                    print '\tSentences: '+str(good)+' ('+"{0:.2f}".format(100.0 * good / (good + bad))+')',
                if good >= best_good:
                    if good > best_good:
                        best_good = good
                        best_bad = bad
                        patience = 0
                    else:
                        patience += 1
                    save()
                else:
                    patience += 1
                if args.v:
                    print '\t['+str(patience)+'/'+str(args.p)+']'
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
    good, bad= validate(validationWords, validationTags)
    if good > best_good:
        save()

end = timeit.default_timer()

print 'Done!\t('+"{0:.2f}".format(end-start)+' seconds)'