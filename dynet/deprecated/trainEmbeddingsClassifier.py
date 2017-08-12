import timeit
start = timeit.default_timer()

import os
import sys
import random
import argparse
import ConfigParser

import csv

parser = argparse.ArgumentParser(description="Train a tagging model")
parser.add_argument('input', dest='d', type=str, help="embeddings file to use as input", required=True)
parser.add_argument('-m', '--model', dest='m', type=str, default='modelEmbeddingsClassifier', help="output model file name (default: \'%(default)s\')")
parser.add_argument('-w', '--vocabularies', dest='w', type=str, default='vocabsEmbeddingsClassifier', help="output file for vocabularies (default: \'%(default)s\')")
parser.add_argument('-e', '--epochs', dest='e', type=int, default=100, help="max number of epochs (default: %(default)s)")
parser.add_argument('-f', '--validation', dest='f', type=None, default=None, help="name of dataset to use for validation (validation disabled if no dataset is given)")
parser.add_argument('-p', '--patience', dest='p', type=int, default=10, help="number of validations with no improvement before training is halted (default: %(default)s)")
parser.add_argument('-i', '--intervals', dest='i', type=int, default=1000, help="number of trained samples between validations (default: %(default)s)")
parser.add_argument('-c', '--config', dest='c', type=str, default='embeddingsClassifier.config', help="configuration file (default: \'%(default)s\')")
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

if not os.path.exists(args.d):
    parser.error('embeddings input file doesn\'t exist')
with open(args.d,'r') as f:
    reader = csv.reader(f)
    lines = filter(lambda l: len(l)>0, list(reader)[1:])
    trainEmbeddings = map(lambda l: map(lambda x: float(x),l[-config.getint('Model', 'EmbeddingSize'):]), lines)
    trainTypes = map(lambda l: l[0], lines)
if args.f:
    if not os.path.exists(args.f):
        parser.error('validation embeddings file doesn\'t exist')
    with open(args.f, 'r') as f:
        reader = csv.reader(f)
        lines = filter(lambda l: len(l) > 0, list(reader)[1:])
        validationEmbeddings = map(lambda l: map(lambda x: float(x),l[-config.getint('Model', 'EmbeddingSize'):]), lines)
        validationTypes = map(lambda l: l[0], lines)

if args.v:
    print 'Loaded datasets'

vt = Vocabulary.from_corpus(trainTypes)

if args.v:
    print 'Vocabularies created'

model = dy.Model()
trainer = dy.AdamTrainer(model)

pW = model.add_parameters((config.getint('MLP', 'LayerSize'), config.getint('Model', 'EmbeddingSize')))
pU = model.add_parameters((vt.size(), config.getint('MLP', 'LayerSize')))

if args.v:
    print 'Training'

def get_graph(ws):
    dy.renew_cg()
    w = dy.parameter(pW)
    u = dy.parameter(pU)
    return u*dy.tanh(w*ws)

def train(embedding, type):
    return dy.pickneglogsoftmax(get_graph(embedding), vt.geti(type))

def classify(embedding):
    return vt.getw(np.argmax(dy.softmax(get_graph(embedding)).npvalue()))

def validate(embeddings, expected):
    good = 0
    bad = 0
    for i in xrange(len(embeddings)):
        w = embeddings[i]
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
        vt.save(f)

words_tagged = 0.0
total_loss = 0.0
indexes = range(len(trainEmbeddings))
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
                good, bad = validate(validationEmbeddings,validationTypes)
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
                    end = timeit.default_timer()
                    print 'Done!\t('+"{0:.2f}".format(end-start)+' seconds)'
                    sys.exit(0)
        embedding = trainEmbeddings[s]
        expected = trainTypes[s]
        loss = train(embedding, expected)
        total_loss += loss.scalar_value()
        words_tagged += len(embedding)
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
    good, bad= validate(validationEmbeddings, validationTypes)
    if good > best_good:
        save()

end = timeit.default_timer()

print 'Done!\t('+"{0:.2f}".format(end-start)+' seconds)'