import timeit
start = timeit.default_timer()

import os
import argparse
import ConfigParser
import csv

parser = argparse.ArgumentParser(description="Classify sentences")
parser.add_argument('input', dest='d', type=str, help="embeddings file to use as input", required=True)
parser.add_argument('-m', '--model', dest='m', type=str, default='modelEmbeddingsClassifier', help="model file name (default: \'%(default)s\')")
parser.add_argument('-w', '--vocabularies', dest='w', type=str, default='vocabsEmbeddingsClassifier', help="vocabularies file name(default: \'%(default)s\')")
parser.add_argument('-c', '--config', dest='c', type=str, default='embeddingsClassifier.config', help="configuration file (default: \'%(default)s\')")
parser.add_argument('-v', '--verbose', dest='v', help="print progress information during training", action='count')
args = parser.parse_args()

import dynet as dy
import numpy as np

config = ConfigParser.ConfigParser()
config.read(args.c)

if not os.path.exists(args.m):
    parser.error('model is missing')
if not os.path.exists(args.w):
    parser.error('vocabularies are missing')

if not os.path.exists(args.d):
    parser.error('embeddings input is missing')
with open(args.d,'r') as f:
    reader = csv.reader(f)
    lines = filter(lambda l: len(l)>0, list(reader)[1:])
    embeddings = map(lambda l: map(lambda x: float(x),l[-config.getint('Model', 'EmbeddingSize'):]), lines)
if args.v:
    print 'Loaded dataset'

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

vt = Vocabulary()
with open(args.w,'r') as f:
    for l in f.readlines():
        vt.add(l.rsplit('\t',1)[0])
if args.v:
    print 'Loaded vocabularies'

model = dy.Model()

pW = model.add_parameters((config.getint('MLP', 'LayerSize'), config.getint('Model', 'EmbeddingSize')))
pU = model.add_parameters((vt.size(), config.getint('MLP', 'LayerSize')))

model.load_all(args.m)
if args.v:
    print 'Loaded model'

if args.v:
    print 'Classifying'

def get_graph(ws):
    dy.renew_cg()
    w = dy.parameter(pW)
    u = dy.parameter(pU)
    return u*dy.tanh(w*ws)

def classify(words):
    return vt.getw(np.argmax(dy.softmax(get_graph(words)).npvalue()))

with open(args.d+'.out','w') as f:
    i = 1
    l = len(embeddings)
    s  = str(l)
    for w in embeddings:
        if args.v:
            print '\r\t' + str(i).zfill(len(s)) + '/' + s + '  (' + "{0:.2f}".format(100.0 * i / l) + '%)',
        f.write(classify(w)+'\n')
        i += 1
    if args.v:
        print ''

end = timeit.default_timer()

print 'Done!\t('+"{0:.2f}".format(end-start)+' seconds)'