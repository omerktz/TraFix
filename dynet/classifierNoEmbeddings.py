import timeit
start = timeit.default_timer()

import os
import argparse
import ConfigParser

parser = argparse.ArgumentParser(description="Classify sentences")
parser.add_argument('-d', '--dataset', dest='d', type=str, help="name of dataset to classify", required=True)
parser.add_argument('-m', '--model', dest='m', type=str, default='modelClassifier', help="model file name (default: \'%(default)s\')")
parser.add_argument('-w', '--vocabularies', dest='w', type=str, default='vocabsClassifier', help="vocabularies file name(default: \'%(default)s\')")
parser.add_argument('-c', '--config', dest='c', type=str, default='classifierNoEmbeddings.config', help="configuration file (default: \'%(default)s\')")
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

if not os.path.exists(args.d+'.words'):
    parser.error('dataset is missing')
with open(args.d+'.words','r') as f:
    words = [l.strip().split(' ') for l in f.readlines()]
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

vw = Vocabulary()
vt = Vocabulary()
def loadVocabs():
    with open(args.w,'r') as f:
        v = vw
        for l in f.readlines():
            l = l.strip()
            if len(l) == 0:
                v = vt
            else:
                v.add(l.rsplit('\t',1)[0])
loadVocabs()
if args.v:
    print 'Loaded vocabularies'

model = dy.Model()

#wordsLookup = model.add_lookup_parameters((vw.size(),config.getint('Model', 'WordEmbeddingSize')))

pH = model.add_parameters((config.getint('MLP', 'LayerSize'), config.getint('Model', 'HiddenLayerSize')*2))
pO = model.add_parameters((vt.size(), config.getint('MLP', 'LayerSize')))

# for classify we want summary of sentence, not context of word in sentence, so backward lstm is not needed
lstm = dy.LSTMBuilder(layers=1, input_dim=config.getint('Model', 'WordEmbeddingSize'), hidden_dim=config.getint('Model', 'HiddenLayerSize'), model=model)

model.load_all(args.m)
if args.v:
    print 'Loaded model'

if args.v:
    print 'Classifying'

def get_graph(ws):
    dy.renew_cg()
    h = dy.parameter(pH)
    o = dy.parameter(pO)
    l = lstm.initial_state()
    #word_embs = [wordsLookup[vw.geti(w)] for w in ws]
    exps = l.transduce(ws)
    # only use summary of sentence (last value from transduce)
    return o*dy.tanh(h*exps[-1])

def tag(words):
    return vt.getw(np.argmax(dy.softmax(get_graph(words)).npvalue()))

with open(args.d+'.out','w') as f:
    i = 1
    l = len(words)
    s  = str(l)
    for w in words:
        if args.v:
            print '\r\t' + str(i).zfill(len(s)) + '/' + s + '  (' + "{0:.2f}".format(100.0 * i / l) + '%)',
        f.write(tag(w)+'\n')
        i += 1
    if args.v:
        print ''

end = timeit.default_timer()

print 'Done!\t('+"{0:.2f}".format(end-start)+' seconds)'