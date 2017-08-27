import argparse
import csv
import os
import random
import shutil
import timeit

import _dynet as dy
import numpy as np
import sys

sys.path.insert(0,'..')
from utils.mapWrodToType import getType

start = timeit.default_timer()

parser = argparse.ArgumentParser(description="Test embedding classification (using leave-one-out method)")
parser.add_argument('input', type=str, help="embeddings file to use as input")
parser.add_argument('-o', '--output', dest='o', type=str, default='output', help="output directory to record failures (default: %(default)s)")
parser.add_argument('-e', '--epochs', dest='e', type=int, default=100, help="max number of epochs (default: %(default)s)")
parser.add_argument('-v', '--verbose', dest='v', help="print progress information during training", action='count')
parser.add_argument('-vv', '--super-verbose', dest='vv', help="print additional progress information during training", action='count')
parser.add_argument('-t', '--timings', dest='t', help="report inner timings", action='count')
parser.add_argument('-es', '--embedding-size', dest='s', type=int, default=512, help="size of embedding vector (default: %(default)s)")
parser.add_argument('-ms', '--mlp-layer-size', dest='m', type=int, default=32, help="size of mlp layer (default: %(default)s)")
parser.add_argument('-s', '--seed', dest='seed', type=int, default=13371337, help="random seed (default: %(default)s)")
args = parser.parse_args()

rnd = random.Random(args.seed)

dyparams = dy.DynetParams()
dyparams.set_random_seed(args.seed)
dyparams.init()

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

if not os.path.exists(args.input):
    parser.error('embeddings input file doesn\'t exist')
with open(args.input,'r') as f:
    lines = filter(lambda l: len(l)>0, list(csv.reader(f))[1:])

embeddings = map(lambda l: map(lambda x: float(x),l[-args.s:]), lines)
words = map(lambda l: l[0], lines)
types = map(lambda w: getType(w).name, words)
data = zip(embeddings, words, types)

vocab = Vocabulary.from_corpus(types)

if args.v or args.vv:
    print 'Loaded data'

class TrainAndTest:

    def __init__(self, train, test, dir):
        self.model = dy.Model()
        self.trainer = dy.AdamTrainer(self.model)

        self.pW = self.model.add_parameters((args.m, args.s))
        self.pU = self.model.add_parameters((vocab.size(), args.m))

        self.trainData = train
        self.testData = test
        self.dir = dir
        if os.path.exists(self.dir):
            shutil.rmtree(self.dir)

    def get_graph(self, embedding):
        dy.renew_cg()
        w = dy.parameter(self.pW)
        u = dy.parameter(self.pU)
        return u*dy.tanh(w*dy.inputTensor(embedding))

    def train_single(self, embedding, type):
        return dy.pickneglogsoftmax(self.get_graph(embedding), vocab.geti(type))

    def classify_single(self, embedding):
        return vocab.getw(np.argmax(dy.softmax(self.get_graph(embedding)).npvalue()))

    def save_failure(self, s, t):
        if not os.path.exists(self.dir):
            os.makedirs(self.dir)
            self.model.save(os.path.join(self.dir,'model'))
            with open(os.path.join(self.dir,'failures.csv'), 'w') as f:
                csv.writer(f).writerow(['embedding','word','expected','type'])
        with open(os.path.join(self.dir,'failures.csv'), 'a') as f:
            csv.writer(f).writerow(map(str,s)+[t])

    def train(self):
        start_time = timeit.default_timer()
        if args.v or args.vv:
            print 'Training... ',
        indexes = range(len(self.trainData))
        for j in xrange(args.e):
            embeddings_tagged = 0.0
            total_loss = 0.0
            rnd.shuffle(indexes)
            for i in xrange(len(indexes)):
                s = self.trainData[i]
                embedding = s[0]
                expected = s[2]
                loss = self.train_single(embedding, expected)
                total_loss += loss.scalar_value()
                embeddings_tagged += 1
                loss.backward()
                self.trainer.update()
            self.trainer.update_epoch(1.0)
        if args.v or args.vv:
            print 'Done!'
            if args.vv:
                print '\tFinal loss: '+str(total_loss)+' over '+str(embeddings_tagged)+' embeddings'
        end_time = timeit.default_timer()
        if args.t:
            print '\tTiming: '+"{0:.2f}".format(end_time-start_time)
        return self

    def test(self):
        start_time = timeit.default_timer()
        if args.v or args.vv:
            print 'Testing... ',
        failures = []
        for s in self.testData:
            embedding = s[0]
            expected = s[2]
            classified_type = self.classify_single(embedding)
            if expected != classified_type:
                self.save_failure(s, classified_type)
                failures.append((expected,classified_type))
        if args.v or args.vv:
            total = len(self.testData)
            print 'Done!'
            if args.vv:
                print '\tSuccesses: '+str(total-len(failures))+'/'+str(total)+' ('+"{0:.2f}".format(100*(total-len(failures))/float(total))+')'
                # print '\tFailures: '+str(len(failures))+'/'+str(total)+' ('+"{0:.2f}".format(100*len(failures)/float(total))+'%)'
        end_time = timeit.default_timer()
        if args.t:
            print '\tTiming: '+"{0:.2f}".format(end_time-start_time)
        return failures

if os.path.exists(args.o):
    shutil.rmtree(args.o)
os.makedirs(args.o)

data_len_str = str(len(data))
failure_matrix = {}
type_counter = {}
type_successes = {}
for i in range(len(data)):
    print '\r'+str(i+1).zfill(len(data_len_str))+'/'+data_len_str,
    sys.stdout.flush()
    res = TrainAndTest(data[0:i]+data[i+1:], [data[i]], os.path.join(args.o, str(i))).train().test()
    expected = data[i][2]
    if expected not in failure_matrix.keys():
        failure_matrix[expected] = {}
        failure_matrix[expected][expected] = 0
    if expected not in type_counter.keys():
        type_counter[expected] = 0
    if expected not in type_successes.keys():
        type_successes[expected] = 0
    type_counter[expected] += 1
    if len(res) == 0:
        type_successes[expected] += 1
        failure_matrix[expected][expected] += 1
    else:
        classified_type = res[0][1]
        if classified_type not in failure_matrix[expected].keys():
            failure_matrix[expected][classified_type] = 0
        failure_matrix[expected][classified_type] += 1
print ''
total_successes = sum(type_successes.values())
print str(total_successes) + ' out of ' + str(len(data)) + ' tests passed (' + "{0:.2f}".format(100 * total_successes / float(len(data))) + '%)'

with open('failures.csv', 'w') as fout:
    csvout = csv.writer(fout)
    first = True
    for d in sorted(os.listdir(args.o), key=lambda x: int(x)):
        with open(os.path.join(args.o, d, 'failures.csv'), 'r') as fin:
            lines = list(csv.reader(fin))
            if first:
                csvout.writerow(['dir']+lines[0])
                first = False
            csvout.writerow([d]+lines[1])
with open('failures_matrix.csv', 'w') as fout:
    csvout = csv.writer(fout)
    types = sorted(type_counter.keys())
    csvout.writerow(['Counters'])
    csvout.writerow(types+['TOTAL'])
    csvout.writerow(map(lambda t: str(type_counter[t]), types)+[str(sum(type_counter.values()))])
    csvout.writerow([])
    csvout.writerow(['Matrix'])
    csvout.writerow(['']+types)
    for t in types:
        csvout.writerow([t] + map(lambda x: str(failure_matrix[t][x] if x in failure_matrix[t].keys() else 0),types))

end = timeit.default_timer()

print 'Done!\t('+"{0:.2f}".format(end-start)+' seconds)'
