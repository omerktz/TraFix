import argparse

parser = argparse.ArgumentParser(description="Count inputs that match given filters")
parser.add_argument('-d', '--dataset', type=str, help="filter a dataset file", action='append', metavar="DDD", required=False)
parser.add_argument('-f', '--file', type=str, help="filter a tab seperated file", action='append', metavar="FFF", required=False)
parser.add_argument('-a', '--and', dest='a', help="inputs must match all filters", action='count')
parser.add_argument('-o', '--or', dest='o', help="inputs need only match one filter", action='count')
parser.add_argument('-n', help="number of translations per input (default: 1)", required=False, default=1, type=int)
parser.add_argument('filters', help="list of filter files, separated by whitespace", nargs='+')
args = parser.parse_args()

if len(args.filters) > 1:
    if (1 if args.a else 0) + (1 if args.o else 0) != 1:
        parser.error('Must choose to either -o or -a in case of multiple filters (but not both)')

if not args.dataset and not args.file:
    parser.error('Must choose either a dataset (-d) or a file (-f) as input')

def load_filter(f):
    if f.endswith('.py'):
        f = f[:-3]
    if f.endswith('.pyc'):
        f = f[:-4]
    return __import__(f).filter

filters = map(load_filter,args.filters)

import os

def handleDataset(d, filters):
    if os.path.exists(d+'.corpus.c'):
        with open(d+'.corpus.c','r') as f:
            cs = [l.strip() for l in f.readlines()]
    else:
        cs = []
    if os.path.exists(d+'.corpus.ll'):
        with open(d+'.corpus.ll','r') as f:
            lls = [l.strip() for l in f.readlines()]
    else:
        lls = []
    if os.path.exists(d+'.corpus.out'):
        with open(d+'.corpus.out','r') as f:
            outs = [l.strip() for l in f.readlines()]
    else:
        outs = []
    assert len(cs)%args.n == 0
    total = max(len(cs),len(lls),len(outs)/args.n)
    count = 0
    for i in range(total):
        if args.a:
            if len(filter(lambda f: not f(cs[i] if i < len(cs) else None, lls[i] if i < len(lls) else None, outs[i:i+args.n] if i < len(outs) else None), filters)) == 0:
                count += 1
        else:
            if len(filter(lambda f: f(cs[i] if i < len(cs) else None, lls[i] if i < len(lls) else None, outs[i:i+args.n] if i < (len(outs)/args.n) else None), filters)) > 0:
                count += 1
    print 'DATASET '+d+': '+str(count)+'/'+str(total)+' lines matched filter(s)'
    return (count,total)

def handleFile(f, filters):
    if not os.path.exists(f):
        return (0,0)
    else:
        with open(f,'r') as fin:
            count = 0
            total = 0
            first = True
            for l in fin.readlines():
                if first:
                    first = False
                else:
                    l = filter(lambda y: len(y)>0, map(lambda x: x.strip().replace('~_~',' , '), l.strip().replace(' , ','~_~').split(',')))
                    if len(l) > 0:
                        total += 1
                        if args.a:
                            if len(filter(lambda f: not f(l[0],l[1],l[2:]),filters)) == 0:
                                count += 1
                        else:
                            if len(filter(lambda f: f(l[0],l[1],l[2:]), filters)) > 0:
                                count += 1
        print 'FILE '+f+': '+str(count)+'/'+str(total)+' lines matched filter(s)'
        return (count,total)

total = 0
count = 0

if args.dataset:
    results = map(lambda d: handleDataset(d, filters), args.dataset)
    count += sum(map(lambda x: x[0], results))
    total += sum(map(lambda x: x[1], results))

if args.file:
    results = map(lambda f: handleFile(f, filters), args.file)
    count += sum(map(lambda x: x[0], results))
    total += sum(map(lambda x: x[1], results))

print 'TOTAL: '+str(count)+'/'+str(total)+' lines matched filter(s)'

