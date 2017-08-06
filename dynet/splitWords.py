import sys
import os
import ast
import re

if not os.path.exists(sys.argv[1]+'.words'):
    print 'Dataset input missing'
if not os.path.exists(sys.argv[1]+'.tags'):
    print 'Dataset tags missing'

def normalize_ll(words):
    mapsto = {}
    res = []
    for i in range(len(words)):
        w = words[i]
        if re.match('^%[0-9]+$', w):
            num = int(w[1:])
            if num not in mapsto.keys():
                mapsto[num] = len(mapsto.keys())+1
            res.append('%'+str(mapsto[num]))
        else:
            res.append(w)
    return res

with open(sys.argv[1]+'.words','r') as fwords:
    words = [l.strip().split(' ') for l in fwords.readlines()]
with open(sys.argv[1]+'.tags','r') as ftags:
    lines = [l.strip().split(' ') for l in ftags.readlines()]
    tags = map(lambda l: map(lambda x:ast.literal_eval(x), l), lines)
with open(sys.argv[1]+'1.corpus.ll','w') as fc:
    with open(sys.argv[1] + '.counts', 'w') as fcount:
        for i in range(len(words)):
            w = words[i]
            t = tags[i]
            max_tag = max(reduce(lambda x,y: x+y, t, []))
            fcount.write(str(max_tag)+'\n')
            for j in range(1, max_tag+1):
                fc.write(' '.join(normalize_ll(map(lambda y: w[y], filter(lambda x: j in t[x], range(len(w))))))+'\n')
