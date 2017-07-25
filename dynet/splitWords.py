import sys
import os
import ast
if not os.path.exists(sys.argv[1]+'.words'):
    print 'Dataset input missing'
if not os.path.exists(sys.argv[1]+'.tags'):
    print 'Dataset tags missing'

with open(sys.argv[1]+'.words','r') as fwords:
    words = [l.strip().split(' ') for l in fwords.readlines()]
with open(sys.argv[1]+'.tags','r') as ftags:
    lines = [l.strip().split(' ') for l in ftags.readlines()]
    tags = map(lambda l: map(lambda x:ast.literal_eval(x), l), lines)
with open(sys.argv[1]+'.corpus.c','w') as fc:
    with open(sys.argv[1] + '.counts', 'w') as fcount:
        for i in range(len(words)):
            w = words[i]
            t = tags[i]
            max_tag = max(reduce(lambda x,y: x+y, t, []))
            fcount.write(str(max_tag)+'\n')
            for j in range(1, max_tag+1):
                fc.write(' '.join(map(lambda y: w[y], filter(lambda x: j in t[x], range(len(w)))))+'\n')
