import sys
import os
import shutil
import ast
if not os.path.exists(sys.argv[1]+'.words'):
    print 'Dataset input missing'
if not os.path.exists(sys.argv[1]+'.tags'):
    print 'Dataset tags missing'

with open(sys.argv[1]+'.tags','r') as ftags:
    lines = [l.strip().split(' ') for l in ftags.readlines()]
    tags = map(lambda l: map(lambda x:ast.literal_eval(x), l), lines)
    max_tag = max(reduce(lambda z, w: z.union(w), map(lambda l: set(reduce(lambda x, y: x+y, l, [])), tags), set()))
for i in range(1, max_tag+1):
    shutil.copy(sys.argv[1]+'.words', sys.argv[1]+str(i)+'.words')
    with open(sys.argv[1]+str(i)+'.tags', 'w') as fout:
        for l in tags:
            fout.write(' '.join(map(lambda t: str(i in t), l))+'\n')