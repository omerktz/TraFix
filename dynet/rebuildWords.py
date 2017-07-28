import sys
import os
import itertools
if not os.path.exists(sys.argv[1]+'.counts'):
    print 'Dataset counts missing'
if not os.path.exists(sys.argv[1]+'.corpus.out'):
    print 'Dataset translation missing'

n = int(sys.argv[2])

with open(sys.argv[1]+'.counts','r') as fcounts:
    counts = [int(l.strip()) for l in fcounts.readlines()]
with open(sys.argv[1]+'1.'+str(n)+'.corpus.out','r') as fout:
    lines = [l.strip() for l in fout.readlines()]
with open(sys.argv[1]+'.'+str(n*n)+'.corpus.out','w') as fout:
    i = 0;
    count = 0
    for k in counts:
        trans = []
        for j in range(k):
            current = []
            for l in range(n):
                current.append(lines[i])
                i += 1
            trans.append(current)
        for p in itertools.product(*trans):
            fout.write(str(count)+' ||| '+' '.join(p).strip()+' ||| \n')
        count += 1
