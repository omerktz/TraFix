import sys
import os
import itertools

n = int(sys.argv[2])

if not os.path.exists(sys.argv[1]+'.counts'):
    print 'Dataset counts missing'
if not os.path.exists(sys.argv[1]+'1.corpus.'+str(n)+'.out'):
    print 'Dataset translation missing'

with open(sys.argv[1]+'.counts','r') as fcounts:
    counts = [int(l.strip()) for l in fcounts.readlines()]
with open(sys.argv[1]+'1.corpus.'+str(n)+'.out','r') as fout:
    lines = [l.strip().split('|||')[1].strip() for l in fout.readlines()]
with open(sys.argv[1]+'.corpus.'+str(n)+'.out','w') as fout:
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
