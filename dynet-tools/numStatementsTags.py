import sys
import os
if not os.path.exists(sys.argv[1]+'.words'):
    print 'Dataset input missing'
with open(sys.argv[1]+'.words','r') as fin:
    with open(sys.argv[1]+'.tags','w') as fout:
        for l in fin.readlines():
            w = l.strip().split(';')
            fout.write(str(len(filter(lambda x:'store' in x and '%Y' in x, w)))+'\n')
