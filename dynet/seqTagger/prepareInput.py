import sys
import os
os.rename(sys.argv[1]+'.corpus.ll',sys.argv[1]+'.words')
with open(sys.argv[1]+'.words','r') as fin:
    with open(sys.argv[1]+'.tags','w') as fout:
        for l in fin.readlines():
            w = l.strip().split(' ')
            flag = False
            res = ''
            for x in w:
                if x == ';':
                    if flag:
                        res += 'END '
                        flag = False
                    else:
                        res +='HIDDEN '
                else:
                    res += 'NONE '
                    if x.lower() == 'store':
                        flag = True
            fout.write(res.strip()+'\n')
