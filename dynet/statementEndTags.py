import sys
import os
if not os.path.exists(sys.argv[1]+'.words'):
    if os.path.exists(sys.argv[1]+'.ll'):
        os.rename(sys.argv[1]+'.corpus.ll',sys.argv[1]+'.words')
    else:
        print 'Dataset input missing'
with open(sys.argv[1]+'.words','r') as fin:
    with open(sys.argv[1]+'.tags','w') as fout:
        for l in fin.readlines():
            w = l.strip().split(' ')
            flag = 0
            res = ''
            for x in w:
                if x == ';':
                    if flag == 2:
                        res += 'END '
                    else:
                        res +='HIDDEN '
                    flag = 0
                else:
                    res += 'NONE '
                    if x == 'store':
                        flag = 1
                    else:
                        if x == '%Y':
                            if flag == 1:
                                flag == 2
            fout.write(res.strip()+'\n')
