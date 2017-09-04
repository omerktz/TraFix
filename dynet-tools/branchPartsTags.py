import sys
import os

if  not os.path.exists(sys.argv[1]+'.corpus.ll'):
    print 'Dataset input missing'

with open(sys.argv[1]+'.corpus.ll','r') as f:
    lines = [l for l in f.readlines()]
with open(sys.argv[1]+'.words','w') as fwords:
    with open(sys.argv[1]+'.tags','w') as ftags:
        for ll in lines:
            fwords.write(ll)
            if 'br ' not in ll:
                ftags.write(' '.join(['None' for i in range(ll.strip().count(' ')+1)])+'\n')
            else:
                ll = map(lambda x: x.strip() + ' ;', filter(lambda y: len(y) > 0, ll.strip().split(';')))
                cond_insts = []
                if_insts = []
                true_insts = []
                false_insts = []
                after_insts = []
                current = cond_insts
                for i in range(len(ll)):
                    inst = ll[i]
                    if inst.startswith('<label>:'):
                        if current is false_insts:
                            current = after_insts
                        elif current is true_insts:
                            current = false_insts
                        elif current is if_insts:
                            current = true_insts
                    elif current is cond_insts and inst.startswith('br '):
                            current = if_insts
                    current.append(inst)
                if current is false_insts:
                    after_insts = false_insts[:]
                    false_insts = []
                for x in cond_insts:
                    ftags.write(' '.join(['Cond' for i in range(x.count(' ')+1)])+' ')
                for x in if_insts:
                    ftags.write(' '.join(['If' for i in range(x.count(' ')+1)])+' ')
                for x in true_insts:
                    ftags.write(' '.join(['True' for i in range(x.count(' ')+1)])+' ')
                if len(false_insts) > 0:
                    for x in false_insts:
                        ftags.write(' '.join(['False' for i in range(x.count(' ')+1)])+' ')
                for x in after_insts:
                    ftags.write(' '.join(['After' for i in range(x.count(' ')+1)]))
                ftags.write('\n')