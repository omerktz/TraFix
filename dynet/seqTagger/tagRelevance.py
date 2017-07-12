import sys
import os
import re
if not os.path.exists(sys.argv[1]+'.words'):
    if os.path.exists(sys.argv[1]+'.ll'):
        os.rename(sys.argv[1]+'.corpus.ll',sys.argv[1]+'.words')
    else:
        print 'Dataset input missing'
def propogateRelevance(inst, dependencies, temps, i, relevance):
    if i in relevance[inst]:
        return
    relevance[inst].add(i)
    for x in dependencies[inst]:
        propogateRelevance(temps[x], dependencies, temps, i, relevance)

with open(sys.argv[1]+'.words','r') as fin:
    with open(sys.argv[1]+'.tags','w') as fout:
        for l in fin.readlines():
            instructions = map(lambda x: x.strip() +' ;', filter(lambda y: len(y.strip())>0, l.split(';')))
            temps = {}
            dependencies = {}
            counter = 0
            finals = {}
            for inst in instructions:
                dependencies[inst] = []
                parts = inst.split(' ')
                for p in parts:
                    if re.match('%[0-9]+',p):
                        dependencies[inst].append(p)
                if re.match('%[0-9]+',parts[0]):
                    temps[parts[0]] = inst
                if parts[0] == 'store':
                        finals[inst] = counter
                        if '%Y' in parts:
                            counter += 1
            relevance = {}
            for inst in instructions:
                relevance[inst] = set()
            for inst in finals.keys():
                propogateRelevance(inst, dependencies, temps, finals[inst], relevance)
            res = ''
            for inst in instructions:
                res += ' '+' '.join(map(lambda i:str(sorted(list(relevance[inst]))).replace(' ',''), range(inst.count(' ')+1)))
            fout.write(res.strip()+'\n')
