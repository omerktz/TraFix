import sys
import os
import re
if not os.path.exists(sys.argv[1]+'.words'):
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
            lengths = {}
            dependencies = {}
            counter = 1
            finals = {}
            index = 0
            for inst in instructions:
            	lengths[index] = inst.count(' ')+1
            	dependencies[index] = []
                parts = inst.split(' ')
                for p in parts:
                    if re.match('%[0-9]+',p):
                        dependencies[index].append(p)
                if re.match('%[0-9]+',parts[0]):
                    temps[parts[0]] = index
                if parts[0] == 'store':
                        finals[index] = counter
                        if '%Y' in parts:
                            counter += 1
                index += 1
            relevance = {}
            for inst in range(index):
                relevance[inst] = set()
            for inst in finals.keys():
                propogateRelevance(inst, dependencies, temps, finals[inst], relevance)
            res = ''
            for inst in range(index):
                res += ' '+' '.join(map(lambda i:str(sorted(list(relevance[inst]))).replace(' ',''), range(lengths[inst])))
            fout.write(res.strip()+'\n')
