import sys
import os
import re
if not os.path.exists(sys.argv[1]+'.corpus.c') or not os.path.exists(sys.argv[1]+'.corpus.ll'):
    print 'Dataset input missing'

with open(sys.argv[1]+'.corpus.c','r') as f:
    clines = [l for l in f.readlines()]
with open(sys.argv[1]+'.corpus.ll','r') as f:
    lllines = [l for l in f.readlines()]
with open(sys.argv[1]+'.words','w') as fwords:
    with open(sys.argv[1]+'.tags','w') as ftags:
        for (c,ll) in zip(clines,lllines):
            fwords.write(ll)
            c = map(lambda x: x.strip() + ' ;', filter(lambda y: len(y) > 0, c.strip().split(';')))
            ll = map(lambda x: x.strip() + ' ;', filter(lambda y: len(y) > 0, ll.strip().split(';')))
            dependson = {}
            lastupdatedon = {}
            counter = 0
            relevance = {}
            lastCounters = {}
            for i in range(len(ll)):
                dependson[i] = set()
                parts = filter(lambda p: len(p) > 0, ll[i].split(' '))
                for j in range(1, len(parts)):
                    if parts[j][0] in ['%', '@']:
                        if parts[j] in lastupdatedon.keys():
                            dependson[i].add(lastupdatedon[parts[j]])
                if parts[0] != 'store':
                    for j in range(1,len(parts)):
                        if parts[j][0] in ['%','@']:
                            if parts[j] in lastupdatedon.keys():
                                dependson[i].add(lastupdatedon[parts[j]])
                    if parts[0][0] in ['%','@']:
                        lastupdatedon[parts[0]] = i
                else:
                    source = parts[: parts.index(',')]
                    target = parts[parts.index(',')+1:]
                    for j in range(len(source)):
                        if source[j][0] in ['%','@']:
                            if source[j] in lastupdatedon.keys():
                                dependson[i].add(lastupdatedon[source[j]])
                    for j in range(len(target)):
                        if target[j][0] in ['%','@']:
                            if target[j][1] == 'Y':
                                relevance[i] = set([counter])
                                counter += 1

                            else:
                                relevance[i] = set([counter])
                                var = target[j][1:]
                                relevance[i].update(filter(lambda k: (' ++ '+var+' ' in c[k]) or
                                                 (' '+var+' ++ ' in c[k]) or
                                                 (' -- '+var+' ' in c[k]) or
                                                 (' '+var+' -- ' in c[k]), range(lastCounters[var]+1 if var in lastCounters.keys() else 0, counter+1)))
                                lastCounters[var] = counter
            workq = set(list(relevance.keys())[:])
            while len(workq) > 0:
                i = workq.pop()
                for j in dependson[i]:
                    if j not in relevance.keys():
                        relevance[j] = set()
                    if any(map(lambda x: x not in relevance[j], relevance[i])):
                        relevance[j].update(relevance[i])
                        workq.add(j)
            for i in range(len(ll)):
                if i > 0:
                    ftags.write(' ')
                ftags.write(' '.join([str([(x+1) for x in relevance[i]]).replace(' ','') for j in range(ll[i].count(' ')+1)]))
            ftags.write('\n')


