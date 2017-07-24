import sys
import os
import shutil
import ast
max_tag = max(map(lambda z: int(z), filter(lambda y: len(y) > 0, map(lambda x: x[len(sys.argv[1]):-len('.out')], filter(lambda f: f.endswith('.out') and f.startswith(sys.argv[1]), os.listdir('.'))))))
tags = {}
for i in range(1, max_tag+1):
    with open(sys.argv[1] + str(i) + '.out', 'r') as fin:
        lines = [l.strip().split(' ') for l in fin.readlines()]
    tags[i] = map(lambda l: map(lambda x: x == str(True), l), lines)
with open(sys.argv[1] + '.out', 'w') as fout:
    first_tags = tags[min(tags.keys())]
    for i in range(len(first_tags)):
        inner_res = ''
        for j in range(len(first_tags[i])):
            inner_res += str(filter(lambda k: tags[k][i][j], tags.keys())) + ' '
        fout.write(inner_res.strip() + '\n')

