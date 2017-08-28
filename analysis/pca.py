from sklearn import decomposition
import argparse
import os
import sys
import csv

import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import matplotlib.patches as mpatches
from matplotlib import colors as mcolors

sys.path.insert(0,'..')
from utils.mapWrodToType import *

parser = argparse.ArgumentParser(description="Test embedding classification (using leave-one-out method)")
parser.add_argument('input', type=str, help="embeddings file to use as input")
parser.add_argument('-es', '--embedding-size', dest='s', type=int, default=512, help="size of embedding vector (default: %(default)s)")
parser.add_argument('-fs', '--final-size', dest='f', type=int, default=2, help="vector size after PCA (default: %(default)s)")
parser.add_argument('--screen', help="print reduced vectors to screen", action='count')
parser.add_argument('--plot', help="plot reduced vectors", action='count')
parser.add_argument('--file', help="write reduced vectors to file (default: %(const)s)", nargs='?', type=str, const='pca.csv')
args = parser.parse_args()

if not os.path.exists(args.input):
    parser.error('embeddings input file doesn\'t exist')
if args.f < 1 or args.s <1:
    parser.error('vector sizes must be at least one')
if not (args.screen or args.plot or args.file):
    parser.error('you need to choose at least one output option')

with open(args.input,'r') as f:
    lines = filter(lambda l: len(l)>0, list(csv.reader(f))[1:])

embeddings = map(lambda l: map(lambda x: float(x),l[-args.s:]), lines)
words = sorted(map(lambda l: l[0], lines))
words = sorted(words, key=lambda w: getType(w).value, reverse=True)
types = map(lambda w: getType(w), words)

pca = decomposition.PCA(args.f).fit(embeddings).transform(embeddings)

if args.file:
    with open(args.file,'w') as f:
        csvf = csv.writer(f)
        csvf.writerow(['Word','Type','Raw','','Parsed'])
        for i in range(len(words)):
            csvf.writerow([words[i],types[i].name,str(pca[i]),'']+list(pca[i]))

if args.plot:
    if args.f > 3:
        print 'Plotting is only supported for final vector size at most 3. Skipping plot\n'
    else:
        if len(set(types)) < len(mcolors.BASE_COLORS):
            mcolors = mcolors.BASE_COLORS
            avoid = ['w']
        else:
            mcolors = mcolors.CSS4_COLORS
            avoid = ['white']
        mcolors = sorted(map(lambda y: mcolors[y], filter(lambda x: x not in avoid, mcolors.keys())))
        stride = max(1,len(mcolors)/len(Types))
        colorsMap = {}
        def mapColorToType(t):
            if t.value not in colorsMap.keys():
                colorsMap[t.value] = mcolors[len(colorsMap.keys())*stride]
            return colorsMap[t.value]
        colors = map(mapColorToType, types)
        if args.f == 1:
            p = plt.scatter(pca, [0 for i in range(len(pca))], c=colors)
        if args.f == 2:
            p = plt.scatter(pca[:,0],pca[:,1],c=colors)
        if args.f == 3:
            p = Axes3D(plt.figure()).scatter(pca[:,0],pca[:,1],pca[:,2],c=colors)
        plt.legend(handles=map(lambda t: mpatches.Patch(color=mapColorToType(t), label=t.name), set(types)))
        plt.show()

    if args.screen:
        for i in range(len(words)):
            print  words[i], '\t', types[i].name, '\t', pca[i]
