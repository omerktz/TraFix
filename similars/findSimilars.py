import argparse
import csv

parser = argparse.ArgumentParser(description="Count inputs that match given filters")
parser.add_argument('-d', '--dataset', dest='dataset', type=str, help="dataset to scan", required=True)
parser.add_argument('-o','--output', dest='output', type=str, help="output file name",required=True)
parser.add_argument('-r', '--reference_line', dest='r', type=int, help="number of line to use as reference", metavar='LINE', required=True)
parser.add_argument('-n', dest='n', type=int, help="number of translations per input (default: 1)", required=True)
parser.add_argument('--and', dest='a', help="inputs must match all filters", action='count')
parser.add_argument('--or', dest='o', help="inputs need only match one filter", action='count')
parser.add_argument('filters', help="list of filter files, separated by whitespace", nargs='+')
args = parser.parse_args()

if len(args.filters) > 1:
    if (1 if args.a else 0) + (1 if args.o else 0) != 1:
        parser.error('Must choose to either -o or -a in case of multiple filters (but not both)')

if not args.dataset:
    parser.error('Must provide a dataset as input')

import os

files = ['equivalent','identical','fail','parse','timeout']
if not all(map(lambda f: os.path.exists(args.dataset+'.'+f+'.'+str(args.n)+'.csv'), files)):
    parser.error('Some summary files are missing. Please run evaluateN.py before using this tool'
                 )
def load_filter(f):
    if f.endswith('.py'):
        f = f[:-3]
    if f.endswith('.pyc'):
        f = f[:-4]
    return __import__(f)

filters = map(load_filter,args.filters)

data = {}
for f in files:
    path = args.dataset+'.'+f+'.'+str(args.n)+'.csv'
    with open(path,'r') as fin:
        reader = csv.reader(fin)
        lines = list(reader)
        title = lines[0]
        lines = lines[1:]
        for l in lines:
            if len(l) > 0:
                data[int(l[0])] = l[0:3]+[f]+l[3:]

ref = data[args.r]
reference = map(lambda f: f.process(ref[1],ref[2],ref[4:]), filters)
referenceIndexes = range(len(reference))

summarize = None
if (args.a) or (len(filters) == 1):
    summarize = all
if args.o:
    summarize = any

count = 0
with open(args.output, 'w') as f:
    writer = csv.writer(f)
    writer.writerow(['Reference'])
    writer.writerow(title[0:3]+['result']+title[3:])
    writer.writerow(ref)
    writer.writerow([])
    writer.writerow(['Similars'])
    writer.writerow(title[0:3]+['result']+title[3:])
    for k in sorted(data.keys()):
        if k != args.r:
            l = data[k]
            summary = map(lambda f: f.process(l[1],l[2],l[4:]), filters)
            if summarize(map(lambda i: filters[i].compare(reference[i], summary[i]), referenceIndexes)):
                count += 1
                writer.writerow(l)

print 'Found '+str(count)+'/'+str(len(data.keys())-1)+' similar samples'

