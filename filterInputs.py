import argparse

parser = argparse.ArgumentParser(description="Count inputs that match given filters")
parser.add_argument('-d', '--dataset', type=str, help="filter a dataset file", metavar="DDD", required=False)
parser.add_argument('-f', '--file', type=str, help="filter a tab seperated file", metavar="FFF", required=False)
parser.add_argument('-a', '--and', dest='a', help="inputs must match all filters", action='count')
parser.add_argument('-o', '--or', dest='o', help="inputs need only match one filter", action='count')
parser.add_argument('filters', help="list of filter files, separated by whitespace", nargs='+')
args = parser.parse_args()

if len(args.filters) > 1:
    if (1 if args.a else 0) + (1 if args.o else 0) != 1:
        parser.error('Must choose to either -o or -a in case of multiple filters (but not both)')

if (1 if args.dataset else 0) + (1 if args.file else 0) != 1:
    parser.error('Must choose to either a dataset (-d) or a file (-f) as input (but not both)')

def load_filter(f):
    if f.endswith('.py'):
        f = f[:-3]
    return __import__(f).filter

print args

filters = map(load_filter,args.filters)
(filename,cleanLine) = (args.dataset+'.corpus.c', lambda l:l.strip()) if args.dataset else (args.file,lambda l:l.strip().split('\t')[0].strip())
with open(filename,'r') as fin:
    count = 0
    total =0
    for l in fin.readlines():
        l = cleanLine(l)
        if len(l) > 0:
            total += 1
            if args.a:
                if len(filter(lambda f: not f(l),filters)) == 0:
                    count += 1
            else:
                if len(filter(lambda f: f(l), filters)) > 0:
                    count += 1
    print str(count)+'/'+str(total)+' lines matched filter(s)'

