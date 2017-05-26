def usage():
    print 'Usage: python '+sys.argv[0]+' [-d <dataset name>] [-f <tab seperated file name>] <filter script> [<additional filter scripts ...>]'
    print '\tmust provide either -d or -f but not both'
    print '\tfilter script should contain a function named filter.\n\tfilter function expects a single string argument and return a boolean'
    sys.exit(0)

import sys
if len(sys.argv) <= 3:
    usage()

if '-d' in sys.argv and '-f' in sys.argv:
    usage()
if '-d' not in sys.argv and '-f' not in sys.argv:
    usage()
if sys.argv.count('-d') > 1 or sys.argv.count('-f') > 1:
    usage()

if '-d' in sys.argv:
    flag = '-d'
    getFilename = lambda x:x+'.corpus.c'
    cleanLine = lambda l:l.strip()
if '-f' in sys.argv:
    flag = '-f'
    getFilename = lambda x:x
    cleanLine = lambda l:l.strip().split('\t')[0].strip()

def load_filter(f):
    if f.endswith('.py'):
        f = f[:-3]
    return __import__(f).filter

index = sys.argv.index(flag)
filters = map(load_filter,sys.argv[1:index]+sys.argv[index+2:])
with open(getFilename(sys.argv[index+1]),'r') as fin:
    count = 0
    for l in fin.readlines():
        l = cleanLine(l)
        if len(filter(lambda f: not f(l),filters)) == 0:
            count += 1
    print str(count)+' lines matched filter(s)'

