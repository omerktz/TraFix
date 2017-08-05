import sys
import os
import itertools

n = int(sys.argv[2])

if not os.path.exists(sys.argv[1]+'.counts'):
    print 'Dataset counts missing'
if not os.path.exists(sys.argv[1]+'1.corpus.'+str(n)+'.out'):
    print 'Dataset translation missing'

def filterTranslation(tran, source):
    with open('tmp.c', 'w') as f:
        f.write('void f() {\n')
        f.write('int Y' + ','.join([''] + map(lambda i: 'X'+str(i), range(10))) + ';\n')
        f.write(tran.strip() + '\n')
        f.write('}\n')
    os.system('clang -S -emit-llvm -o tmp.ll tmp.c > /dev/null 2>&1')
    if not os.path.exists('tmp.ll'):
    	return False
    with open('tmp.ll', 'r') as f:
        lines = [l.strip() for l in f.readlines()]
    start = min(filter(lambda i: lines[i].startswith('define') and 'f()' in lines[i], range(len(lines))))
    end = min(filter(lambda i: lines[i] == '}' and i > start, range(len(lines))))
    ll = ''
    for i in range(start + 12, end - 1):
        line = lines[i].strip()
        ll += line + ';'
    ll = ll.strip().replace(' ','')
    return ll == source


def filterTranslations(trans, source):
    res = filter(lambda t: filterTranslation(t, source), trans)
    if len(res) == 0:
        res.append(';')
    return res

with open(sys.argv[1]+'.counts','r') as fcounts:
    counts = [int(l.strip()) for l in fcounts.readlines()]
with open(sys.argv[1]+'1.corpus.ll','r') as fout:
    sources = [l.strip().replace(' ','') for l in fout.readlines()]
with open(sys.argv[1]+'1.corpus.'+str(n)+'.out','r') as fout:
    lines = [l.strip().split('|||')[0:2] for l in fout.readlines()]
with open(sys.argv[1]+'.corpus.'+str(n)+'.out','w') as fout:
    i = 0;
    count = 0
    for k in counts:
        print '\r'+str(count),
        sys.stdout.flush()
        trans = []
        for j in range(k):
            current = []
            current_id = lines[i][0].strip()
            while (i < len(lines)) and (lines[i][0].strip() == current_id):
                current.append(lines[i][1].strip())
                i += 1
            trans.append(filterTranslations(current, sources[int(current_id)]))
        for p in itertools.product(*trans):
            fout.write(str(count)+' ||| '+' '.join(p).strip()+' ||| \n')
        count += 1
print ''
