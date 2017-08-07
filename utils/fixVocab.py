import sys
vocab = {}
with open(sys.argv[1],'r') as f:
    for l in f.readlines():
        if l.startswith('  '):
            l = l.split(': ')
            l[1] = l[1].strip()
            if l[1].endswith(','):
                l[1] = l[1][:-1]
            vocab[int(l[1])+2] = l[0]
with open(sys.argv[1],'w') as f:
    f.write('{\n')
    f.write('  "eos": 0, \n')
    f.write('  "UNK": 1, \n')
    i = 0
    for k in vocab.keys():
        f.write(vocab[k]+': '+str(k))
        i += 1
        if i != len(vocab.keys()):
            f.write(', ')
        f.write('\n')
    f.write('}')
