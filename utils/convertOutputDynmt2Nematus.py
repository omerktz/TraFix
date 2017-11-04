import sys
import re
with open(sys.argv[1],'r') as f:
	lines = f.readlines()
lines = map(lambda x: x.strip(), lines)
lines = filter(lambda x: len(x)>0, lines)
#lines = lines[lines.index('predicting...') + 1:]
#lines = filter(lambda x: not x.startswith('input:'), lines)
#lines = filter(lambda x: not x.startswith('predicted'), lines)
#lines = filter(lambda x: '/1000' not in x, lines)
lines = filter(lambda x: re.match('^[0-9]+\-best', x), lines)
with open(sys.argv[2],'w') as f:
	i = -1
	for l in lines:
			if l.startswith('0-'):
				i += 1
			f.write(str(i)+' ||| '+l[7:]+' ||| 0\n')
