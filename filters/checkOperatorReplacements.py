import re
import os

def normalize(x):
	x = x.split(' ')
	for i in range(len(x)):
		if x[i].startswith('X'):
			x[i] = 'VAR'
		if re.match("^[-+]?\d+$",x[i]):
			x[i] = 'NUM'
		if x[i] in ['+', '-', '*', '/', '%']:
			x[i] = 'BINARY'
		if x[i] in ['++', '--']:
			x[i] = 'UNARY'
	return ' '.join(x)

def load():
	bops = ['+', '-', '*', '/', '%']
	uops = ['++', '--']
	if os.path.exists('operatorRepalcements.tsv'):
		with open('operatorRepalcements.tsv','r') as f:
			res = {}
			l = f.readline()
			for op in bops:
				l = f.readline().strip().split('\t')[1:]
				res[op] = dict(map(lambda i:(bops[i],int(l[i])), range(len(bops))))
			l = f.readline()
			l = f.readline()
			for op in uops:
				l = f.readline().strip().split('\t')[1:]
				res[op] = dict(map(lambda i:(uops[i],int(l[i])), range(len(uops))))
			return res
	else:
		res = {}
		for o in bops:
			res[o] = dict(map(lambda b:(b,0), bops))
		for o in uops:
			res[o] = dict(map(lambda u:(u,0), uops))
		return res

def store(stats):
	bops = ['+', '-', '*', '/', '%']
	uops = ['++', '--']
	with open('operatorRepalcements.tsv','w') as f:
		f.write('orig\t'+'\t'.join(bops)+'\n')
		for op in bops:
			f.write(op+'\t'+'\t'.join(map(lambda o: str(stats[op][o]), bops))+'\n')
		f.write('\n')
		f.write('orig\t'+'\t'.join(uops)+'\n')
		for op in uops:
			f.write(op+'\t'+'\t'.join(map(lambda o: str(stats[op][o]), uops))+'\n')
		f.write('\n')

def filter(c,ll,out):
    if not c:
    	return False
    if not out:
    	return False
    if len(out) == 0:
    	return False
    out = out[0]
    if normalize(c) != normalize(out):
    	return False
    c = c.split(' ')
    out = out.split(' ')
    data = load()
    for i in range(len(c)):
    	if c[i] in ['+', '-', '*', '/', '%']:
    		if c[i] != out[i]:
    			data[c[i]][out[i]] += 1
    store(data)
    return True