import re

def normalizeWnum(x):
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

def normalizeWOnum(x):
	x = x.split(' ')
	for i in range(len(x)):
		if x[i].startswith('X'):
			x[i] = 'VAR'
		if x[i] in ['+', '-', '*', '/', '%']:
			x[i] = 'BINARY'
		if x[i] in ['++', '--']:
			x[i] = 'UNARY'
	return ' '.join(x)

def filter(c,ll,out):
    if not c:
    	return False
    if not out:
    	return False
    if len(out) == 0:
    	return False
    if normalizeWnum(c) not in map(normalizeWnum,out):
    	return False
    return normalizeWOnum(c) not in map(normalizeWOnum,out)