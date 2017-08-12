import re
import csv

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

def filter(c,ll,out):
    if not c:
    	return False
    if not out:
    	return False
    if len(out) == 0:
    	return False
    if normalize(c) in map(normalize,out):
    	return True
    with open('structurallyDifferent.csv','a') as f:
		csv.writer(f).writerow([c,ll]+out)
    return False