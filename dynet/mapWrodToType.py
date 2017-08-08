import re

import enum
Types = enum.Enum('Types', 'Var TmpVar Num Op Assign Other')

def getType(w):
	if w == '=':
		return Types.Assign
	if w.startswith('%'):
		if re.match('%[0-9]+$',w):
			return Types.TmpVar
		return Types.Var
	if re.match('^\-?[0-9]+$',w):
		return Types.Num
	if w in ['add','sub','load','store','sdiv','mul','srem']:
		return Types.Op
	return Types.Other

if __name__ == "__main__":
	import sys
	import csv
	with open(sys.argv[1],'r') as f:
		reader = csv.reader(f)
		lines = list(reader)[1:]
		for l in lines:
			w = l[0]
			t = getType(w)
			print w, t.name