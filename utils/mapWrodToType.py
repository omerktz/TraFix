import re

import enum
Types = enum.Enum('Types', 'Assign Model Op Var Global Tmp Other Num')

def getType(w):
	if w in ['eos', 'UNK']:
		return Types.Model
	if w == '=':
		return Types.Assign
	if w.startswith('%'):
		if re.match('%[0-9]+$',w):
			return Types.Tmp
		return Types.Var
	if w.startswith('@'):
		return Types.Global
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