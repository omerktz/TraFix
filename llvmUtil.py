"""
This compiler interface was implemented for Calng version 3.8.0.
The cleanup stage (part of the process method) might not work properly for other versions of Clang.
"""

import os
import re
import ConfigParser
from compilerUtil import create_source_file
from regex import match

llvm_config = ConfigParser.ConfigParser()
llvm_config.read('configs/llvm.config')
llvm_separator = ' ; '

def compiler(s, check_success=False):
	src_file = create_source_file(s)
	tgt_file = 'tmp' + str(os.getpid()) + '.ll'
	optimization_level = ' -O0' if llvm_config.getboolean('Compile', 'Optimized') else ''
	os.system('clang -S -emit-llvm' + optimization_level + ' -o '+tgt_file+' '+src_file+' > /dev/null 2>&1')
	if check_success:
		if not os.path.exists(tgt_file):
			return None
	with open(tgt_file, 'r') as f:
		lines = [l.strip() for l in f.readlines()]
	splitlines = []
	for l in lines:
		splitlines += l.split(' ; ')
	lines = splitlines
	start = min(filter(lambda i: lines[i].startswith('define') and 'main()' in lines[i], range(len(lines))))
	lines = lines[start+1:]
	end = min(filter(lambda i: lines[i] == '}', range(len(lines))))
	lines = lines[:end-1]
	lllines = []
	for line in lines:
		line = line.strip().replace(',', ' ,')
		line = re.sub('[ \t]+', ' ', line)
		if line.startswith(';'):
			line = line[1:].strip()
		if len(line) > 0:
			lllines += [line.strip()]
	try:
		os.remove(src_file)
		os.remove(tgt_file)
	except OSError:
		pass
	return process(lllines)

def process(lines):
	res = ''
	labels = {}
	for line in lines:
		if line.startswith('<label>:'):
			num = line[8:]
			if ' ' in num:
				num = num[:num.find(' ')]
			labels[num] = str(len(labels.keys()))
	for line in lines:
		line = line.strip()
		if len(line) == 0:
			continue
		if llvm_config.getboolean('Process', 'RemovePreds'):
			if line.startswith('preds '):
				continue
		if llvm_config.getboolean('Compile', 'Optimized'):
			if '!' in line:
				line = line[:line.find('!')].strip()[:-1].strip()
		if llvm_config.getboolean('Process', 'RemoveAlign4'):
			line = re.sub(', align 4', ' ', line)
		if llvm_config.getboolean('Process', 'RemoveI32'):
			line = re.sub('i32\*? ', '', line)
			line = re.sub('i1 ', '', line)
		if llvm_config.getboolean('Process', 'RemoveNSW'):
			line = re.sub('nsw ', '', line)
		if llvm_config.getboolean('Process', 'ReplaceLabels'):
			for label in labels.keys():
				line = re.sub('<label>:'+label+'$', '<label>'+labels[label]+' :', line)
				line = re.sub('label %'+label+'$', '<label>'+labels[label], line)
				line = re.sub('label %'+label+' ', '<label>'+labels[label]+' ', line)
		res += line+' ; '
	res = re.sub('[ \t]+', ' ', res)
	return res.strip()

def is_number(n):
	return match("^[0-9]+$", n)

def get_number(n):
	return n

equivalent_ops = []

class Instruction:
	def __init__(self, code, i):
		self.code = code
		self.op = ''
		self.is_jump = False
		self.is_label = False
		self.targets = []
		self.defines = []
		self.is_branch = False
		self.is_condition = False
		self.uses = []
		self.is_symmetric = False
		self.labels = []
		can_be_reduced = False
		self.parse_instruction(code, i)

	def parse_instruction(self, code, i):
		if code in ['__entry__', '__exit__']:
			self.op = code
			return
		if re.match('^<label>[0-9]+ :$', code):
			self.is_label = True
			self.labels.append(code)
			return
		if code.startswith('br '):
			self.is_jump = True
			self.op = 'br'
			code = code[3:]
			if ',' in self.code:
				self.is_branch = True
				parts = map(lambda x: x.strip(), code.split(','))
				labels = parts[1:]
				self.uses.append(parts[0])
			else:
				labels = [code]
			self.targets = ['<label>'+x[7:]+' :' for x in labels]
		elif code.startswith('store'):
			code = code[6:]
			parts = map(lambda x: x.strip(), code.split(','))
			self.op = 'store'
			self.defines = [parts[1][1:]]
			self.uses.append(parts[0])
		elif ' = ' in self.code:
			self.defines = [self.code.split(' = ')[0].strip()]
			code = code[code.index('=')+1:].strip()
			self.op = code[:code.index(' ')]
			if code.startswith('load'):
				self.uses.append(code.split(',')[1].strip()[1:])
			else:
				code = code[len(self.op)+1:].strip()
				if self.op == 'icmp':
					self.is_condition = True
					self.relation = code[:code.index(' ')]
					code = code[len(self.relation)+1:].strip()
				self.uses += map(lambda x: x.strip(), code.split(','))
				# normalize conditions
				if self.is_condition:
					if self.relation in ['sgt', 'sge']:
						self.relation = 'sl' + self.relation[2]
						self.uses.reverse()
				if self.op in ['add', 'mul'] or (self.is_condition and self.relation in ['eq', 'ne']):
					self.is_symmetric = True
