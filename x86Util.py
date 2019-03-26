import os
import re
import ConfigParser
from compilerUtil import create_source_file
from regex import match

x86_config = ConfigParser.ConfigParser()
x86_config.read('configs/x86.config')
x86_separator = ' ; '

def compiler(s, check_success=False):
	if x86_config.getboolean('Compile', 'Optimized'):
		src_file = create_source_file(s, '')
		optimization = ''
	else:
		src_file = create_source_file(s, '#pragma GCC optimize ("O0")\n')
		optimization = ' -Os'
	tgt_file = 'tmp' + str(os.getpid()) + '.x86'
	os.system('gcc -m32 -S' + optimization + ' -o ' + tgt_file + ' ' + src_file + ' > /dev/null 2>&1')
	if check_success:
		if not os.path.exists(tgt_file):
			return None
	with open(tgt_file, 'r') as f:
		lines = [l.strip() for l in f.readlines()]
	splitlines = []
	for l in lines:
		splitlines += l.split(' ; ')
	lines = splitlines
	start = min(filter(lambda i: lines[i].strip() == 'main:', range(len(lines))))
	lines = lines[start+2:]
	x86lines = []
	for line in lines:
		line = line.strip().replace(',', ' , ').replace('(', ' ( ').replace(')', ' ) ')
		line = re.sub('[ \t]+', ' ', line)
		if line.startswith(';'):
			line = line[1:].strip()
		if len(line) > 0:
			x86lines += [line.strip()]
	try:
		os.remove(src_file)
		os.remove(tgt_file)
	except OSError:
		pass
	return process(x86lines)

def process(lines):
	remaining_lines = []
	labels = {}
	for line in lines:
		if re.match('\.L[0-9]+:', line):
			num = line[2:-1]
			if ' ' in num:
				num = num[:num.find(' ')]
			labels[num] = str(len(labels.keys()))
	last_label = None
	for line in lines:
		line = line.strip()
		if len(line) == 0:
			continue
		if line == 'nop':
			continue
		if x86_config.getboolean('Process', 'RemoveCLTD'):
			if line == 'cltd':
				continue
		if x86_config.getboolean('Process', 'ReplaceLabels'):
			for label in labels.keys():
				line = re.sub('\.L'+label, '.L'+labels[label], line)
		if re.match("^s[ha][rl]l %e.x$", line):
			line = line[:5]+'1 , '+line[5:]
		line = re.sub(':', ' :', line)
		line = ' '.join(map(lambda x: x[1:] if match('^\$\-?[0-9]+$', x) else x, line.split(' ')))
		if line.startswith('.'):
			if line.endswith(':'):
				last_label = line
			continue
		if last_label:
			remaining_lines.append(last_label)
			last_label = None
		remaining_lines.append(line)
	remaining_lines = remaining_lines[2:-2]
	while (len(remaining_lines) > 0) and (remaining_lines[0].startswith('pushl %e')):
		remaining_lines = remaining_lines[1:]
	while (len(remaining_lines) > 0) and (remaining_lines[-1].startswith('popl %e')):
		remaining_lines = remaining_lines[:-1]
	res = re.sub('[ \t]+', ' ', ' ; '.join(remaining_lines+['']))
	return res.strip()

def is_number(n):
	return match("^[0-9]+$", n)

def get_number(n):
	return n

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
		self.labels = [i]
		self.parse_instruction(code, i)

	def parse_instruction(self, code, i):
		if code in ['__entry__', '__exit__']:
			self.op = code
			return
		if re.match('^\.L[0-9]+ :$', code):
			self.is_label = True
			self.labels.append(code)
			return
		self.op = code[:code.index(' ')].strip()
		code = code[len(self.op):].strip()
		if self.op in ['jmp', 'je', 'jz', 'jne', 'jnz', 'jg', 'jnle', 'jge', 'jnl', 'jl', 'jnge', 'jle', 'jng', 'ja', 'jnbe', 'jae', 'jnb', 'jb', 'jnae', 'jbe', 'jna', 'jcxz', 'jc', 'jnc', 'jo', 'jno', 'jp', 'jpe', 'jnp', 'jpo', 'js', 'jns']:
			self.is_jump = True
			self.targets = [code + ' :']
			if self.op != 'jmp':
				self.is_branch = True
				self.uses.append('FLAGS')
				self.targets.append(i+1)
				self.is_condition = True
				self.relation = self.op[1:]
		elif self.op in ['cmpl', 'testl']:
			self.uses = map(lambda x: x.strip(), code.split(','))
			self.defines = ['FLAGS']
		elif self.op == 'movl':
			parts = map(lambda x: x.strip(), code.split(','))
			self.uses = [parts[0]]
			self.defines = [parts[1]]
		elif self.op in ['cmova', 'cmovae', 'cmovb', 'cmovbe', 'cmovc', 'cmove', 'cmovg', 'cmovge', 'cmovl', 'cmovle', 'cmovna', 'cmovnae', 'cmovnb', 'cmovnbe', 'cmovnc', 'cmovne', 'cmovng', 'cmovnge', 'cmovnl', 'cmovnle', 'cmovno', 'cmovnp', 'cmovns', 'cmovnz', 'cmovo', 'cmovp', 'cmovpe', 'cmovpo', 'cmovs', 'cmovz']:
			parts = map(lambda x: x.strip(), code.split(','))
			self.uses = [parts[0]] + ['FLAGS']
			self.defines = [parts[1]]
		elif self.op in ['addl', 'subl', 'adcl', 'sbbl']:
			self.uses = map(lambda x: x.strip(), code.split(','))
			if self.op in ['adcl', 'sbbl']:
				self.uses += ['FLAGS']
			self.defines = [self.uses[1]] + ['FLAGS']
			if re.match('^\-[0-9]+$', self.uses[0]):
				self.uses = [self.uses[1], self.uses[0][1:]]
				self.op = 'addl' if self.op == 'subl' else 'subl'
			self.is_symmetric = self.op in ['addl', 'adcl']
		elif self.op in ['andl', 'orl', 'xorl']:
			self.uses = map(lambda x: x.strip(), code.split(','))
			self.defines = [self.uses[1]] + ['FLAGS']
		elif self.op in ['inc', 'dec']:
			self.uses = [code, '1']
			self.defines = [code] + ['FLAGS']
			self.op = 'addl' if self.op == 'inc' else 'subl'
			self.is_symmetric = self.op == 'addl'
		elif self.op == 'imull':
			parts = map(lambda x: x.strip(), code.split(','))
			parts = map(lambda n: n[1:] if re.match('^\$\-?[0-9]+$', n) else n, parts)
			if len(parts) == 1:
				self.uses = [code, '%eax']
				self.defines = ['%eax', '%edx']
			elif len(parts) == 2:
				self.uses = parts
				self.defines = [parts[1]]
			elif len(parts) ==3:
				self.uses = parts[0:2]
				self.defines = [parts[2]]
			else:
				import sys
				print 'Invalid asm instruction: '+self.op+' '+code
				sys.exit(1)
			self.defines += ['FLAGS']
			self.is_symmetric = True
		elif self.op == 'idivl':
			self.uses = [code, '%eax', '%edx']
			self.defines = ['%eax', '%edx', 'FLAGS']
		elif self.op in ['negl', 'notl']:
			self.uses = [code]
			self.defines = [code, 'FLAGS']
		elif self.op in ['sall', 'sarl', 'shll', 'shrl']:
			parts = map(lambda x: x.strip(), code.split(','))
			parts = map(lambda n: n[1:] if re.match('^\$\-?[0-9]+$', n) else n, parts)
			if len(parts) == 1:
				parts = ['1'] + parts
			self.uses = parts[:]
			self.defines = [parts[1]] + ['FLAGS']
		elif self.op == 'leal':
			parts = filter(lambda y:len(y) > 0, map(lambda x: x.strip(), re.sub('  ', ' ', re.sub('[\(\)]', '', code)).split(',')))
			self.defines = [parts[-1]]
			self.uses = parts[:-1]
			self.uses.reverse()
		else:
			print 'Unknown op: ' + self.code
			# import sys
			# sys.exit(2)