import os
import re
import ConfigParser
from compilerUtil import create_source_file

llvm_config = ConfigParser.ConfigParser()
llvm_config.read('configs/llvm.config')
llvm_separator = ' ; '

def compiler(s, check_success=False):
	src_file = create_source_file(s)
	tgt_file = 'tmp' + str(os.getpid()) + '.ll'
	os.system('clang -S -emit-llvm -O' + str(
		llvm_config.getint('Compile', 'OptimizationLevel')) + ' -o '+tgt_file+' '+src_file+' > /dev/null 2>&1')
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
	os.remove(src_file)
	os.remove(tgt_file)
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
		if llvm_config.getint('Compile', 'OptimizationLevel') > 0:
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
				line = re.sub('<label>:'+label+'$', '<label>:'+labels[label], line)
				line = re.sub('label %'+label+'$', '<label>%'+labels[label], line)
		res += line+' ; '
	res = re.sub('[ \t]+', ' ', res)
	return res.strip()
