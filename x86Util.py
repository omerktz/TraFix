import os
import re
import ConfigParser
from compilerUtil import create_source_file

x86_config = ConfigParser.ConfigParser()
x86_config.read('configs/x86.config')
x86_separator = ' ; '

def compiler(s, check_success=False):
	src_file = create_source_file(s)
	tgt_file = 'tmp' + str(os.getpid()) + '.x86'
	os.system('gcc -m32 -S -O' + str(
		x86_config.getint('Compile', 'OptimizationLevel')) + ' -o ' + tgt_file + ' ' + src_file + ' > /dev/null 2>&1')
	if check_success:
		if not os.path.exists(tgt_file):
			return None
	with open(tgt_file, 'r') as f:
		lines = [l.strip() for l in f.readlines()]
	splitlines = []
	for l in lines:
		splitlines += l.split(' ; ')
	lines = splitlines
	start = min(filter(lambda i: lines[i].strip() == 'f:', range(len(lines))))
	lines = lines[start+2:]
	x86line = ''
	for line in lines:
		line = line.strip().replace(',', ' ,').replace('(', ' ( ').replace(')', ' ) ')
		line = re.sub('[ \t]+', ' ', line)
		if line.startswith(';'):
			line = line[1:].strip()
		if len(line) > 0:
			x86line += line + x86_separator
	os.remove(src_file)
	os.remove(tgt_file)
	return process(x86line)

def process(s):
	res = ''
	labels = {}
	lines = map(lambda x: x.strip(), s.split(';'))
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
		if x86_config.getboolean('Process', 'ReplaceLabels'):
			for label in labels.keys():
				line = re.sub('\.L'+label, '.L'+labels[label], line)
		if line.startswith('.'):
			if line.endswith(':'):
				last_label = line
			continue
		if last_label:
			res += last_label+' ; '
			last_label = None
		res += line+' ; '
	res = re.sub('[ \t]+', ' ', res)
	return res.strip()
