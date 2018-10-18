import os
import re
import ConfigParser
from compilerUtil import create_source_file
import angr
import cle

vex_config = ConfigParser.ConfigParser()
vex_config.read('configs/vex.config')
vex_separator = ' ; '


def compiler(s, check_success=False):
	src_file = create_source_file(s)
	tgt_file = 'tmp' + str(os.getpid())
	os.system('gcc -m32 -O' + str(
		vex_config.getint('Compile', 'OptimizationLevel')) + ' -o ' + tgt_file + ' ' + src_file + ' > /dev/null 2>&1')
	if check_success:
		if not os.path.exists(tgt_file):
			return None
	binary = angr.Project(tgt_file, load_options={'auto_load_libs': False})
	loader = binary.loader
	cfg = binary.analyses.CFGFast()
	addr = filter(lambda a: cfg.functions[a].name == 'main', cfg.functions.keys())[0]
	func = cfg.functions[addr]
	vexlines = {}
	for b in func.blocks:
		lines = map(lambda s: s.strip(), str(b.vex).split('\n')[3:-1])
		lines = map(lambda l: l[l.find('|')+1:].strip() if '|' in l else l[5:l.find(';')].strip(), lines)
		addr = None
		for l in lines:
			if l.startswith('------ IMark('):
				addr = int(l[len('------ IMark('):l.find(',')],16)
				if addr in vexlines.keys():
					break
				vexlines[addr] = ['0x'+hex(addr)[2:].zfill(8)+' :']
			else:
				vexlines[addr] += [l.replace(',', ' , ').replace('(', ' ( ').replace(')', ' ) ').replace('{', ' { ').replace('}', ' } ')]
	os.remove(src_file)
	os.remove(tgt_file)
	lines = []
	for a in sorted(vexlines.keys()):
		lines += vexlines[a]
	return process(lines, loader)

def process(lines, loader):
	res = ''
	labels = {}
	globals = {}
	for line in lines:
		if re.match('0x[0-9a-fA-F]+ :', line):
			num = line[:-2]
			if ' ' in num:
				num = num[:num.find(' ')]
			labels[num] = str(len(labels.keys()))
		else:
			for x in re.findall('\( 0x[0-9a-fA-F]+ \)', line):
				symbol = loader.find_symbol(int(x[2:-2], 16))
				if symbol:
					globals[x[2:-2]] = symbol.name
	for line in lines:
		line = line.strip()
		if len(line) == 0:
			continue
		if line.startswith('if '):
			line = line[:line.find(';')]+'}'
		if vex_config.getboolean('Process', 'ReplaceLabels'):
			for label in labels.keys():
				line = re.sub(label, 'L'+labels[label], line)
				line = re.sub(hex(int(label,16)), 'L' + labels[label], line)
		if vex_config.getboolean('Process', 'RemoveI32'):
			line = re.sub(':I32', '', line)
		if vex_config.getboolean('Process', 'ReplaceGlobals'):
			for g in globals.keys():
				line = re.sub('\( '+g+' \)', '( '+globals[g]+' )', line)
		if vex_config.getboolean('Process', 'NormalizeNumbers'):
			for num in re.findall('0x[0-9a-fA-F]+',line):
				line = re.sub(num, str(int(num,16)), line)
		res += line+' ; '
	res = re.sub('[ \t]+', ' ', res)
	return res.strip()
