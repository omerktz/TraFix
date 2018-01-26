import os
import re


def translateToLLVM(s, config, settings, args=None, vocab=None, check_success=False, assignments_counter=None, var_count=None):
	separator = ' ; ' if settings.getboolean('LLVM', 'AppendSemicolon') else ' '
	with open('tmp' + str(os.getpid()) + '.c', 'w') as f:
		f.write('int ' + ('Y' if not settings.getboolean('Assignments', 'RenameTargetVars') else ','.join(
			map(lambda i: 'Y' + str(i), range(
				assignments_counter if assignments_counter else config.getint('Assigments',
																			  'MaxAssignments'))))) + ','.join(
			[''] + map(lambda i: 'X' + str(i),
					   range(var_count if var_count else config.getint('Var', 'NumVars')))) + ';\n')
		f.write('void f() {\n')
		for x in s:
			f.write(str(x) + '\n')
		f.write('}\n')
	os.system('clang -S -emit-llvm -O' + str(
		config.getint('General', 'OptimizationLevel')) + ' -o tmp' + str(os.getpid()) + '.ll tmp' + str(
		os.getpid()) + '.c > /dev/null 2>&1')
	if check_success:
		if not os.path.exists('tmp' + str(os.getpid()) + '.ll'):
			return None
	with open('tmp' + str(os.getpid()) + '.ll', 'r') as f:
		lines = [l.strip() for l in f.readlines()]
	splitlines = []
	for l in lines:
		splitlines += l.split(' ; ')
	lines = splitlines
	start = min(
		filter(lambda i: lines[i].startswith('define') and 'f()' in lines[i], range(len(lines))))
	end = min(filter(lambda i: lines[i] == '}' and i > start, range(len(lines))))
	llline = ''
	branchlabels = ('', '')
	branchIndex = -1
	for i in range(start + 1, end - 1):
		if len(lines[i].strip()) > 0:
			line = lines[i].strip().replace(',', ' ,')
			if line.startswith(';'):
				line = line[1:].strip()
			line = re.sub('[ \t]+', ' ', line)
			if settings.getboolean('Branch', 'RemovePreds'):
				if line.startswith('preds '):
					continue
			if settings.getboolean('Branch', 'SimplifyLabels'):
				if line.startswith('<label>:'):
					label = line[len('<label>:'):]
					if label == branchlabels[0]:
						line = '<label>:lTrue' + str(branchIndex)
					elif label == branchlabels[1]:
						line = '<label>:lFalse' + str(branchIndex)
					else:
						line = '<label>:lAfter' + str(branchIndex)
				elif line.startswith('br '):
					parts = line.split(',')
					if len(parts) == 3:
						branchIndex += 1
						branchlabels = (
							parts[1].strip()[len('label %'):], parts[2].strip()[len('label %'):])
						line = parts[0].strip() + ' , label %lTrue' + str(
							branchIndex) + ' , label %lFalse' + str(branchIndex)
					else:
						label = line[len('br label %'):]
						if label == branchlabels[1]:
							line = 'br label %lFalse' + str(branchIndex)
						else:
							line = 'br label %lAfter' + str(branchIndex)
			if config.getint('General', 'OptimizationLevel') > 0:
				line = line[:line.find('!')].strip()[:-1].strip()
			if settings.getboolean('LLVM', 'RemoveAlign4'):
				if line.endswith(', align 4'):
					line = line[:-len(', align 4')].strip()
			if settings.getboolean('LLVM', 'ReplaceTemps'):
				line = re.sub('%[0-9]+ ', '%tmp ', line)
			if settings.getboolean('LLVM', 'RemoveI32'):
				line = re.sub('i32\*? ', '', line)
				line = re.sub('i1 ', '', line)
			if settings.getboolean('LLVM', 'RemoveNSW'):
				line = re.sub('nsw ', '', line)
			if args and args.print_vocabs and vocab:
				vocab.update(map(lambda y: y.strip(), line.split(' ')))
			llline += line + separator
	os.remove('tmp' + str(os.getpid()) + '.c')
	os.remove('tmp' + str(os.getpid()) + '.ll')
	return llline
