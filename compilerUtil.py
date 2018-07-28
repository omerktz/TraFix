import os
def create_source_file(s, func_prefix = ''):
	with open('tmp' + str(os.getpid()) + '.c', 'w') as f:
		f.write('int ' + ','.join(s.collect_vars()) + ';\n')
		f.write(func_prefix)
		f.write('void main() {\n')
		f.write(str(s) + '\n')
		f.write('}\n')
	return 'tmp' + str(os.getpid()) + '.c'