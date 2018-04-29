import os
def create_source_file(s):
	with open('tmp' + str(os.getpid()) + '.c', 'w') as f:
		f.write('int ' + ','.join(s.collect_vars()) + ','.join([''] + list(s.collect_nums())) + ';\n')
		f.write('void f() {\n')
		f.write(str(s) + '\n')
		f.write('}\n')
	return 'tmp' + str(os.getpid()) + '.c'