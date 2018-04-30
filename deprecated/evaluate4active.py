import sys
import os
import subprocess
# import parmap
import time
import itertools
import csv
import ConfigParser
import postOrderUtil as po2c
import llvmUtil as c2llvm


def runCbmc(timeout):
	with open(os.devnull, 'w') as fnull:
		s = subprocess.Popen(['cbmc', 'cbmc' + str(os.getpid()) + '.c'], stdout=fnull, stderr=subprocess.STDOUT)
		poll_period = 0
		s.poll()
		while s.returncode is None and timeout > 0:
			time.sleep(poll_period)
			timeout -= poll_period
			poll_period = min(timeout, poll_period + 1)
			s.poll()
		if timeout > 0:
			if s.returncode == 0:
				return 0  # equivalent
			if s.returncode == 6:
				return 1  # parse
			return 2  # fail
		else:
			s.kill()
			return 3  # timeout


varCount = 10


def compareProgs((c, out)):
	with open('cbmc' + str(os.getpid()) + '.c', 'w') as fcbmc:
		c = filter(lambda x: len(x) > 0, c.strip().split(' '))
		yi_c = 0
		for i in range(len(c)):
			if c[i][0] not in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '-', '*', '/', '%', '(', ')', '=',
							   ';']:
				if c[i] == 'Y':
					c[i] = c[i] + '_' + str(yi_c) + '_0'
					yi_c += 1
				else:
					c[i] = c[i] + '_0'
		c = ' '.join(c)
		out = filter(lambda x: len(x) > 0, out.strip().split(' '))
		yi_out = 0
		for i in range(len(out)):
			if out[i][0] not in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '-', '*', '/', '%', '(', ')',
								 '=', ';']:
				if out[i] == 'Y':
					out[i] = out[i] + '_' + str(yi_out) + '_1'
					yi_out += 1
				else:
					out[i] = out[i] + '_1'
		out = ' '.join(out)
		if yi_c != yi_out:
			return 2  # fail
		fcbmc.write('void main() {\n')
		fcbmc.write('\tint ' + ','.join(map(lambda i: 'Y_' + str(i) + '_0,Y_' + str(i) + '_1', range(yi_c))))
		for i in range(varCount):
			fcbmc.write(',X' + str(i) + '_0,X' + str(i) + '_1')
		fcbmc.write(';\n')
		for i in range(varCount):
			fcbmc.write('\t__CPROVER_assume(X' + str(i) + '_0==X' + str(i) + '_1);\n')
		fcbmc.write('\t' + c + '\n')
		fcbmc.write('\t' + out + '\n')
		for i in range(yi_c):
			fcbmc.write(
				'\t__CPROVER_assert(Y_' + str(i) + '_0==Y_' + str(i) + '_1,"computations not equivalent (' + str(
					i) + ')");\n')
		fcbmc.write('}')
	ret = runCbmc(60)
	os.remove('cbmc' + str(os.getpid()) + '.c')
	return ret


def convertPostOrderToC(po):
	return po2c.parse(po)


def convertCToLLVM(c, config):
	s = [y + ';' for y in filter(lambda x: len(x) > 0, c.split(';'))]
	return c2llvm.compiler(s, config, check_success=True,
						   assignments_counter=sum([str(x).count(' = ') for x in c]))


def evaluateProg(i, p, expected, c, po, ll, out, postOrder, convert, llvm, cbmc, config):
	# print '\r' + p,
	sys.stdout.flush()
	if len(filter(lambda x: len(x) > 0, out)) == 0:
		return (i, c, po, ll, out, 3)  # fail
	else:
		if postOrder:
			if not convert:
				if expected in out:
					return (i, c, po, ll, [expected], 0)  # identical
			# res = parmap.map(convertPostOrderToC, out)
			res = map(convertPostOrderToC, out)
			if all(map(lambda x: not x[0], res)):
				return (i, c, po, ll, [], 2)  # parse
			else:
				if convert:
					out = map(lambda x: x[1].c().strip(), filter(lambda y: y[0], res))
				else:
					return (i, c, po, ll, [], 3)  # fail
		# compare c code
		config = ConfigParser.ConfigParser()
		config.read(args.config)
		if expected in out:
			return (i, c, po, ll, [expected], 0)  # identical
		res = map(lambda x: convertCToLLVM(x, config).strip(), out)
		if not any(res):
			return (i, c, po, ll, [], 2)  # parse
		if llvm:
			if ll in res:
				return (i, c, po, ll, [expected], 0)  # identical
		if cbmc:
			# res = parmap.map(compareProgs, map(lambda x: (c, x), out))
			res = map(compareProgs, map(lambda x: (expected, x), out))
			if 0 in res:
				return (i, c, po, ll, map(lambda j: out[j], filter(lambda i: res[i] == 0, range(len(res)))), 1)  # equivalent
			else:
				if 2 in res:
					return (i, c, po, ll, [], 3)  # fail
				else:
					if 1 in res:
						return (i, c, po, ll, [], 2)  # parse
					else:
						return (i, c, po, ll, [], 4)  # timeout
		return (i, c, po, ll, [], 3)  # fail


def evaluate(k, fin, fc, fpo, fll, fout, postOrder, convert, llvm, cbmc, force, config, fs=None, ff=None):
	nsuccess = 0
	nfail = 0
	ins = [l.strip() for l in fin.readlines()]
	cs = [l.strip() for l in fc.readlines()]
	pos = [l.strip() for l in fpo.readlines()]
	lls = [l.strip() for l in fll.readlines()]
	outs = [map(lambda x: x.strip(), l.strip().split('|||')[0:2]) for l in fout.readlines()]
	groups = {}
	for (n, g) in itertools.groupby(outs, lambda x: x[0]):
		groups[int(n)] = [x[1] for x in g]
	max_len = max(len(ins), len(lls), len(groups.keys()))
	ins = ins + [''] * (max_len - len(ins))
	lls = lls + [''] * (max_len - len(lls))
	for i in filter(lambda x: x not in groups.keys(), range(max_len)):
		groups[i] = []
	results = map(
		lambda i: evaluateProg(i, str(i + 1).zfill(len(str(max_len))) + '/' + str(max_len), ins[i], cs[i], pos[i],
							   lls[i], groups[i], postOrder, convert, llvm, cbmc, config), range(len(ins)))
	# print ''
	for x in results:
		if x[5] in [0, 1]:
			if fs:
				fs.writerow([str(x[0]), x[1], x[2], x[3]] + x[4])
			nsuccess += 1
		else:
			if ff:
				ff.writerow([str(x[0]), x[1], x[2], x[3]] + x[4])
			nfail += 1
	if force:
		if cbmc:
			for f in os.listdir('.'):
				if f.startswith('cbmc') and f.endswith('.c'):
					os.remove(f)
		if llvm:
			for f in os.listdir('.'):
				if f.startswith('tmp') and (f.endswith('.c') or f.endswith('ll')):
					os.remove(f)
	return (nsuccess, nfail)


def main(f, k, ext, postOrder, convert, llvm, cbmc, force, config):
	with open(f + '.success.' + str(k) + '.csv', 'w') as fsuccess:
		with open(f + '.fail.' + str(k) + '.csv', 'w') as ffail:
			csv.writer(fsuccess).writerow(['line', 'c', 'po', 'll'] + map(lambda i: 'out' + str(i), range(k)))
			csv.writer(ffail).writerow(['line', 'c', 'po', 'll'] + map(lambda i: 'out' + str(i), range(k)))
			with open(f + '.corpus.c', 'r') as fc:
				with open(f + '.corpus.' + ext, 'r') as fin:
					with open(f + '.corpus.po', 'r') as fpo:
						with open(f + '.corpus.ll', 'r') as fll:
							with open(f + '.corpus.' + str(k) + '.out', 'r') as fout:
								(nsuccess, nfail) = evaluate(k, fin, fc, fpo, fll, fout, postOrder, convert, llvm, cbmc,
															 force, config, fs=csv.writer(fsuccess), ff=csv.writer(ffail))
	print str(nsuccess) + ' statements translated successfully'
	print str(nfail) + ' statements failed to translate'


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Evaluate dataset translations")
	parser.add_argument('dataset', type=str, help="dataset to translate")
	parser.add_argument('num_translations', type=int, help="number of translations in output for each input")
	post_order = parser.add_argument('-po', '--post-order', dest='po', help="use translations to post order code",
									 action='count')
	convert = parser.add_argument('--convert', dest='convert', help="convert post order to c", action='count')


	class ForceConvert(argparse._CountAction):
		def __call__(self, parser, namespace, values, option_string=None):
			if getattr(namespace, post_order.dest, False):
				setattr(namespace, convert.dest, 1)
			argparse._CountAction.__call__(self, parser, namespace, values, option_string)


	parser.add_argument('--llvm', dest='llvm', help="compile c to llvm", action=ForceConvert)
	parser.add_argument('--cbmc', dest='cbmc', help="use cbmc to compare c", action=ForceConvert)
	parser.add_argument('-f', '--force-cleanup', dest='force', help="force delete all tmp files when finished",
						action='count')
	parser.add_argument('-c', '--config', dest='config', type=str, default='configs/codenator.config',
						help="configuration file used for llvm compilation (default: \'%(default)s\')")
	args = parser.parse_args()

	main(args.dataset, args.num_translations, 'po' if (args.po and not args.convert) else 'c', args.po, args.convert,
		 args.llvm, args.cbmc, args.force, args.config)
	if args.force:
		if args.cbmc:
			for f in os.listdir('.'):
				if f.startswith('cbmc') and f.endswith('.c'):
					os.remove(f)
		if args.llvm:
			for f in os.listdir('.'):
				if f.startswith('tmp') and (f.endswith('.c') or f.endswith('ll')):
					os.remove(f)
