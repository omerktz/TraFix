import sys
import os
import subprocess
#import parmap
import time
import itertools
import csv
import utils.convertPostOrderToC as po2c


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
					c[i] = c[i] + '_' + str(yi_c) + '_1'
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


def evaluateProg(i, p, c, ll, out, postOrder, convert):
	#print '\r' + p,
	sys.stdout.flush()
	if len(filter(lambda x: len(x) > 0, out)) == 0:
		return (i, c, ll, out, 3)  # fail
	else:
		if postOrder:
			if not convert:
				if c in out:
					return (i, c, ll, out, 0)  # identical
			#res = parmap.map(convertPostOrderToC, out)
			res = map(convertPostOrderToC, out)
			if all(map(lambda x: not x[0], res)):
				return (i, c, ll, out, 2)  # parse
			else:
				if convert:
					out = map(lambda x: x[1].c().strip(), filter(lambda y: y[0], res))
				else:
					return (i, c, ll, out, 3)  # fail
		# compare c code
		if c in out:
			return (i, c, ll, out, 0)  # identical
		else:
			#res = parmap.map(compareProgs, map(lambda x: (c, x), out))
			res = map(compareProgs, map(lambda x: (c, x), out))
			for f in os.listdir('.'):
				if f.startswith('cbmc') and f.endswith('.c'):
					os.remove(f)
			if 0 in res:
				return (i, c, ll, out, 1)  # equivalent
			else:
				if 2 in res:
					return (i, c, ll, out, 3)  # fail
				else:
					if 1 in res:
						return (i, c, ll, out, 2)  # parse
					else:
						return (i, c, ll, out, 4)  # timeout


def evaluate(k, fc, fll, fout, postOrder, convert, fi=None, fs=None, ff=None, fp=None, ft=None):
	nidentical = 0
	nsuccess = 0
	nfail = 0
	nparse = 0
	ntimeout = 0
	cs = [l.strip() for l in fc.readlines()]
	lls = [l.strip() for l in fll.readlines()]
	outs = [map(lambda x: x.strip(), l.strip().split('|||')[0:2]) for l in fout.readlines()]
	groups = {}
	for (n, g) in itertools.groupby(outs, lambda x: x[0]):
		groups[int(n)] = [x[1] for x in g]
	max_len = max(len(cs), len(lls), len(groups.keys()))
	cs = cs + [''] * (max_len - len(cs))
	lls = lls + [''] * (max_len - len(lls))
	for i in filter(lambda x: x not in groups.keys(), range(max_len)):
		groups[i] = []
	results = map(
		lambda i: evaluateProg(i, str(i + 1).zfill(len(str(max_len))) + '/' + str(max_len), cs[i], lls[i], groups[i],
							   postOrder, convert), range(len(cs)))
	#print ''
	for x in results:
		if x[4] == 0:
			if fi:
				fi.writerow([str(x[0]), x[1], x[2]] + x[3])
			nidentical += 1
		else:
			if x[4] == 1:
				if fs:
					fs.writerow([str(x[0]), x[1], x[2]] + x[3])
				nsuccess += 1
			else:
				if x[4] == 2:
					if fp:
						fp.writerow([str(x[0]), x[1], x[2]] + x[3])
					nparse += 1
				else:
					if x[4] == 3:
						if ff:
							ff.writerow([str(x[0]), x[1], x[2]] + x[3])
						nfail += 1
					else:
						if ft:
							ft.writerow([str(x[0]), x[1], x[2]] + x[3])
						ntimeout += 1
	for f in os.listdir('.'):
		if f.startswith('cbmc') and f.endswith('.c'):
			os.remove(f)
	return (nidentical, nsuccess, nparse, nfail, ntimeout)


def main(f, k, ext, postOrder, convert):
	with open(f + '.identical.' + str(k) + '.csv', 'w') as fidentical:
		with open(f + '.equivalent.' + str(k) + '.csv', 'w') as fsuccess:
			with open(f + '.fail.' + str(k) + '.csv', 'w') as ffail:
				with open(f + '.parse.' + str(k) + '.csv', 'w') as fparse:
					with open(f + '.timeout.' + str(k) + '.csv', 'w') as ftimeout:
						csv.writer(fidentical).writerow(['line', ext, 'll'] + map(lambda i: 'out' + str(i), range(k)))
						csv.writer(fsuccess).writerow(['line', ext, 'll'] + map(lambda i: 'out' + str(i), range(k)))
						csv.writer(ffail).writerow(['line', ext, 'll'] + map(lambda i: 'out' + str(i), range(k)))
						csv.writer(fparse).writerow(['line', ext, 'll'] + map(lambda i: 'out' + str(i), range(k)))
						csv.writer(ftimeout).writerow(['line', ext, 'll'] + map(lambda i: 'out' + str(i), range(k)))
						with open(f + '.corpus.' + ext, 'r') as fc:
							with open(f + '.corpus.ll', 'r') as fll:
								with open(f + '.corpus.' + str(k) + '.out', 'r') as fout:
									(nidentical, nsuccess, nparse, nfail, ntimeout) = evaluate(k, fc, fll, fout,
																							   postOrder, convert,
																							   csv.writer(fidentical),
																							   csv.writer(fsuccess),
																							   csv.writer(ffail),
																							   csv.writer(fparse),
																							   csv.writer(ftimeout))
	print str(nidentical) + ' statements translated identically'
	print str(nsuccess) + ' statements translated equivalently'
	print str(nparse) + ' translated statements failed to parse'
	print str(nfail) + ' translated statements are not equivalent'
	print str(ntimeout) + ' translation evaluations timed-out'


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Evaluate dataset translations")
	parser.add_argument('dataset', type=str, help="dataset to translate")
	parser.add_argument('num_translations', type=int, help="number of translations in output for each input")
	parser.add_argument('-po', '--post-order', dest='po', help="use translations to post order code", action='count')
	parser.add_argument('-c', '--convert', dest='convert', help="convert post order to c", action='count')
	args = parser.parse_args()

	main(args.dataset, args.num_translations, 'po' if (args.po and not args.convert) else 'c', args.po, args.convert)
	for f in os.listdir('.'):
		if f.startswith('cbmc') and f.endswith('.c'):
			os.remove(f)
