import os
import itertools
import csv
import postOrderUtil as po_util
import llvmUtil as hl2ll
import re
import logging
from utils.colored_logger_with_timestamp import init_colorful_root_logger


def parsePostOrder(po):
	return po_util.parse(po)


class MockHL:
	def __init__(self, s):
		self._s = s
		self._vars = set()
		self._nums = set()
		for x in s.split(' '):
			if re.match('^N[0-9]+$',x):
				self._nums.add(x)
			elif re.match('^X[0-9]+$',x):
				self._vars.add(x)
	def __str__(self):
		return self._s
	def collect_vars(self):
		return self._vars
	def collect_nums(self):
		return self._nums

def compiler(hl):
	if not hl:
		return hl
	s = [y + ' ; ' for y in filter(lambda x: len(x) > 0, hl.split(';'))]
	return hl2ll.llvm_compiler(MockHL(s))

def evaluateProg(i, hl, ll, out, failed_dataset=None):
	if hl in out:
		return (i, hl, ll, hl, 0)  # success
	if len(filter(lambda x: len(x) > 0, out)) == 0:
		return (i, hl, ll, None, 1)  # fail
	else:
		res = map(parsePostOrder, out)
		if all(map(lambda x: not x[0], res)):
			return (i, hl, ll, None, 2)  # unparsable
		cs = map(lambda x: x[1].c().strip() if x[0] else '', res)
		# compare c code
		lls = map(lambda x: compiler(x), cs)
		if not any(lls):
			return (i,hl, ll, None, 2)  # unparsable
		lls = map(lambda l: l.strip() if l is not None else '', lls)
		if ll in lls:
			return (i, hl, ll, cs[lls.index(ll)], 0)  # success
		if failed_dataset:
			with open(failed_dataset + '.corpus.hl', 'a') as fhl:
				with open(failed_dataset + '.corpus.ll', 'a') as fll:
					for j in range(len(out)):
						if len(out[j]) > 0 and len(lls[j]) > 0:
							fhl.write(out[j] + '\n')
							fll.write(lls[j] + '\n')
		return (i, hl, ll, None, 1)  # fail


def evaluate(fhl, fll, fout, force, fs=None, ff=None, failed_dataset=None):
	nsuccess = 0
	nfail = 0
	hls = [l.strip() for l in fhl.readlines()]
	lls = [l.strip() for l in fll.readlines()]
	outs = [map(lambda x: x.strip(), l.strip().split('|||')[0:2]) for l in fout.readlines()]
	groups = {}
	for (n, g) in itertools.groupby(outs, lambda x: x[0]):
		groups[int(n)] = [x[1] for x in g]
	results = map(
		lambda i: evaluateProg(i, hls[i], lls[i], groups[i], failed_dataset),
		range(len(lls)))
	for x in results:
		if x[4] == 0:
			if fs:
				fs.writerow([str(x[0]), x[1], x[2], x[3]])
			nsuccess += 1
		else:
			if ff:
				ff.writerow([str(x[0]), x[1], x[2], x[3]])
			nfail += 1
	if force:
		for f in os.listdir('.'):
			if f.startswith('tmp') and (f.endswith('.c') or f.endswith('ll')):
				os.remove(f)
	return (nsuccess, nfail)


def main(f, k, force, failed_dataset=None):
	with open(f + '.success.' + str(k) + '.csv', 'w') as fsuccess:
		with open(f + '.fail.' + str(k) + '.csv', 'w') as ffail:
			csv.writer(fsuccess).writerow(['line', 'hl', 'll', 'out'])
			csv.writer(ffail).writerow(['line', 'hl', 'll'])
			with open(f + '.corpus.hl', 'r') as fhl:
				with open(f + '.corpus.ll', 'r') as fll:
					with open(f + '.corpus.' + str(k) + '.out', 'r') as fout:
						(nsuccess, nfail) = evaluate(fhl, fll, fout, force,
													 fs=csv.writer(fsuccess), ff=csv.writer(ffail),
													 failed_dataset=failed_dataset)
	logging.info(str(nsuccess) + ' statements translated successfully')
	logging.info(str(nfail) + ' statements failed to translate')


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Evaluate dataset translations")
	parser.add_argument('dataset', type=str, help="dataset to translate")
	parser.add_argument('num_translations', type=int, help="number of translations in output for each input")
	parser.add_argument('-f', '--force-cleanup', dest='force', help="force delete all tmp files when finished",
						action='count')
	parser.add_argument('-c', '--config', dest='config', type=str, default='configs/codenator.config',
						help="configuration file used for llvm compilation (default: \'%(default)s\')")
	parser.add_argument('-s', '--settings', dest='settings', type=str, default='configs/codenator_setting.config',
						help="general settings used for llvm compilation (default: \'%(default)s\')")
	parser.add_argument('-d', '--failed-dataset', dest='failed_dataset', type=str,
						help="dataset for which to write failed translations")
	parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
	parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')
	args = parser.parse_args()
	init_colorful_root_logger(logging.getLogger(''), vars(args))

	main(args.dataset, args.num_translations, args.force, args.failed_dataset)
	if args.force:
		for f in os.listdir('.'):
			if f.startswith('tmp') and (f.endswith('.c') or f.endswith('ll')):
				os.remove(f)
