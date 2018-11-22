import os
import itertools
import csv
import postOrderUtil as po_util
import re
import logging
import json
from utils.colored_logger_with_timestamp import init_colorful_root_logger
import ConfigParser
import graph_comparison as gc
from abstract_numerals import *
import code_fixer as cf
import random


def parsePostOrder(po):
	return po_util.parse(po)


hl2ll = None
def load_compiler(f):
	global hl2ll
	if f.endswith('.py'):
		f = f[:-3]
	if f.endswith('.pyc'):
		f = f[:-4]
	hl2ll =  __import__(f)


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
	s = ''.join([y + ' ; ' for y in filter(lambda x: len(x) > 0, hl.split(';'))])
	return hl2ll.compiler(MockHL(s), check_success=True)


def apply_number_replacements_wrapper(ll, replacements, config):
	min_value = max(config.getint('Number', 'MinValue'), config.getint('Number', 'MinAbstractedValue'))
	max_value = min(config.getint('Number', 'MaxValue'), config.getint('Number', 'MaxAbstractedValue'))
	code = apply_number_replacements(ll, replacements).split(' ')
	for i in range(len(code)):
		if re.match('^N[0-9]+$', code[i]):
			code[i] = str(random.randint(min_value, max_value))
	return ' '.join(code)


def evaluateProg(i, hl, ll, out, replacements, config, failed_dataset=None):
	# if hl in out:
	# 	return (i, hl, ll, replacements, hl, 0)  # success
	if len(filter(lambda x: len(x) > 0, out)) == 0:
		return (i, hl, ll, replacements, None, 1)  # no translations
	out = map(lambda x: apply_number_replacements(x, replacements), out)
	res = map(parsePostOrder, out)
	if all(map(lambda x: not x[0], res)):
		return (i, hl, ll, replacements, None, 2)  # unparsable
	cs = map(lambda x: x[1].c().strip() if x[0] else '', res)
	# compare c code
	lls = map(lambda x: compiler(x), cs)
	if not any(lls):
		return (i,hl, ll, replacements, None, 3)  # does not compile
	lls = map(lambda l: re.sub('[ \t]+', ' ', l.strip()) if l is not None else '', lls)
	ll = apply_number_replacements_wrapper(ll, replacements, config)
	if ll in lls:
		return (i, hl, ll, replacements, cs[lls.index(ll)], 0)  # success
	graph_comparisons = map(lambda l: gc.compare_codes(l, ll), lls)
	successful_comparisons = filter(lambda j: graph_comparisons[j][0], range(len(graph_comparisons)))
	if len(successful_comparisons) > 0:
		for j in successful_comparisons:
			needed_replacements = graph_comparisons[j][1]
			if all(map(lambda l: len(l) == 0, needed_replacements.values())):
				return (i, hl, ll, replacements, cs[j], 0)  # success
			else:
				logging.debug('Attempting to fix code for input '+str(i))
				fixed_code = cf.fix_code(cs[j], ll, hl2ll, gc, lls[j], needed_replacements)
				if fixed_code is not None:
					logging.debug('Fix successful!')
					return (i, hl, ll, replacements, fixed_code, 0)  # success
	if failed_dataset:
		with open(failed_dataset + '.corpus.hl', 'a') as fhl:
			with open(failed_dataset + '.corpus.ll', 'a') as fll:
				with open(failed_dataset + '.corpus.replacements', 'a') as freplacements:
					for j in range(len(out)):
						if len(out[j]) > 0 and len(lls[j]) > 0:
							(l, replaces) = generate_number_replacements(lls[j], config, hl2ll)
							h = apply_number_replacements(out[j], replaces)
							fhl.write(h + '\n')
							fll.write(l + '\n')
							freplacements.write(json.dumps(reverse_mapping(replaces)) + '\n')
	return (i, hl, ll, replacements, None, 4)  # fail


def evaluate(fhl, fll, fout, freplacemetns, force, config, fs=None, ff=None, failed_dataset=None):
	nsuccess = 0
	nfail = 0
	hls = [re.sub('[ \t]+', ' ', l.strip()) for l in fhl.readlines()]
	lls = [re.sub('[ \t]+', ' ', l.strip()) for l in fll.readlines()]
	outs = [map(lambda x: re.sub('[ \t]+', ' ', x.strip()), l.strip().split('|||')[0:2]) for l in fout.readlines()]
	replacements = [json.loads(l.strip()) for l in freplacemetns.readlines()]
	groups = {}
	for (n, g) in itertools.groupby(outs, lambda x: x[0]):
		groups[int(n)] = [x[1] for x in g]
	results = map(
		lambda i: evaluateProg(i, hls[i], lls[i], groups[i] if i in groups.keys() else [], replacements[i], config, failed_dataset), range(len(lls)))
	for x in results:
		if x[5] == 0:
			if fs:
				fs.writerow([str(x[0]), x[1], x[2], json.dumps(x[3]), x[4]])
			nsuccess += 1
		else:
			if ff:
				ff.writerow([str(x[0]), x[1], x[2], json.dumps(x[3]), x[4]])
			nfail += 1
	if force:
		for f in os.listdir('.'):
			if f.startswith('tmp') and (f.endswith('.c') or f.endswith('ll')):
				os.remove(f)
	return (nsuccess, nfail)


def main(f, k, compiler, force, config, failed_dataset=None):
	logging.info('Compiler provided by '+args.compiler)
	load_compiler(compiler)
	gc.set_instruction_class(hl2ll.Instruction)
	with open(f + '.success.' + str(k) + '.csv', 'w') as fsuccess:
		with open(f + '.fail.' + str(k) + '.csv', 'w') as ffail:
			csv.writer(fsuccess).writerow(['line', 'hl', 'll', 'replacements', 'out'])
			csv.writer(ffail).writerow(['line', 'hl', 'll', 'replacements'])
			with open(f + '.corpus.hl', 'r') as fhl:
				with open(f + '.corpus.ll', 'r') as fll:
					with open(f + '.corpus.' + str(k) + '.out', 'r') as fout:
						with open(f + '.corpus.replacements', 'r') as freplacements:
							(nsuccess, nfail) = evaluate(fhl, fll, fout, freplacements, force, config,
													 fs=csv.writer(fsuccess), ff=csv.writer(ffail),
													 failed_dataset=failed_dataset)
	logging.info(str(nsuccess) + ' statements translated successfully')
	logging.info(str(nfail) + ' statements failed to translate')


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Evaluate dataset translations")
	parser.add_argument('dataset', type=str, help="dataset to translate")
	parser.add_argument('num_translations', type=int, help="number of translations in output for each input")
	parser.add_argument('compiler', type=str, help="file containing implementation of 'compiler' function")
	parser.add_argument('-f', '--force-cleanup', dest='force', help="force delete all tmp files when finished",
						action='count')
	parser.add_argument('-d', '--failed-dataset', dest='failed_dataset', type=str,
						help="dataset for which to write failed translations")
	parser.add_argument('-c', '--config', dest='c', type=str, default='configs/codenator.config',
						help="configuration file (default: \'%(default)s\')")
	parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
	parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')
	args = parser.parse_args()
	init_colorful_root_logger(logging.getLogger(''), vars(args))

	config = ConfigParser.ConfigParser()
	config.read(args.c)

	main(args.dataset, args.num_translations, args.compiler, args.force, config, args.failed_dataset)
	if args.force:
		for f in os.listdir('.'):
			if f.startswith('tmp') and (f.endswith('.c') or f.endswith('ll')):
				os.remove(f)
