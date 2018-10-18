import ConfigParser
import ast
import argparse
import numpy.random as npr
import os
import re
import sys
import logging
import json
from utils.colored_logger_with_timestamp import init_colorful_root_logger


hl2ll = None
def load_compiler(f):
	global hl2ll
	if f.endswith('.py'):
		f = f[:-3]
	if f.endswith('.pyc'):
		f = f[:-4]
	hl2ll =  __import__(f)


class SmartFormatter(argparse.HelpFormatter):
	def _split_lines(self, text, width):
		if text.startswith('R|'):
			return text[2:].splitlines()
		return argparse.HelpFormatter._split_lines(self, text, width)


parser = argparse.ArgumentParser(description="Generate random code samples", formatter_class=SmartFormatter)
parser.add_argument('compiler', type=str, help="file containing implementation of 'compiler' function")
parser.add_argument('-n', '--num', dest='n', type=int,
					help="R|number of samples to generate\n(if not given, generates samples until manually stopped)")
parser.add_argument('-o', '--out', dest='o', type=str, default='out',
					help="output files names (default: \'%(default)s\')")
parser.add_argument('-c', '--config', dest='c', type=str, default='configs/codenator.config',
					help="configuration file (default: \'%(default)s\')")
parser.add_argument('-e', '--exclude', dest='e', type=str,
					help="dataset to exclude from current generation")
parser.add_argument('-a', '--append', dest='a', type=str,
					help="initial dataset to extend")
parser.add_argument('-t', '--truncate', dest='t', type=int,
					help="truncate resulting dataset")
parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')

args = parser.parse_args()

config = ConfigParser.ConfigParser()
config.read(args.c)

load_compiler(args.compiler)

def choose_by_weight(values, weights):
	if len(values) == 1:
		return values[0]
	sum_weights = float(sum(weights))
	return npr.choice(values, p=map(lambda x: x/sum_weights, weights))


class Expr:
	def collect_vars(self):
		return set()


class Number(Expr):
	_minNumber = config.getint('Number', 'MinValue')
	_maxNumber = config.getint('Number', 'MaxValue')

	def __init__(self, nesting_level=0):
		value = npr.randint(Number._minNumber, Number._maxNumber+1)
		self._num = str(value)

	def __str__(self):
		return self._num

	def po(self):
		return self._num

	def __eq__(self, other):
		if not isinstance(other, Number):
			return False
		return other._num == self._num

	@staticmethod
	def reset():
		Number._constants_map = {}


class Var(Expr):
	_vars = []

	@staticmethod
	def clear():
		Var._vars = []

	@staticmethod
	def repopulate():
		def create_var(i):
			return Var(name='X' + str(i))

		Var._vars = map(create_var, xrange(config.getint('Var', 'NumVars')))

	def __init__(self, name=None, nesting_level=0):
		if name:
			self._name = name
		else:
			self._name = npr.choice(Var._vars)._name

	def __str__(self):
		return self._name

	def po(self):
		return self._name

	def __eq__(self, other):
		if not isinstance(other, Var):
			return False
		return other._name == self._name

	def __hash__(self):
		return hash(self._name)

	def collect_vars(self):
		return {self._name}


class Op(Expr):
	pass


class BinaryOp(Op):
	_Ops = ['+', '-', '*', '/', '%']

	def __init__(self, nesting_level=0):
		self._op1 = get_expr(nesting_level+1)
		self._act = npr.choice(BinaryOp._Ops)
		self._op2 = get_expr(nesting_level+1)
		while (self._op2 == self._op1) or \
				((self._act == '/') and isinstance(self._op2, Number) and (self._op2._num == 0)) or \
				(isinstance(self._op1, Number) and isinstance(self._op2, Number)):
			self._op2 = get_expr(nesting_level+1)

	def __str__(self):
		res = ''
		if isinstance(self._op1, Op):
			res += '( ' + str(self._op1) + ' )'
		else:
			res += str(self._op1)
		res += ' ' + self._act + ' '
		if isinstance(self._op2, Op):
			res += '( ' + str(self._op2) + ' )'
		else:
			res += str(self._op2)
		return res

	def po(self):
		return self._op1.po() + ' ' + self._op2.po() + ' ' + self._act

	def __eq__(self, other):
		if not isinstance(other, BinaryOp):
			return False
		return (other._act == self._act) and (other._op1 == self._op1) and (other._op2 == self._op2)

	def collect_vars(self):
		return self._op1.collect_vars().union(self._op2.collect_vars())


class UnaryOp(Op):
	_Ops = ['++', '--']

	def __init__(self, nesting_level=0):
		self._op = Var()
		self._act = npr.choice(UnaryOp._Ops)
		self._position = npr.choice([True, False])

	def __str__(self):
		res = ''
		if self._position:
			res += self._act + ' '
		res += str(self._op)
		if not self._position:
			res += ' ' + self._act
		return res

	def po(self):
		return self._op.po() + ' ' + ('X' if self._position else '') + self._act + ('' if self._position else 'X')

	def __eq__(self, other):
		if not isinstance(other, UnaryOp):
			return False
		return (other._act == self._act) and (other._op == self._op)

	def collect_vars(self):
		return self._op.collect_vars()


class Assignment:
	def __init__(self, nesting_level=0):
		self._source = get_expr()
		self._target = Var()

	def __str__(self):
		return str(self._target) + ' = ' + str(self._source)

	def po(self):
		return self._source.po() + ' ' + self._target.po() + ' = '

	def __eq__(self, other):
		if not isinstance(other, Assignment):
			return False
		return other._source == self._source

	def collect_vars(self):
		return self._source.collect_vars().union(self._target.collect_vars())


class Condition:
	_Relations = ['>', '>=', '<', '<=', '==', '!=']

	def __init__(self):
		self._op1 = get_expr()
		self._act = npr.choice(Condition._Relations)
		self._op2 = get_expr()
		while self._op2 == self._op1 or (isinstance(self._op1, Number) and isinstance(self._op2, Number)):
			self._op2 = get_expr()

	def __str__(self):
		res = ''
		if isinstance(self._op1, Op):
			res += '( ' + str(self._op1) + ' )'
		else:
			res += str(self._op1)
		res += ' ' + self._act + ' '
		if isinstance(self._op2, Op):
			res += '( ' + str(self._op2) + ' )'
		else:
			res += str(self._op2)
		return res

	def po(self):
		return self._op1.po() + ' ' + self._op2.po() + ' ' + self._act + ' COND '

	def __eq__(self, other):
		if not isinstance(other, Condition):
			return False
		return (other._act == self._act) and (other._op1 == self._op1) and (other._op2 == self._op2)

	def collect_vars(self):
		return self._op1.collect_vars().union(self._op2.collect_vars())


class Branch:
	_elseRatio = config.getfloat('Branch', 'ElseRatio')

	def __init__(self, nesting_level=0):
		def body_generator():
			return Statements(types=[Assignment], nesting_level=nesting_level+1, max_statements=config.getint('Branch','MaxInnerStatements'))

		self._cond = Condition()
		self._if = body_generator()
		if npr.random() > Branch._elseRatio:
			self._else = body_generator()
			while self._else == self._if:
				self._else = body_generator()
		else:
			self._else = None

	def __eq__(self, other):
		if not isinstance(other, Branch):
			return False
		if (other._cond != self._cond) or (other._if != self._if):
			return False
		if (other._else and not self._else) or (self._else and not other._else):
			return False
		if other._else and self._else:
			return other._else == self._else
		return True

	def __str__(self):
		res = 'if ( ' + str(self._cond) + ' ) { ' + str(self._if) + ' } '
		if self._else:
			res += 'else { ' + str(self._else) + ' } '
		return res

	def po(self):
		return self._cond.po() + self._if.po() + 'TRUE ' + (
			(self._else.po() + 'FALSE ') if self._else else '') + ' IF '

	def collect_vars(self):
		return self._if.collect_vars().union(self._else.collect_vars() if self._else else set()).union(self._cond.collect_vars())


class Loop:

	def __init__(self, nesting_level=0):
		def body_generator():
			return Statements(types=[Assignment], nesting_level=nesting_level+1, max_statements=config.getint('Loop','MaxInnerStatements'))

		self._cond = Condition()
		self._body = body_generator()

	def __eq__(self, other):
		if not isinstance(other, Loop):
			return False
		if (other._cond != self._cond) or (other._body != self._body):
			return False
		return True

	def __str__(self):
		return 'while ( ' + str(self._cond) + ' ) { ' + str(self._body) + ' } '

	def po(self):
		return self._cond.po() + self._body.po() + ' WHILE '

	def collect_vars(self):
		return self._body.collect_vars().union(self._cond.collect_vars())


_exprs = [Number, Var, BinaryOp, UnaryOp]
def get_expr(nesting_level=0):
	weights = map(lambda e: config.getfloat(e.__name__, 'Weight'), _exprs)
	degrade = map(lambda e: config.getfloat(e.__name__, 'Degrade'), _exprs)
	nested_weights = map(lambda i: weights[i]/pow(degrade[i], nesting_level), xrange(len(weights)))
	expression = choose_by_weight(_exprs, nested_weights)
	return expression(nesting_level=nesting_level)


class Statements:
	_max_statements = config.getint('Statements', 'MaxStatements')
	_statements_weights = ast.literal_eval(config.get('Statements', 'Weights'))

	def __init__(self, types=[Assignment, Branch, Loop], nesting_level=0, max_statements=_max_statements):
		statements_limit = min(max_statements, Statements._max_statements)
		weights = map(lambda i: float(Statements._statements_weights[i])/pow(i+1, nesting_level), xrange(statements_limit))
		num_statements = choose_by_weight(range(1, statements_limit + 1), weights)
		self._inner = map(lambda i: Statements.generate_statement(types)(nesting_level=nesting_level), xrange(num_statements))

	@staticmethod
	def generate_statement(types):
		return choose_by_weight(types, map(lambda x: config.getfloat(x.__name__, 'Weight'), types))

	def collect_vars(self):
		return reduce(lambda y, z: y.union(z), map(lambda x: x.collect_vars(), self._inner), set())

	def __str__(self):
		return ' ; '.join(map(str, self._inner)+[''])

	def po(self):
		return ' '.join(map(lambda x: x.po(), self._inner))

	def __eq__(self, other):
		if not isinstance(other, Statements):
			return False
		if len(self._inner) != len(other._inner):
			return False
		for i in xrange(len(self._inner)):
			if self._inner[i] != other._inner[i]:
				return False
		return True


def compiler(s):
	return hl2ll.compiler(s)


def preprocess_hl(s):
	return s.po()


def generate_number_replacements(line):
	min_abstracted_number = config.getint("Number", "MinAbstractedValue")
	max_abstracted_number = config.getint("Number", "MaxAbstractedValue")
	max_constants = config.getint("Number", "NumbersPerStatement")
	replacements = {}
	parts = line.strip().split(" ")
	for i in range(len(parts)):
		if hl2ll.is_number(parts[i]):
			number = hl2ll.get_number(parts[i])
			if (int(number) >= min_abstracted_number) and (int(number) <= max_abstracted_number):
				constant = 'N' + str(npr.randint(0, max_constants))
				replacements[number] = constant
				parts[i] = constant
	return (" ".join(parts), replacements)


def apply_number_replacements(line, replacements):
	parts = line.strip().split(" ")
	for i in range(len(parts)):
		if parts[i] in replacements.keys():
			parts[i] = replacements[parts[i]]
	return " ".join(parts)


def generate_statements():
	if args.n is not None:
		limit = args.n
		limited = True
	else:
		limit = 0
		limited = False
	out_file = args.o
	j = 1
	Var.clear()
	Var.repopulate()
	corpus_hl = []
	corpus_ll = []
	corpus_replacements = []
	exclude = set()
	if args.e is not None:
		if os.path.exists(args.e+'.corpus.hl'):
			logging.info('Excluding dataset: ' + str(args.e))
			with open(args.e+'.corpus.hl', 'r') as f:
				for l in f.readlines():
					exclude.add(l.strip())
	if args.a is not None:
		if os.path.exists(args.a+'.corpus.hl') and os.path.exists(args.a+'.corpus.ll') and os.path.exists(args.a+'.corpus.replacements'):
			logging.info('Initial dataset: ' + str(args.a))
			with open(args.a+'.corpus.hl', 'r') as fhl:
				with open(args.a + '.corpus.ll', 'r') as fll:
					with open(args.a + '.corpus.replacements', 'r') as freplacements:
						hl_lines = map(lambda x: x.strip(), fhl.readlines())
						ll_lines = map(lambda x: x.strip(), fll.readlines())
						replacements_lines = map(lambda x: x.strip(), freplacements.readlines())
			assert len(hl_lines) == len(ll_lines)
			assert len(hl_lines) == len(replacements_lines)
			for i in xrange(len(hl_lines)):
				if hl_lines[i] not in exclude:
					corpus_hl.append(hl_lines[i])
					corpus_ll.append(ll_lines[i])
					corpus_replacements.append(replacements_lines[i])
					exclude.add(hl_lines[i])
	if limited:
		logging.info('Generating ' + str(limit) + ' statements')
	else:
		logging.info('Generating statements until manually stopped (ctrl+C)')
	logging.info('Saving to files: ' + out_file + '.corpus.hl, ' + out_file + '.corpus.ll')
	while (not limited) or (j <= limit):
		if args.debug:
			if limited:
				print str(j).zfill(len(str(limit)))+'/'+str(limit)+'\r',
			else:
				print str(j)+'\r',
			sys.stdout.flush()
		done = False
		hl_line = ''
		s = None
		Number.reset()
		while not done:
			try:
				s = Statements()
				hl_line = re.sub('[ \t]+', ' ', preprocess_hl(s)).strip()
				if hl_line not in exclude:
					done = True
			except RuntimeError:
				pass
		exclude.add(hl_line)
		ll_line = re.sub('[ \t]+', ' ', compiler(s))
		(ll_line, replacements) = generate_number_replacements(ll_line)
		hl_line = apply_number_replacements(hl_line, replacements)
		corpus_ll.append(ll_line.strip())
		corpus_hl.append(hl_line.strip())
		reverse_replacement = {}
		for k in replacements.keys():
			reverse_replacement[replacements[k]] = k
		corpus_replacements.append(json.dumps(reverse_replacement))
		j += 1
	logging.info('Shuffling and writing dataset')
	if args.t:
		logging.info('Truncating to '+str(args.t)+' entries')
	j = 0
	with open(out_file + '.corpus.hl', 'w') as fhl:
		with open(out_file + '.corpus.ll', 'w') as fll:
			with open(out_file + '.corpus.replacements', 'w') as freplacements:
				for i in npr.permutation(len(corpus_hl)):
					if args.t:
						if j >= args.t:
							break
					fhl.write(corpus_hl[i] + '\n')
					fll.write(corpus_ll[i] + '\n')
					freplacements.write(corpus_replacements[i] + '\n')
					j += 1
	logging.info('Done!')


if __name__ == "__main__":
	init_colorful_root_logger(logging.getLogger(''), vars(args))
	logging.info('Compiler provided by '+args.compiler)
	generate_statements()
