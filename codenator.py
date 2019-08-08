import ConfigParser
import ast
import argparse
import os
import re
import sys
import logging
import json
from utils.colored_logger_with_timestamp import init_colorful_root_logger
from abstract_numerals import *
import numpy.random as npr


hl2ll = None
def load_compiler(f):
	global hl2ll
	if f.endswith('.py'):
		f = f[:-3]
	if f.endswith('.pyc'):
		f = f[:-4]
	hl2ll =  __import__(f)


parser = argparse.ArgumentParser(description="Generate random code samples")
parser.add_argument('compiler', type=str, help="file containing implementation of 'compiler' function")
parser.add_argument('-n', '--num', dest='n', type=int, default=0,
					help="number of samples to generate (default: %(default)s")
parser.add_argument('-o', '--out', dest='o', type=str, default='out',
					help="output files names (default: \'%(default)s\')")
parser.add_argument('-c', '--config', dest='c', type=str, default='configs/codenator.config',
					help="configuration file (default: \'%(default)s\')")
parser.add_argument('-e', '--exclude', dest='e', type=str,
					help="dataset to exclude from current generation")
parser.add_argument('-a', '--append', dest='a', type=str,
					help="initial dataset to extend")
parser.add_argument('-r', '--retain', dest='r', type=int,
					help="percentate of initial dataset to retain (value should be between 0 and 100)")
parser.add_argument('-t', '--truncate', dest='t', type=int,
					help="truncate resulting dataset")
parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')

args = parser.parse_args()

config = ConfigParser.ConfigParser()
config.read(args.c)

load_compiler(args.compiler)

def choose_by_weight(values, weights, degrade=None, nesting_level=0):
	if len(values) == 1:
		return values[0]
	if degrade is not None:
		nested_weights = map(lambda i: weights[i] / pow(degrade[i], nesting_level), xrange(len(weights)))
	else:
		nested_weights = weights
	sum_weights = float(sum(nested_weights))
	return npr.choice(values, p=map(lambda x: x/sum_weights, nested_weights))


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
	_Ops = ast.literal_eval(config.get('BinaryOp', 'Ops'))
	_OpsWeights = ast.literal_eval(config.get('BinaryOp', 'OpsWeights'))

	def __init__(self, nesting_level=0):
		self._act = choose_by_weight(BinaryOp._Ops, BinaryOp._OpsWeights)
		self._op1 = get_expr(nesting_level+1)
		while isinstance(self._op1, Number) and \
				(((self._op1._num == 0) and (self._act != '-')) or \
				 ((self._op1._num == 1) and (self._act in ['*', '%']))):
			self._op1 = get_expr(nesting_level + 1)
		self._op2 = get_expr(nesting_level+1)
		while (self._op2 == self._op1) or \
				(isinstance(self._op1, Number) and isinstance(self._op2, Number)) or \
				(isinstance(self._op2, Number) and ((self._op2._num == 0) or \
													((self._op2._num == 1) and (self._act in ['*', '/', '%'])))) or \
				(isinstance(self._op2, Number) and (self._act in ['<<', '>>']) and
				 									((self._op2._num > 32) or (self._op2._num < 1))) and \
				((self._act in ['&', '|', '^']) and (isinstance(self._op2, Number) and (self._op2._num == 0)) or \
				 									(isinstance(self._op1, Number) and (self._op1._num == 0))):
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
		return re.sub('\s+', ' ', res).strip()

	def po(self):
		return re.sub('\s+', ' ', self._op1.po() + ' ' + self._op2.po() + ' ' + self._act)

	def __eq__(self, other):
		if not isinstance(other, BinaryOp):
			return False
		return (other._act == self._act) and (other._op1 == self._op1) and (other._op2 == self._op2)

	def collect_vars(self):
		return self._op1.collect_vars().union(self._op2.collect_vars())


class StatementUnaryOp(Op):
	_Ops = ast.literal_eval(config.get('StatementUnaryOp', 'Ops'))
	_OpsWeights = ast.literal_eval(config.get('StatementUnaryOp', 'OpsWeights'))
	_PositionRatio = config.getfloat('StatementUnaryOp', 'PositionRatio')

	def __init__(self, nesting_level=0):
		self._op = Var()
		self._act = choose_by_weight(StatementUnaryOp._Ops, StatementUnaryOp._OpsWeights)
		self._position = (npr.random() > StatementUnaryOp._PositionRatio)

	def __str__(self):
		res = ''
		if self._position:
			res += self._act + ' '
		res += str(self._op)
		if not self._position:
			res += ' ' + self._act
		return re.sub('\s+', ' ', res).strip()

	def po(self):
		return re.sub('\s+', ' ', self._op.po() + ' ' + ('' if self._position else 'X') + self._act + ('X' if self._position else ''))

	def __eq__(self, other):
		if not isinstance(other, StatementUnaryOp):
			return False
		return (other._act == self._act) and (other._op == self._op)

	def collect_vars(self):
		return self._op.collect_vars()


class OtherUnaryOp(Op):
	_Ops = ast.literal_eval(config.get('OtherUnaryOp', 'Ops'))
	_OpsWeights = ast.literal_eval(config.get('OtherUnaryOp', 'OpsWeights'))

	def __init__(self, nesting_level=0):
		self._op = get_expr()
		self._act = choose_by_weight(OtherUnaryOp._Ops, OtherUnaryOp._OpsWeights)

	def __str__(self):
		return re.sub('\s+', ' ', self._act + ' ( ' + str(self._op) + ' )').strip()

	def po(self):
		return re.sub('\s+', ' ', self._op.po() + ' ' + self._act + 'X')

	def __eq__(self, other):
		if not isinstance(other, OtherUnaryOp):
			return False
		return (other._act == self._act) and (other._op == self._op)

	def collect_vars(self):
		return self._op.collect_vars()


class Assignment:
	def __init__(self, nesting_level=0):
		self._source = get_expr()
		self._target = Var()

	def __str__(self):
		return re.sub('\s+', ' ', str(self._target) + ' = ' + str(self._source)).strip()

	def po(self):
		return re.sub('\s+', ' ', self._source.po() + ' ' + self._target.po() + ' = ')

	def __eq__(self, other):
		if not isinstance(other, Assignment):
			return False
		return other._source == self._source

	def collect_vars(self):
		return self._source.collect_vars().union(self._target.collect_vars())


class Condition:
	_Relations = ['>', '>=', '<', '<=', '==', '!=']
	_InitialNestingLevel = config.getint('Condition', 'InitialNestingLevel')

	def __init__(self):
		self._op1 = get_expr(nesting_level=Condition._InitialNestingLevel)
		self._act = npr.choice(Condition._Relations)
		self._op2 = get_expr(nesting_level=Condition._InitialNestingLevel)
		while self._op2 == self._op1 or (isinstance(self._op1, Number) and isinstance(self._op2, Number)):
			self._op2 = get_expr(nesting_level=Condition._InitialNestingLevel)

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
		return re.sub('\s+', ' ', res).strip()

	def po(self):
		return re.sub('\s+', ' ', self._op1.po() + ' ' + self._op2.po() + ' ' + self._act + ' COND ')

	def __eq__(self, other):
		if not isinstance(other, Conditions.Condition):
			return False
		return (other._act == self._act) and (other._op1 == self._op1) and (other._op2 == self._op2)

	def collect_vars(self):
		return self._op1.collect_vars().union(self._op2.collect_vars())


class Conditions:
	_LogicalOperators = ['||', '&&']
	_NegateRatio = config.getfloat('Condition', 'NegateRatio')
	_MaxConditionsNestingLevel = config.getint('Condition', 'MaxConditionsNestingLevel')
	_MoreConditionsProbability = config.getfloat('Condition', 'MoreConditionsProbability')

	def __init__(self, nesting_level=0):
		probability = Conditions._MoreConditionsProbability / (nesting_level + 1)
		# probability = pow(Statements._more_statements_probability, nesting_level + 1)
		if (npr.random() > probability) or (nesting_level >= Conditions._MaxConditionsNestingLevel):
			self._conds = [Condition()]
			self._concat = None
		else:
			self._conds = [Conditions(nesting_level=nesting_level + 1), Conditions(nesting_level=nesting_level + 1)]
			self._concat = npr.choice(Conditions._LogicalOperators)
		self._negate = (npr.random() <= Conditions._NegateRatio)

	def __str__(self):
		res = ''
		if self._negate:
			res += '! ( '
		if len(self._conds) == 1:
			res += str(self._conds[0])
		else:
			res += '( ' + str(self._conds[0]) + ' ) ' + self._concat + ' ( ' + str(self._conds[1]) + ' )'
		if self._negate:
			res += ' )'
		return re.sub('\s+', ' ', res).strip()

	def po(self):
		res = self._conds[0].po()
		if len(self._conds) > 1:
			res += self._conds[1].po() + self._concat
		if self._negate:
			res += ' NOT'
		# 'CONDS' should only appear at the end of the overall condition
		res = re.sub(' CONDS', '', res)
		return re.sub('\s+', ' ', res + ' CONDS ')

	def __eq__(self, other):
		if not isinstance(other, Conditions):
			return False
		if len(self._conds) != len(other._conds):
			return False
		if  self._negate != other._negate:
			return False
		if len(self._conds) == 1:
			return self._conds[0].__eq__(other._conds[0])
		return (self._concat == other._concat) and self._conds[0].__eq__(other._conds[0]) and self._conds[1].__eq__(other._conds[1])

	def collect_vars(self):
		if len(self._conds) == 1:
			return self._conds[0].collect_vars()
		return self._conds[0].collect_vars().union(self._conds[1].collect_vars())


class Branch:
	_elseRatio = config.getfloat('Branch', 'ElseRatio')

	def __init__(self, nesting_level=0):
		def body_generator():
			return Statements(
				types=[Assignment, Branch, Loop] if config.getboolean('Branch', 'AllowNested') else [Assignment],
				nesting_level=nesting_level+1,
				max_statements=config.getint('Branch', 'MaxInnerStatements')
			)

		self._cond = Conditions()
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
		return re.sub('\s+', ' ', res).strip()

	def po(self):
		return re.sub('\s+', ' ', self._cond.po() + self._if.po() + 'TRUE ' + (
			(self._else.po() + 'FALSE ') if self._else else '') + ' IF ')

	def collect_vars(self):
		return self._if.collect_vars().union(self._else.collect_vars() if self._else else set()).union(self._cond.collect_vars())


class Loop:
	def __init__(self, nesting_level=0):
		def body_generator():
			return Statements(
				types=[Assignment, Branch, Loop] if config.getboolean('Loop', 'AllowNested') else [Assignment],
				nesting_level=nesting_level+1,
				max_statements=config.getint('Loop', 'MaxInnerStatements')
			)

		self._cond = Conditions()
		self._body = body_generator()

	def __eq__(self, other):
		if not isinstance(other, Loop):
			return False
		if (other._cond != self._cond) or (other._body != self._body):
			return False
		return True

	def __str__(self):
		return re.sub('\s+', ' ', 'while ( ' + str(self._cond) + ' ) { ' + str(self._body) + ' } ').strip()

	def po(self):
		return re.sub('\s+', ' ', self._cond.po() + self._body.po() + ' WHILE ')

	def collect_vars(self):
		return self._body.collect_vars().union(self._cond.collect_vars())


_exprs = [Number, Var, BinaryOp, StatementUnaryOp, OtherUnaryOp]
def get_expr(nesting_level=0):
	weights = map(lambda e: config.getfloat(e.__name__, 'Weight'), _exprs)
	degrade = map(lambda e: config.getfloat(e.__name__, 'Degrade'), _exprs)
	expression = choose_by_weight(_exprs, weights, degrade, nesting_level)
	return expression(nesting_level=nesting_level)


class Statements:
	_max_statements = config.getint('Statements', 'MaxStatements')
	_more_statements_probability = config.getfloat('Statements', 'MoreStatementsProbability')

	def __init__(self, types=filter(lambda x: x is not None, [Assignment, Branch, Loop, StatementUnaryOp if config.getboolean('StatementUnaryOp', 'AllowAsStatement') else None]), nesting_level=0, max_statements=_max_statements):
		statements_limit = min(max_statements, Statements._max_statements)
		probability = Statements._more_statements_probability / (nesting_level + 1)
		# probability = pow(Statements._more_statements_probability, nesting_level + 1)
		self._inner = []
		while len(self._inner) <= statements_limit:
			self._inner.append(Statements.generate_statement(types, nesting_level=nesting_level)(nesting_level=nesting_level))
			if npr.random() <= probability:
				break

	@staticmethod
	def generate_statement(types, nesting_level=0):
		return choose_by_weight(types, map(lambda x: config.getfloat(x.__name__, 'Weight'), types), map(lambda x: config.getfloat(x.__name__, 'Degrade'), types), nesting_level)

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


def generate_statements():
	limit = args.n
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
			if args.r is not None:
				chosen_indexes = npr.choice(range(len(hl_lines)), len(hl_lines)*(100-args.r)/100)
				hl_lines = map(lambda i: hl_lines[i], chosen_indexes)
				ll_lines = map(lambda i: ll_lines[i], chosen_indexes)
				replacements_lines = map(lambda i: replacements_lines[i], chosen_indexes)
			for i in xrange(len(hl_lines)):
				if hl_lines[i] not in exclude:
					corpus_hl.append(hl_lines[i])
					corpus_ll.append(ll_lines[i])
					corpus_replacements.append(replacements_lines[i])
					exclude.add(hl_lines[i])
	logging.info('Generating ' + str(limit) + ' statements')
	logging.info('Saving to files: ' + out_file + '.corpus.hl, ' + out_file + '.corpus.ll')
	while j <= limit:
		if args.debug:
			print str(j).zfill(len(str(limit)))+'/'+str(limit)+'\r',
			sys.stdout.flush()
		done = False
		hl_line = ''
		s = None
		Number.reset()
		while not done:
			try:
				s = Statements()
				# # verify postOrderUtil works:
				# import postOrderUtil
				# po_res = postOrderUtil.parse(s.po())
				# if (not po_res[0]) or (po_res[1].c().strip() != str(s).strip()):
				# 	print '\nError'
				# 	print '\t', s.po()
				# 	print '\t', str(s)
				# 	print '\t', ('False' if not po_res[0] else po_res[1].c())
				hl_line = re.sub('[ \t]+', ' ', preprocess_hl(s)).strip()
				if hl_line not in exclude:
					done = True
			except RuntimeError:
				pass
		# # print hl code
		# print str(s)
		exclude.add(hl_line)
		ll_line = re.sub('[ \t]+', ' ', compiler(s))
		if config.getboolean('Number', 'Abstract'):
			(ll_line, replacements) = generate_number_replacements(ll_line, config, hl2ll)
			hl_line = apply_number_replacements(hl_line, replacements)
		else:
			replacements = {}
		hl_line = hl_line.strip()
		ll_line = ll_line.strip()
		if (len(hl_line) > 0) and (len(ll_line) > 0):
			corpus_ll.append(ll_line)
			corpus_hl.append(hl_line)
			corpus_replacements.append(json.dumps(reverse_mapping(replacements)))
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
