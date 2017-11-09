import random
import os
import sys
import ConfigParser
import ast
import argparse
import re


class SmartFormatter(argparse.HelpFormatter):
	def _split_lines(self, text, width):
		if text.startswith('R|'):
			return text[2:].splitlines()
		return argparse.HelpFormatter._split_lines(self, text, width)


parser = argparse.ArgumentParser(description="Generate random code samples", formatter_class=SmartFormatter)
parser.add_argument('-n', '--num', dest='n', type=int,
					help="R|number of samples to generate\n(if not given, generates samples until manually stopped)")
parser.add_argument('-o', '--out', dest='o', type=str, default='out',
					help="output files names (default: \'%(default)s\')")
parser.add_argument('-c', '--config', dest='c', type=str, default='configs/codenator.config',
					help="configuration file (default: \'%(default)s\')")
parser.add_argument('-po', '--post-order', dest='po', help="output c code in post order", action='count')

args = parser.parse_args()

config = ConfigParser.ConfigParser()
config.read(args.c)


class ParseTreeTemp:
	_counter = 0

	def __init__(self):
		self._name = 't' + str(ParseTreeTemp._counter)
		ParseTreeTemp._counter += 1

	def __str__(self):
		return self._name

	@staticmethod
	def resetCounter():
		ParseTreeTemp._counter = 0

	@staticmethod
	def updateCounter(n):
		ParseTreeTemp._counter += n


class Expr:
	@staticmethod
	def isValid():
		return True

	def collectVarNames(self):
		return set()

	def collectVars(self):
		return set()


class Number(Expr):
	_minNumber = config.getint('Number', 'MinValue')
	_maxNumber = config.getint('Number', 'MaxValue')

	def __init__(self):
		self._num = random.randint(Number._minNumber, Number._maxNumber)

	def __str__(self):
		return str(self._num)

	def po(self):
		return str(self._num)

	def __eq__(self, other):
		if not isinstance(other, Number):
			return False
		return other._num == self._num


class Var(Expr):
	_vars = []

	@staticmethod
	def clear():
		Var._vars = []

	@staticmethod
	def repopulate():
		def createVar(i):
			v = Var()
			v._name = 'X' + str(i)
			return v

		Var._vars = map(createVar, xrange(config.getint('Var', 'NumVars')))

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

	def collectVarNames(self):
		return set([self._name])

	def collectVars(self):
		return set([self])


class SourceVar(Var):
	def __init__(self):
		self._name = Var._vars[random.randrange(0, len(Var._vars))]._name

	@staticmethod
	def isValid():
		return len(Var._vars) > 0


class TargetVar(Var):
	# _threshold = 0.8
	# def __init__(self):
	#     if (random.uniform(0,1) <= TargetVar._threshold) or (len(Var._vars) == 0):
	#         self._name = 'X'+str(len(Var._vars))
	#         Var._vars.append(self)
	#     else:
	#         self._name = Var._vars[random.randrange(0, len(Var._vars))]._name
	_var = None

	@staticmethod
	def getTargetVar():
		if not TargetVar._var:
			TargetVar._var = Var()
			TargetVar._var._name = 'Y'
		return TargetVar._var


class Op(Expr):
	pass


class BinaryOp(Op):
	_Ops = ['+', '-', '*', '/', '%']

	def __init__(self):
		inner_weights = _inner_weights
		self._op1 = getExpr(inner_weights)
		self._act = BinaryOp._Ops[random.randrange(0, len(BinaryOp._Ops))]
		self._op2 = getExpr([0 if isinstance(self._op1, Number) else inner_weights[0]] + inner_weights[1:])
		while (self._op2 == self._op1) or ((self._act == '/') and isinstance(self._op2, Number) and (
					self._op2._num == 0)):  # or (isinstance(self._op1,Number) and isinstance(self._op2,Number)):
			self._op2 = getExpr([0 if isinstance(self._op1, Number) else inner_weights[0]] + inner_weights[1:])

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

	def collectVarNames(self):
		return self._op1.collectVarNames().union(self._op2.collectVarNames())

	def collectVars(self):
		return self._op1.collectVars().union(self._op2.collectVars())


class UnaryOp(Op):
	_Ops = ['++', '--']

	def __init__(self):
		self._op = SourceVar()
		self._act = UnaryOp._Ops[random.randint(0, 1)]
		self._position = (random.randint(0, 1) == 1)

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

	def collectVarNames(self):
		return self._op.collectVarNames()

	def collectVars(self):
		return self._op.collectVars()


class Assignment:
	def __init__(self, i):
		self._source = getExpr()
		self._target = TargetVar.getTargetVar()
		if config.getboolean('Assignments', 'RenameTargetVars'):
			target_name = self._target._name + str(i)
			self._target = Var()
			self._target._name = target_name

	def __str__(self):
		return str(self._target) + ' = ' + str(self._source) + ' ; '

	def po(self):
		return self._target.po() + ' ' + self._source.po() + ' ='

	def __eq__(self, other):
		if not isinstance(other, Assignment):
			return False
		return other._source == self._source

	def collectVarNames(self):
		return self._source.collectVarNames().union(self._target.collectVarNames())

	def collectVars(self):
		return self._source.collectVars()


class Condition:
	_Relations = ['>', '>=', '<', '<=', '==', '!=']

	def __init__(self):
		inner_weights = _inner_weights
		self._op1 = getExpr(inner_weights)
		self._act = Condition._Relations[random.randrange(0, len(Condition._Relations))]
		self._op2 = getExpr([0 if isinstance(self._op1, Number) else inner_weights[0]] + inner_weights[1:])
		while (self._op2 == self._op1):  # or (isinstance(self._op1, Number) and isinstance(self._op2, Number)):
			self._op2 = getExpr([0 if isinstance(self._op1, Number) else inner_weights[0]] + inner_weights[1:])

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
		if not isinstance(other, Condition):
			return False
		return (other._act == self._act) and (other._op1 == self._op1) and (other._op2 == self._op2)

	def collectVarNames(self):
		return self._op1.collectVarNames().union(self._op2.collectVarNames())

	def collectVars(self):
		return self._op1.collectVars().union(self._op2.collectVars())


class Assignments:
	_max_statements = config.getint('Assignments', 'MaxAssignments')
	_statements_weights = ast.literal_eval(config.get('Assignments', 'Weights'))
	_assignments_counter = 0

	@staticmethod
	def getAssignments(max_statements=_max_statements, statements_weights=_statements_weights):
		num_statements_weights = reduce(lambda x, y: x + y,
										map(lambda i: [i + 1] * statements_weights[i], range(max_statements)), [])
		num_statements = num_statements_weights[random.randrange(0, len(num_statements_weights))]
		result = map(lambda i: Assignment(Assignments._assignments_counter + i), range(num_statements))
		Assignments._assignments_counter += num_statements
		return result

	@staticmethod
	def resetCounter():
		Assignments._assignments_counter = 0


class Statements:
	_branchRatio = config.getfloat('Statements', 'BranchRatio')

	@staticmethod
	def getStatements(max_statements=Assignments._max_statements, statements_weights=Assignments._statements_weights):
		if random.random() >= Statements._branchRatio:
			return Assignments.getAssignments(max_statements, statements_weights)
		else:
			return [Branch()]


class Branch:
	_elseRatio = config.getfloat('Branch', 'ElseRatio')
	_max_inner_statements = config.getint('Branch', 'MaxInnerAssignments')
	_inner_statements_weights = ast.literal_eval(config.get('Branch', 'InnerWeights'))
	_allow_nested = config.getboolean('Branch', 'AllowNested')
	_branch_counter = 0;

	def __init__(self):
		self._cond = Condition()

		def body_generator():
			return Statements.getStatements(Branch._max_inner_statements,
											Branch._inner_statements_weights) if Branch._allow_nested else Assignments.getAssignments(
				Branch._max_inner_statements, Branch._inner_statements_weights)

		self._if = body_generator()
		if random.random() > Branch._elseRatio:
			self._else = body_generator()
			while (self._else == self._if):
				self._else = body_generator()
		else:
			self._else = None

	@staticmethod
	def resetCounter():
		Branch._branch_counter = 0

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
		res = 'if ( ' + str(self._cond) + ' ) { ' + ' '.join(map(lambda x: str(x), self._if)) + ' } '
		if self._else:
			res += 'else { ' + ' '.join(map(lambda x: str(x), self._else)) + ' } '
		return res

	def po(self):
		separator = ' ; ' if config.getboolean('PostOrder', 'AppendSemicolon') else ' '
		return self._cond.po() + ' COND ' + separator.join(map(lambda x: x.po(), self._if) + ['']) + 'TRUE ' + (
			separator.join(map(lambda x: x.po(), self._else) + ['']) + 'FALSE ' if self._else else '') + 'IF'

	def collectVarNames(self):
		_if = reduce(lambda y, z: y.union(z), map(lambda x: x.collectVarNames(), self._if), set())
		_else = reduce(lambda y, z: y.union(z), map(lambda x: x.collectVarNames(), self._else), set())
		return _if.union(_else)

	def collectVars(self):
		_if = reduce(lambda y, z: y.union(z), map(lambda x: x.collectVars(), self._if), set())
		_else = reduce(lambda y, z: y.union(z), map(lambda x: x.collectVars(), self._else), set())
		return _if.union(_else)


class Init:
	def __str__(self):
		if len(Var._vars) == 0:
			return ''
		vars = ','.join(map(lambda x: str(x), Var._vars))
		return 'int ' + vars + ' ;\n'


_exprs = [Number, SourceVar, BinaryOp, UnaryOp]
_weights = map(lambda e: config.getint(e.__name__, 'Weight'), _exprs)
_inner_weights = map(lambda e: config.getint(e.__name__, 'InnerWeight'), _exprs)


def getExpr(weights=_weights):
	assert len(weights) == len(_exprs)
	exprs = []
	for i in range(len(weights)):
		exprs += [_exprs[i]] * weights[i]
	random.shuffle(exprs)
	expr = exprs[random.randrange(0, len(exprs))]
	while not expr.isValid():
		expr = exprs[random.randrange(0, len(exprs))]
	return expr()


class Stats:
	class OperatorCount:
		def __init__(self, name, op):
			self._name = name
			self._op = op
			self._total = 0
			self._statements = 0
			self._inputs = 0

		def updateCounts(self, s):
			self._total += sum(map(lambda o: s.count(' ' + o + ' '), self._op))
			self._statements += sum(
				map(lambda x: 1 if len(filter(lambda o: ' ' + o + ' ' in x, self._op)) > 0 else 0, s.split(';')))
			self._inputs += 1 if len(filter(lambda o: ' ' + o + ' ' in s, self._op)) > 0 else 0

		def toString(self, count_inputs, count_statemtns, count_total):
			return self._name + ',' + str(self._inputs) + ',' + "{0:.2f}".format(
				100.0 * self._inputs / float(count_inputs) if count_inputs > 0 else 0.0) + ',' + str(
				self._statements) + ',' + "{0:.2f}".format(
				100.0 * self._statements / float(count_statemtns) if count_statemtns > 0 else 0.0) + ',' + str(
				self._total) + ',' + "{0:.2f}".format(
				100.0 * self._total / float(count_total) if count_total > 0 else 0.0)

	class Counter:
		def __init__(self, f):
			self._f = f
			self._min = None
			self._max = None

		def updateCounts(self, s):
			val = self._f(s)
			if self._min:
				self._min = min(self._min, val)
			else:
				self._min = val
			if self._max:
				self._max = max(self._max, val)
			else:
				self._max = val

		def __str__(self):
			return str(self._min) + ',' + str(self._max)

	class LengthCounter(Counter):
		def __init__(self):
			Stats.Counter.__init__(self, lambda x: len(filter(lambda x: x != ' ', list(x.strip()))))

	class StatementsCounter(Counter):
		def __init__(self):
			Stats.Counter.__init__(self, lambda x: x.count(';'))

	class WordCounter(Counter):
		def __init__(self):
			Stats.Counter.__init__(self, lambda x: x.strip().count(' ') + 1)

	def __init__(self):
		self._num_inputs = 0
		self._num_statements = 0
		self._ifs = 0
		self._elses = 0
		self._statement_count = dict(map(lambda x: (x + 1, 0), range(config.getint('Assignments', 'MaxAssignments'))))
		self._ops = [Stats.OperatorCount('+', ['+']), Stats.OperatorCount('-', ['-']), Stats.OperatorCount('*', ['*']),
					 Stats.OperatorCount('/', ['/']), Stats.OperatorCount('%', ['%']),
					 Stats.OperatorCount('++', ['++']), Stats.OperatorCount('--', ['--']),
					 Stats.OperatorCount('Binary', ['+', '-', '*', '/', '%']),
					 Stats.OperatorCount('Unary', ['++', '--']),
					 Stats.OperatorCount('All', ['+', '-', '*', '/', '%', '++', '--'])]
		self._c_statement_length = Stats.LengthCounter()
		self._ir_statement_length = Stats.LengthCounter()
		self._c_statement_count = Stats.StatementsCounter()
		self._ir_statement_count = Stats.StatementsCounter()
		self._c_word_count = Stats.WordCounter()
		self._ir_word_count = Stats.WordCounter()

	def updateStats(self, c, ll):
		self._num_inputs += 1
		self._num_statements += c.count(';')
		if '} else {' not in c:
			self._statement_count[c.count(';')] += 1
		else:
			tmp = c.split('} else {')
			self._statement_count[tmp[0].count(';')] += 1
			self._statement_count[tmp[1].count(';')] += 1
		if c.startswith('if'):
			self._ifs += 1
		if '} else {' in c:
			self._elses += 1
		map(lambda o: o.updateCounts(c), self._ops)
		self._c_statement_length.updateCounts(c)
		self._c_statement_count.updateCounts(c)
		self._c_word_count.updateCounts(c)
		self._ir_statement_length.updateCounts(ll)
		self._ir_statement_count.updateCounts(ll)
		self._ir_word_count.updateCounts(ll)

	def __str__(self):
		res = ''
		res += '[General]\n'
		res += 'Inputs,' + str(self._num_inputs) + '\n'
		res += 'Statements,' + str(self._num_statements) + '\n'
		res += '\n[Branches]\n'
		res += 'If,%,Else,%\n'
		res += str(self._ifs) + ',' + "{0:.2f}".format(100.0 * self._ifs / float(self._num_inputs)) + ',' + str(
			self._elses) + ',' + "{0:.2f}".format(100.0 * self._elses / float(self._num_inputs)) + '\n'
		res += '\n[Lengths]\n'
		res += ',Min,Max\n'
		res += 'C,' + str(self._c_statement_length) + '\n'
		res += 'IR,' + str(self._ir_statement_length) + '\n'
		res += '\n[Statements]\n'
		res += ',Min,Max\n'
		res += 'C,' + str(self._c_statement_count) + '\n'
		res += 'IR,' + str(self._ir_statement_count) + '\n'
		res += '\n[Word Counts]\n'
		res += ',Min,Max\n'
		res += 'C,' + str(self._c_word_count) + '\n'
		res += 'IR,' + str(self._ir_word_count) + '\n'
		res += '\n[Operators]\n'
		res += ',Samples,%,Statements,%,Total,t%\n'
		res += '\n'.join(map(lambda x: x.toString(self._num_inputs, self._num_statements, self._ops[-1]._total),
							 self._ops[:-1])) + '\n'
		res += '\n[Statements]\n'
		res += 'Num,Count,%\n'
		res += '\n'.join(map(lambda x: str(x) + ',' + str(self._statement_count[x]) + ',' + "{0:.2f}".format(
			100.0 * self._statement_count[x] / float(self._num_inputs) if self._num_inputs > 0 else 0.0),
							 range(1, config.getint('Assignments', 'MaxAssignments') + 1)))
		return res


def generateStatements():
	if args.n:
		limit = args.n
		limited = True
	else:
		limit = 0
		limited = False
	outFile = args.o
	# from cleanup import cleanup
	# cleanup(outDir)
	if limited:
		print 'Generating ' + str(limit) + ' statements'
	else:
		print 'Generating statements until manually stopped (ctrl+C)'
	print 'Saving to files: ' + outFile + '.corpus.c, ' + outFile + '.corpus.ll'+(', '+outFile+'.corpus.po' if args.po else '')
	print ''
	j = 1
	vocabc = set()
	vocabir = set()
	if args.po:
		vocabpo = set()
		corpuspo = open(outFile + '.corpus.po', 'w')
	stats = Stats()
	with open(outFile + '.corpus.c', 'w') as corpusc:
		with open(outFile + '.corpus.ll', 'w') as corpusir:
			Var.clear()
			Var.repopulate()
			statements = set()
			while (not limited) or (j <= limit):
				ParseTreeTemp.resetCounter()
				Branch.resetCounter()
				print '\r\t' + str(j),
				if limited:
					print '/' + str(limit),
				sys.stdout.flush()
				Assignments.resetCounter()
				done = False
				while not done:
					try:
						s = Statements.getStatements()
						if config.getboolean('General', 'SimplifyVars'):
							for x in s:
								k = 0
								for v in x.collectVars():
									v._name = 'X' + str(k)
									k += 1
						if ' '.join(map(lambda x: str(x), s)) not in statements:
							done = True
					except RuntimeError:
						pass
				statements.add(' '.join(map(lambda x: str(x), s)))
				separator = ' ; ' if config.getboolean('LLVM', 'AppendSemicolon') else ' '
				with open('tmp'+str(os.getpid())+'.c', 'w') as f:
					f.write('int ' + ('Y' if not config.getboolean('Assignments', 'RenameTargetVars') else ','.join(
						map(lambda i: 'Y' + str(i), range(Assignments._assignments_counter)))) + ','.join(
						[''] + map(lambda v: v._name, Var._vars)) + ';\n')
					f.write('void f() {\n')
					for x in s:
						f.write(str(x) + '\n')
					f.write('}\n')
				os.system('clang -S -emit-llvm -O' + str(
					config.getint('General', 'OptimizationLevel')) + ' -o tmp'+str(os.getpid())+'.ll tmp'+str(os.getpid())+'.c > /dev/null 2>&1')
				with open('tmp'+str(os.getpid())+'.ll', 'r') as f:
					lines = [l.strip() for l in f.readlines()]
				splitlines = []
				for l in lines:
					splitlines += l.split(' ; ')
				lines = splitlines
				start = min(filter(lambda i: lines[i].startswith('define') and 'f()' in lines[i], range(len(lines))))
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
						if config.getboolean('Branch', 'RemovePreds'):
							if line.startswith('preds '):
								continue
						if config.getboolean('Branch', 'SimplifyLabels'):
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
						if config.getboolean('General', 'RemoveAlign4'):
							if line.endswith(', align 4'):
								line = line[:-len(', align 4')].strip()
						if config.getboolean('General', 'RemoveI32'):
							line = re.sub('i32\*? ', '', line)
						vocabir.update(map(lambda y: y.strip(), line.split(' ')))
						llline += line + separator
				cline = ''
				for x in s:
					cline += str(x)
				cline += '\n'
				corpusc.write(cline)
				vocabc.update(map(lambda x: x.strip(), cline.split(' ')))
				corpusir.write(llline + '\n')
				stats.updateStats(cline, llline)
				os.remove('tmp'+str(os.getpid())+'.c')
				os.remove('tmp'+str(os.getpid())+'.ll')
				if args.po:
					separator = ' ; ' if config.getboolean('PostOrder', 'AppendSemicolon') else ' '
					line = ''
					for x in s:
						line += x.po() + separator
					line += '\n'
					corpuspo.write(line)
					vocabpo.update(map(lambda x: x.strip(), line.split(' ')))
				j += 1
	with open(outFile + '.vocab.c.json', 'w') as f:
		f.write('{\n')
		f.write('  "eos": 0, \n')
		f.write('  "UNK": 1, \n')
		i = 0
		n = len(vocabc)
		for w in vocabc:
			f.write('  "' + w + '": ' + str(i + 2))
			i += 1
			if i != n:
				f.write(', ')
			f.write('\n')
		f.write('}')
	with open(outFile + '.vocab.ll.json', 'w') as f:
		f.write('{\n')
		f.write('  "eos": 0, \n')
		f.write('  "UNK": 1, \n')
		i = 0
		n = len(vocabir)
		for w in vocabir:
			f.write('  "' + w + '": ' + str(i + 2))
			i += 1
			if i != n:
				f.write(', ')
			f.write('\n')
		f.write('}')
	if args.po:
		corpuspo.close()
		with open(outFile + '.vocab.po.json', 'w') as f:
			f.write('{\n')
			f.write('  "eos": 0, \n')
			f.write('  "UNK": 1, \n')
			i = 0
			n = len(vocabpo)
			for w in vocabpo:
				f.write('  "' + w + '": ' + str(i + 2))
				i += 1
				if i != n:
					f.write(', ')
				f.write('\n')
			f.write('}')
	with open(outFile + '.stats.csv', 'w') as f:
		f.write(str(stats))
	print '\nDone!\n'


if __name__ == "__main__":
	generateStatements()
