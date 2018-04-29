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
		self._statement_count = dict(
			map(lambda x: (x + 1, 0), range(config.getint('Assignments', 'MaxAssignments'))))
		self._ops = [Stats.OperatorCount('+', ['+']), Stats.OperatorCount('-', ['-']),
					 Stats.OperatorCount('*', ['*']),
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
		res += str(self._ifs) + ',' + "{0:.2f}".format(
			0.0 if self._num_inputs == 0 else (100.0 * self._ifs / float(self._num_inputs))) + ',' + str(
			self._elses) + ',' + "{0:.2f}".format(
			0.0 if self._num_inputs == 0 else (100.0 * self._elses / float(self._num_inputs))) + '\n'
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

def parse_stats(dataset):
	stats = Stats()
	with open(dataset + '.corpus.c', 'r') as fc:
		with open(dataset+'.corpus.ll', 'r') as fll:
			clines = fc.readlines()
			lllines = fll.readlines()
			assert len(clines) == len(lllines)
			for i in xrange(len(clines)):
				stats.updateStats(clines[i], lllines[i])
	with open(dataset + '.stats.csv', 'w') as f:
		f.write(str(stats))
