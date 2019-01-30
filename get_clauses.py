import itertools


class HashableList(list):
	def __hash__(self):
		return hash(','.join(sorted(map(lambda x: str(x), self))))


class Num:
	def __init__(self, i, x):
		self.location = i
		self.value = x
		self.var = 'X'+str(i)

	def __str__(self):
		return self.var

	def __eq__(self, other):
		if not isinstance(other, Num):
			return False
		return self.value == other.value

	def __hash__(self):
		return hash(str(self))


class Op:
	def __init__(self, op1, op2, arg1, arg2, op, flatten=True):
		self.value = 0
		self.op1 = op1
		self.op2 = op2
		if not flatten:
			if isinstance(arg1, Op):
				self.args1 = set(['(' + str(arg1) + ')'])
			else:
				self.args1 = set([str(arg1)])
			if isinstance(arg2, Op):
				self.args2 = set(['(' + str(arg2) + ')'])
			else:
				self.args2 = set([str(arg2)])
		else:
			if isinstance(arg1, Op):
				if arg1.op1 == self.op1 and arg1.op2 == self.op2:
					self.args1 = arg1.args1.copy()
					self.args2 = arg1.args2.copy()
				else:
					self.args1 = set(['('+str(arg1)+')'])
					self.args2 = set()
			else:
				self.args1 = set([str(arg1)])
				self.args2 = set()
			if op == self.op1:
				if isinstance(arg2, Op):
					if arg2.op1 == self.op1 and arg2.op2 == self.op2:
						self.args1.update(arg2.args1)
						self.args2.update(arg2.args2)
					else:
						self.args1.update(['('+str(arg2)+')'])
				else:
					self.args1.update([str(arg2)])
			else:
				if isinstance(arg2, Op):
					if arg2.op1 == self.op1 and arg2.op2 == self.op2:
						self.args2.update(arg2.args1)
						self.args1.update(arg2.args2)
					else:
						self.args2.update(['(' + str(arg2) + ')'])
				else:
					self.args2.update([str(arg2)])

	def __str__(self):
		result = ''
		if self.op1 is not None:
			result += self.op1.join(sorted(self.args1))
		else:
			if len(self.args1) > 1:
				print 'Warning: lhs of mod has more than a single argument!'
			result += list(self.args1)[0]
		if len(self.args2) > 0:
			result += self.op2 + self.op2.join(sorted(self.args2))
		return result

	def __eq__(self, other):
		if not isinstance(other, Op):
			return False
		if self.op1 != other.op1:
			return False
		if self.op2 != other.op2:
			return False
		if self.args1 != other.args1:
			return False
		if self.args2 != other.args2:
			return False
		return True

	def __hash__(self):
		return hash(str(self))

	@staticmethod
	def isValid(lhs, rhs):
		return True


class Add(Op):
	def __init__(self, lhs, rhs):
		Op.__init__(self, '+', '-', lhs, rhs, '+')
		self.value = lhs.value + rhs.value


class Sub(Op):
	def __init__(self, lhs, rhs):
		Op.__init__(self, '+', '-', lhs, rhs, '-')
		self.value = lhs.value - rhs.value


class Mul(Op):
	def __init__(self, lhs, rhs):
		Op.__init__(self, '*', '/', lhs, rhs, '*')
		self.value = lhs.value * rhs.value


class Div(Op):
	def __init__(self, lhs, rhs):
		Op.__init__(self, '*', '/', lhs, rhs, '/')
		self.value = lhs.value / rhs.value

	@staticmethod
	def isValid(lhs, rhs):
		return rhs.value != 0


class Mod(Op):
	def __init__(self, lhs, rhs):
		Op.__init__(self, None, '%', lhs, rhs, '%', flatten=False)
		self.value = lhs.value % rhs.value

	@staticmethod
	def isValid(lhs, rhs):
		return rhs.value != 0


def get_possible_targets(target):
	targets = [target, target - 1, target + 1]
	if target > 0 and target <= 32:
		targets.append(2 ** target)
	return set(targets)

ops = [Add, Sub, Mul, Div]
MAX_START_VARS = 5
def get_clauses_vars(start_vars, target):
	if len(start_vars) == 0:
		return []
	if len(start_vars) > MAX_START_VARS:
		return []
	if reduce(lambda x, y: x*y, map(lambda v: v.value, start_vars), 1) < target:
		return []
	targets = get_possible_targets(target)
	worklist = set()
	done = set()
	clauses = []
	worklist.add(HashableList(start_vars))
	while len(worklist) > 0:
		vars = worklist.pop()
		done.add(vars)
		if len(vars) == 1:
			var = vars.pop()
			if var.value in [target]:
				if var not in clauses:
					clauses.append(var)
			continue
		all_pairs = filter(lambda (i, j): i < j, itertools.product(range(len(vars) - 1), range(1, len(vars))))
		for pair in all_pairs:
			var_pair = (vars[pair[0]], vars[pair[1]])
			new_ops = set(map(lambda op: op(*var_pair), filter(lambda op: op.isValid(*var_pair), ops)) + map(lambda op: op(*var_pair[::-1]), filter(lambda op: op.isValid(*var_pair[::-1]), ops)))
			rest_of_vars = map(lambda i: vars[i], filter(lambda j: j not in pair, range(len(vars))))
			for new_op in new_ops:
				new_vars = HashableList(rest_of_vars[:] + [new_op])
				if new_vars not in done:
					worklist.add(new_vars)
	return set(map(str, clauses))

def get_clauses(locations, nums, target):
	return get_clauses_vars(map(lambda (i,x): Num(i,x), zip(locations,nums)), target)


if __name__ == "__main__":
	# import time
	# for i in range(10):
	# 	locs = range(1, i + 1)
	# 	vals = range(1, i + 1)
	# 	tgt = sum(vals)
	# 	start = time.time()
	# 	get_clauses(locs, vals, tgt)
	# 	get_clauses(locs, vals, tgt)
	# 	get_clauses(locs, vals, tgt)
	# 	get_clauses(locs, vals, tgt)
	# 	res = get_clauses(locs, vals, tgt)
	# 	end = time.time()
	# 	print i, len(res), ((end - start) / 5.0)
	result = get_clauses([1,2,3,4], [1,2,3,4], 13)
	print result
	print len(result)