import re
import itertools

class Instruction:
	def __init__(self, code):
		self.code = code
		self.is_jump = False
		self.is_label = False
		self.targets = []
		self.defines = None
		self.is_branch = False
		self.condition = None
		self.is_condition = False
		self.uses = []
		self.is_symmetric = False
		self.parse_instruction(code)

	def parse_instruction(self, code):
		if code in ['__entry__', '__exit__']:
			self.op = code
			return
		if re.match('^<label>:[0-9]+$', code):
			self.is_label = True
			return
		if code.startswith('br '):
			self.is_jump = True
			self.op = 'br'
			code = code[3:]
			if ',' in self.code:
				self.is_branch = True
				parts = map(lambda x: x.strip(), code.split(','))
				labels = parts[1:]
				self.condition = parts[0]
				self.uses.append(self.condition)
			else:
				labels = [code]
			self.targets = ['<label>:'+x[8:] for x in labels]
		elif code.startswith('store'):
			code = code[6:]
			parts = map(lambda x: x.strip(), code.split(','))
			self.op = 'store'
			self.defines = parts[1]
			self.uses.append(parts[0])
		elif ' = ' in self.code:
			self.defines = self.code.split(' = ')[0].strip()
			code = code[code.index('=')+1:].strip()
			self.op = code[:code.index(' ')]
			if code.startswith('load'):
				self.uses.append(code.split(',')[1].strip())
			else:
				code = code[len(self.op)+1:].strip()
				if self.op == 'icmp':
					self.is_condition = True
					self.relation = code[:code.index(' ')]
					code = code[len(self.relation)+1:].strip()
				self.uses += map(lambda x: x.strip(), code.split(','))
				# normalize conditions
				if self.is_condition:
					if self.relation in ['sgt', 'sge']:
						self.relation = 'sl' + self.relation[2]
						self.uses.reverse()
				if self.op in ['add', 'mul'] or (self.is_condition and self.relation in ['eq', 'ne']):
					self.is_symmetric = True


class Graph:
	def __init__(self, code):
		# remove garbage
		cleaned_code = ' __entry__ ; ' + re.sub('i32\*?', '', re.sub('i1', '', code)).replace('  ', ' ') + ' __exit__ ; '
		# parse code
		split_code = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), cleaned_code.split(';')))
		self.instructions = dict(zip(range(len(split_code)), [Instruction(c) for c in split_code]))
		# build cfg
		self.childs = dict([(i, []) for i in self.instructions])
		self.parents = dict([(i, []) for i in self.instructions])
		for i in self.instructions:
			if self.instructions[i].is_jump:
				for label in self.instructions[i].targets:
					index = filter(lambda j: self.instructions[j].code == label, self.instructions)[0]
					self.childs[i].append(index)
					self.parents[index].append(i)
			else:
				if (i+1) in self.instructions:
					self.childs[i].append(i+1)
					self.parents[i+1].append(i)
		# clean cfg
		redundant = filter(lambda i: (self.instructions[i].is_jump and not self.instructions[i].is_branch) or self.instructions[i].is_label, self.instructions.keys())
		for j in redundant:
			childs = self.childs[j][:]
			parents = self.parents[j][:]
			for c in childs:
				self.parents[c].remove(j)
				self.parents[c] += parents
			for p in parents:
				self.childs[p].remove(j)
				self.childs[p] += childs
			del self.childs[j]
			del self.parents[j]
			del self.instructions[j]
		# build ddg
		ddg_init = dict([(i, set()) for i in self.instructions])
		ddg_gen = dict(map(lambda i: (i, [(self.instructions[i].defines, i)]) if self.instructions[i].defines is not None else (i, []), self.instructions))
		ddg_kill = dict(map(lambda i: (i, [(self.instructions[i].defines, j) for j in self.instructions]) if self.instructions[i].defines is not None else (i, []), self.instructions))
		self.reaching_definitions = self.get_fixed_point(ddg_init, ddg_gen, ddg_kill, set.union, self.parents, self.childs)
		self.ddg = dict(map(lambda i: (i, map(lambda u: map(lambda y: y[1], filter(lambda x: x[0] == u, self.reaching_definitions[i])), self.instructions[i].uses)), self.instructions))
		# compute dominators
		dom_init = dict([(i, set(self.instructions.keys())) for i in self.instructions])
		last_instruction = max(self.instructions.keys())
		dom_init[last_instruction] = set([last_instruction])
		dom_gen = dict([(i, [i]) for i in self.instructions])
		dom_kill = dict([(i, []) for i in self.instructions])
		self.post_dominators = self.get_fixed_point(dom_init, dom_gen, dom_kill, set.intersection, self.childs, self.parents)
		self.immediate_post_dominators = {}
		for i in self.post_dominators:
			post_dominators = self.post_dominators[i]
			if len(post_dominators) > 0:
				self.immediate_post_dominators[i] = filter(lambda d: all(map(lambda x: d not in self.post_dominators[x], post_dominators)), post_dominators)[0]
			else:
				self.immediate_post_dominators[i] = None
		self.cdg = dict([(i, set()) for i in self.instructions])
		branches = filter(lambda i: self.instructions[i].is_branch, self.instructions)
		for b in branches:
			immediate_post_dominator = self.immediate_post_dominators[b]
			reachable = set()
			new_reachable = set(filter(lambda c: c != immediate_post_dominator, self.childs[b]))
			while new_reachable != reachable:
				reachable = new_reachable
				new_reachable = set(filter(lambda c: c != immediate_post_dominator, reachable.union(*map(lambda x: self.childs[x], reachable))))
			for r in reachable:
				self.cdg[r].add(b)


	def get_fixed_point(self, init, gen, kill, merge, predecessors, successors):
		in_states = {}
		out_states = init
		worklist = set(self.instructions.keys())
		while len(worklist) > 0:
			i = worklist.pop()
			if len(predecessors[i]) > 0:
				states = [out_states[p] for p in predecessors[i]]
				new_in_state = set(merge(*states))
			else:
				new_in_state = set()
			new_out_state = set(filter(lambda x: x not in kill[i], new_in_state)).union(gen[i])
			in_states[i] = new_in_state
			if new_out_state != out_states[i]:
				out_states[i] = new_out_state
				worklist.update(successors[i])
		return in_states

	def print_code(self):
		for i in sorted(self.instructions.keys()):
			print i, self.instructions[i].code


def compare_graphs(graph1, graph2):
	if len(graph1.instructions) != len(graph2.instructions):
		return False
	def is_matching_instructions(index1, index2):
		def is_number(x):
			return re.match('^\-?[0-9]+$', x) or re.match('^N[0-9]+$', x)
		inst1 = graph1.instructions[index1]
		inst2 = graph2.instructions[index2]
		if inst1.op != inst2.op:
			return False
		if inst1.is_condition:
			if inst1.relation != inst2.relation:
				return False
		if inst1.op == 'store':
			if inst1.defines != inst2.defines:
				return False
		if inst1.op == 'load':
			if inst1.uses != inst2.uses:
				return False
		if len(inst1.uses) != len(inst2.uses):
			return False
		numeric_args1 = len(filter(is_number, inst1.uses))
		numeric_args2 = len(filter(is_number, inst2.uses))
		if numeric_args1 != numeric_args2:
			return False
		if inst1.is_symmetric:
			func = itertools.product
		else:
			func = zip
		args = func(inst1.uses, inst2.uses)
		matching_numeric_args = len(filter(lambda (x, y): is_number(x) and (x == y), args))
		expected_numeric_args_pairs = 4 if ((numeric_args1 == 2) and (inst1.uses[0] == inst1.uses[1])) else numeric_args1
		if expected_numeric_args_pairs != matching_numeric_args:
			return False
		cdg1 = graph1.cdg[index1]
		cdg2 = graph2.cdg[index2]
		if len(cdg1) != len(cdg2):
			return False
		ddg1 = graph1.ddg[index1]
		ddg2 = graph2.ddg[index2]
		if len(ddg1) != len(ddg2):
			return False
		if sorted(map(len,ddg1)) != sorted(map(len,ddg2)):
			return False
		return True
	def generate_all_dependency_pairs(index1, index2):
		cdg1 = graph1.cdg[index1]
		cdg2 = graph2.cdg[index2]
		dependency_pairs = set(list(itertools.product(cdg1, cdg2)))
		ddg1 = graph1.ddg[index1]
		ddg2 = graph2.ddg[index2]
		if graph1.instructions[index1].is_symmetric:
			func = itertools.product
		else:
			func = zip
		for (x,y) in func(ddg1, ddg2):
			if len(x) == len(y):
				dependency_pairs.update(list(itertools.product(x, y)))
		return len(set(map(lambda x: x[0], dependency_pairs))), dependency_pairs
	all_pairs = itertools.product(graph1.instructions.keys(), graph2.instructions.keys())
	initial_pairs = filter(lambda (x, y): is_matching_instructions(x, y), all_pairs)
	pairs_dependencies = dict(map(lambda p: (p, generate_all_dependency_pairs(*p)), initial_pairs))
	changed = True
	while changed:
		changed = False
		for pair in pairs_dependencies.keys():
			dependencies = pairs_dependencies[pair][1]
			required_matches = pairs_dependencies[pair][0]
			dependencies = set(filter(lambda p: p in pairs_dependencies.keys(), dependencies))
			lhs_count = len(set(map(lambda x: x[0], dependencies)))
			rhs_count = len(set(map(lambda x: x[1], dependencies)))
			if (lhs_count >= required_matches) and (rhs_count >= required_matches):
				pairs_dependencies[pair] = (required_matches, dependencies)
			else:
				changed = True
				del pairs_dependencies[pair]
	if set(map(lambda x: x[0], pairs_dependencies.keys())) != set(graph1.instructions.keys()):
		return False
	if set(map(lambda x: x[1], pairs_dependencies.keys())) != set(graph2.instructions.keys()):
		return False
	return True


def compare_codes(code1, code2):
	return compare_graphs(Graph(code1), Graph(code2))


if __name__ == "__main__":
	results = []
	x = '%1 = load i32 , i32* @X3 ; %2 = load i32 , i32* @X10 ; %3 = mul i32 %2 , N0 ; %4 = mul i32 %1 , %3 ; store i32 %4 , i32* @X11 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X0 ; %3 = load i32 , i32* @X7 ; %4 = icmp sgt i32 %2 , %3 ; br i1 %4 , <label>%1 , <label>%2 ; <label>:1 ; %6 = load i32 , i32* @X8 ; %7 = sdiv i32 N16 , %6 ; %8 = load i32 , i32* @X7 ; %9 = sub i32 N19 , %8 ; %10 = sub i32 %7 , %9 ; %11 = load i32 , i32* @X11 ; %12 = add i32 %11 , -1 ; store i32 %12 , i32* @X11 ; %13 = mul i32 %10 , %12 ; store i32 %13 , i32* @X1 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X13 ; %2 = add i32 %1 , 1 ; store i32 %2 , i32* @X13 ; %3 = sub i32 N11 , %2 ; store i32 %3 , i32* @X7 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X1 ; %2 = load i32 , i32* @X13 ; %3 = srem i32 %1 , %2 ; %4 = add i32 N12 , %3 ; store i32 %4 , i32* @X5 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X3 ; store i32 %1 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X8 ; store i32 %1 , i32* @X6 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X7 ; %3 = load i32 , i32* @X12 ; %4 = add i32 %2 , %3 ; %5 = load i32 , i32* @X4 ; %6 = icmp sgt i32 %4 , %5 ; br i1 %6 , <label>%1 , <label>%2 ; <label>:1 ; %8 = load i32 , i32* @X13 ; %9 = load i32 , i32* @X9 ; %10 = sub i32 %8 , %9 ; %11 = mul i32 %10 , N1 ; %12 = load i32 , i32* @X13 ; %13 = add i32 %12 , -1 ; store i32 %13 , i32* @X13 ; %14 = add i32 %11 , %12 ; %15 = load i32 , i32* @X13 ; %16 = sdiv i32 N9 , %15 ; %17 = add i32 %14 , %16 ; %18 = add i32 N1 , %17 ; store i32 %18 , i32* @X10 ; br <label>%0 ; <label>:2 ; %20 = load i32 , i32* @X13 ; %21 = srem i32 N11 , %20 ; store i32 %21 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X14 ; %2 = load i32 , i32* @X7 ; %3 = mul i32 %1 , %2 ; store i32 %3 , i32* @X4 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N10 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X9 ; %2 = load i32 , i32* @X2 ; %3 = sub i32 %2 , N15 ; %4 = srem i32 N1 , %3 ; %5 = add i32 %1 , %4 ; %6 = load i32 , i32* @X12 ; %7 = icmp slt i32 %5 , %6 ; br i1 %7 , <label>%0 , <label>%1 ; <label>:0 ; %9 = load i32 , i32* @X9 ; %10 = load i32 , i32* @X0 ; %11 = sdiv i32 %10 , N18 ; %12 = mul i32 %9 , %11 ; %13 = load i32 , i32* @X0 ; %14 = add i32 %13 , 1 ; store i32 %14 , i32* @X0 ; %15 = add i32 %13 , N10 ; %16 = load i32 , i32* @X7 ; %17 = load i32 , i32* @X11 ; %18 = mul i32 %16 , %17 ; %19 = srem i32 N2 , %18 ; %20 = mul i32 %15 , %19 ; %21 = srem i32 %12 , %20 ; store i32 %21 , i32* @X6 ; br <label>%2 ; <label>:1 ; %23 = load i32 , i32* @X13 ; %24 = load i32 , i32* @X14 ; %25 = srem i32 %23 , %24 ; %26 = sdiv i32 %25 , N4 ; %27 = load i32 , i32* @X2 ; %28 = load i32 , i32* @X4 ; %29 = sub i32 %27 , %28 ; %30 = mul i32 N14 , %29 ; %31 = load i32 , i32* @X7 ; %32 = mul i32 %30 , %31 ; %33 = sub i32 %26 , %32 ; store i32 %33 , i32* @X6 ; br <label>%2 ; <label>:2 ; %35 = load i32 , i32* @X14 ; %36 = add i32 %35 , N15 ; %37 = srem i32 %36 , N3 ; %38 = load i32 , i32* @X12 ; %39 = add i32 %38 , N8 ; %40 = sub i32 N3 , %39 ; %41 = mul i32 %37 , %40 ; store i32 %41 , i32* @X10 ; %42 = load i32 , i32* @X1 ; %43 = add i32 %42 , 1 ; store i32 %43 , i32* @X1 ; store i32 %43 , i32* @X1 ; %44 = load i32 , i32* @X14 ; store i32 %44 , i32* @X14 ; store i32 N10 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X6 ; %2 = mul i32 N6 , %1 ; %3 = load i32 , i32* @X9 ; %4 = mul i32 %3 , N17 ; %5 = add i32 N19 , %4 ; %6 = sdiv i32 N8 , %5 ; %7 = mul i32 %2 , %6 ; store i32 %7 , i32* @X7 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N5 , i32* @X8 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X4 ; %2 = load i32 , i32* @X6 ; %3 = mul i32 %1 , %2 ; %4 = sdiv i32 N0 , %3 ; %5 = mul i32 N14 , %4 ; %6 = load i32 , i32* @X2 ; %7 = add i32 %5 , %6 ; store i32 %7 , i32* @X8 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N3 , i32* @X1 ; %1 = load i32 , i32* @X1 ; %2 = load i32 , i32* @X8 ; %3 = load i32 , i32* @X12 ; %4 = sub i32 N9 , %3 ; %5 = add i32 %2 , %4 ; %6 = sdiv i32 %1 , %5 ; store i32 %6 , i32* @X14 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X13 ; %2 = add i32 %1 , -1 ; store i32 %2 , i32* @X13 ; store i32 %2 , i32* @X5 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X2 ; %2 = mul i32 N9 , %1 ; %3 = add i32 %2 , N6 ; store i32 %3 , i32* @X3 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X5 ; %2 = load i32 , i32* @X12 ; %3 = load i32 , i32* @X3 ; %4 = mul i32 %2 , %3 ; %5 = load i32 , i32* @X7 ; %6 = sub i32 %4 , %5 ; %7 = icmp slt i32 %1 , %6 ; br i1 %7 , <label>%0 , <label>%1 ; <label>:0 ; %9 = load i32 , i32* @X3 ; %10 = load i32 , i32* @X4 ; %11 = add i32 %9 , %10 ; %12 = sdiv i32 N17 , %11 ; %13 = load i32 , i32* @X8 ; %14 = sdiv i32 %12 , %13 ; %15 = load i32 , i32* @X6 ; %16 = sdiv i32 %14 , %15 ; store i32 %16 , i32* @X0 ; %17 = load i32 , i32* @X14 ; %18 = load i32 , i32* @X8 ; %19 = sdiv i32 %18 , N1 ; %20 = sub i32 %17 , %19 ; store i32 %20 , i32* @X11 ; br <label>%2 ; <label>:1 ; %22 = load i32 , i32* @X5 ; %23 = load i32 , i32* @X12 ; %24 = load i32 , i32* @X3 ; %25 = srem i32 %23 , %24 ; %26 = sdiv i32 N3 , %25 ; %27 = load i32 , i32* @X4 ; %28 = mul i32 %26 , %27 ; %29 = sdiv i32 N14 , %28 ; %30 = sdiv i32 %22 , %29 ; store i32 %30 , i32* @X12 ; br <label>%2 ; <label>:2 ; %32 = load i32 , i32* @X11 ; %33 = sub i32 N10 , %32 ; store i32 %33 , i32* @X14 ; %34 = load i32 , i32* @X10 ; %35 = load i32 , i32* @X3 ; %36 = srem i32 %34 , %35 ; %37 = load i32 , i32* @X2 ; %38 = add i32 N15 , %37 ; %39 = srem i32 %36 , %38 ; %40 = add i32 N14 , %39 ; store i32 %40 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X3 ; %2 = load i32 , i32* @X7 ; %3 = mul i32 %1 , %2 ; %4 = load i32 , i32* @X5 ; %5 = srem i32 %4 , N8 ; %6 = add i32 N9 , %5 ; %7 = load i32 , i32* @X9 ; %8 = mul i32 N0 , %7 ; %9 = srem i32 %6 , %8 ; %10 = icmp sge i32 %3 , %9 ; br i1 %10 , <label>%0 , <label>%1 ; <label>:0 ; %12 = load i32 , i32* @X11 ; store i32 %12 , i32* @X11 ; br <label>%2 ; <label>:1 ; %14 = load i32 , i32* @X2 ; %15 = add i32 N2 , %14 ; %16 = load i32 , i32* @X1 ; %17 = srem i32 N5 , %16 ; %18 = load i32 , i32* @X9 ; %19 = add i32 %17 , %18 ; %20 = mul i32 %15 , %19 ; store i32 %20 , i32* @X2 ; br <label>%2 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X14 ; %3 = icmp slt i32 N9 , %2 ; br i1 %3 , <label>%1 , <label>%2 ; <label>:1 ; %5 = load i32 , i32* @X9 ; %6 = load i32 , i32* @X8 ; %7 = sdiv i32 N10 , %6 ; %8 = sdiv i32 %5 , %7 ; %9 = srem i32 %8 , N18 ; %10 = load i32 , i32* @X13 ; %11 = load i32 , i32* @X6 ; %12 = sub i32 %10 , %11 ; %13 = sdiv i32 N11 , %12 ; %14 = load i32 , i32* @X2 ; %15 = load i32 , i32* @X6 ; %16 = sdiv i32 %14 , %15 ; %17 = add i32 %13 , %16 ; %18 = add i32 %9 , %17 ; store i32 %18 , i32* @X14 ; br <label>%0 ; <label>:2 ; store i32 N8 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N6 , i32* @X0 ; %1 = load i32 , i32* @X11 ; %2 = load i32 , i32* @X13 ; %3 = srem i32 %1 , %2 ; %4 = srem i32 %3 , N18 ; store i32 %4 , i32* @X6 ; %5 = load i32 , i32* @X14 ; %6 = load i32 , i32* @X8 ; %7 = mul i32 %6 , N12 ; %8 = srem i32 %7 , N15 ; %9 = sdiv i32 %5 , %8 ; %10 = load i32 , i32* @X3 ; %11 = sub i32 %9 , %10 ; %12 = load i32 , i32* @X11 ; %13 = load i32 , i32* @X12 ; %14 = add i32 %12 , %13 ; %15 = load i32 , i32* @X7 ; %16 = srem i32 %14 , %15 ; %17 = icmp sgt i32 %11 , %16 ; br i1 %17 , <label>%0 , <label>%1 ; <label>:0 ; %19 = load i32 , i32* @X4 ; store i32 %19 , i32* @X6 ; br <label>%2 ; <label>:1 ; %21 = load i32 , i32* @X0 ; store i32 %21 , i32* @X1 ; br <label>%2 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X12 ; %3 = load i32 , i32* @X6 ; %4 = mul i32 %2 , %3 ; %5 = load i32 , i32* @X12 ; %6 = sdiv i32 %4 , %5 ; %7 = load i32 , i32* @X1 ; %8 = load i32 , i32* @X10 ; %9 = mul i32 %7 , %8 ; %10 = sdiv i32 %6 , %9 ; %11 = icmp slt i32 N14 , %10 ; br i1 %11 , <label>%1 , <label>%2 ; <label>:1 ; %13 = load i32 , i32* @X7 ; %14 = load i32 , i32* @X10 ; %15 = sdiv i32 N5 , %14 ; %16 = srem i32 %13 , %15 ; %17 = load i32 , i32* @X8 ; %18 = load i32 , i32* @X3 ; %19 = srem i32 %17 , %18 ; %20 = mul i32 %16 , %19 ; %21 = load i32 , i32* @X1 ; %22 = sub i32 N6 , %21 ; %23 = mul i32 %22 , N17 ; %24 = srem i32 %20 , %23 ; store i32 %24 , i32* @X4 ; br <label>%0 ; <label>:2 ; %26 = load i32 , i32* @X1 ; %27 = sdiv i32 0 , %26 ; %28 = load i32 , i32* @X3 ; %29 = add i32 %27 , %28 ; store i32 %29 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X8 ; %2 = load i32 , i32* @X7 ; %3 = load i32 , i32* @X11 ; %4 = mul i32 %2 , %3 ; %5 = load i32 , i32* @X8 ; %6 = sub i32 %4 , %5 ; %7 = mul i32 %6 , 1 ; %8 = srem i32 %1 , %7 ; store i32 %8 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X0 ; %2 = load i32 , i32* @X3 ; %3 = mul i32 N0 , %2 ; %4 = srem i32 N1 , %3 ; %5 = sub i32 %1 , %4 ; %6 = mul i32 N1 , %5 ; store i32 %6 , i32* @X0 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X11 ; %2 = load i32 , i32* @X4 ; %3 = add i32 %1 , %2 ; %4 = load i32 , i32* @X9 ; %5 = sub i32 N2 , %4 ; %6 = mul i32 %3 , %5 ; %7 = load i32 , i32* @X5 ; %8 = add i32 %7 , -1 ; store i32 %8 , i32* @X5 ; %9 = load i32 , i32* @X0 ; %10 = sdiv i32 %7 , %9 ; %11 = sub i32 %10 , N12 ; %12 = sub i32 %6 , %11 ; store i32 %12 , i32* @X9 ; %13 = load i32 , i32* @X10 ; %14 = add i32 %13 , -1 ; store i32 %14 , i32* @X10 ; %15 = load i32 , i32* @X5 ; %16 = sub i32 %15 , N11 ; %17 = mul i32 %13 , %16 ; store i32 %17 , i32* @X12 ; %18 = load i32 , i32* @X7 ; %19 = load i32 , i32* @X2 ; %20 = sdiv i32 %18 , %19 ; %21 = load i32 , i32* @X13 ; %22 = sub i32 %20 , %21 ; %23 = load i32 , i32* @X4 ; %24 = load i32 , i32* @X11 ; %25 = add i32 %23 , %24 ; %26 = load i32 , i32* @X8 ; %27 = add i32 %26 , N16 ; %28 = load i32 , i32* @X3 ; %29 = srem i32 %27 , %28 ; %30 = sub i32 %25 , %29 ; %31 = srem i32 %22 , %30 ; %32 = sub i32 %31 , N9 ; store i32 %32 , i32* @X4 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X4 ; %3 = add i32 %2 , -1 ; store i32 %3 , i32* @X4 ; %4 = load i32 , i32* @X0 ; %5 = sub i32 %4 , N0 ; %6 = icmp sgt i32 %2 , %5 ; br i1 %6 , <label>%1 , <label>%2 ; <label>:1 ; %8 = load i32 , i32* @X6 ; store i32 %8 , i32* @X6 ; br <label>%0 ; <label>:2 ; %10 = load i32 , i32* @X7 ; %11 = add i32 %10 , 1 ; store i32 %11 , i32* @X7 ; %12 = add i32 N3 , %11 ; store i32 %12 , i32* @X7 ; %13 = load i32 , i32* @X10 ; %14 = load i32 , i32* @X3 ; %15 = add i32 %14 , -1 ; store i32 %15 , i32* @X3 ; %16 = sdiv i32 %15 , N15 ; %17 = sdiv i32 %13 , %16 ; store i32 %17 , i32* @X5 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X10 ; %2 = add i32 %1 , -1 ; store i32 %2 , i32* @X10 ; %3 = load i32 , i32* @X6 ; %4 = add i32 %3 , -1 ; store i32 %4 , i32* @X6 ; %5 = add i32 %1 , %3 ; %6 = icmp slt i32 N16 , %5 ; br i1 %6 , <label>%0 , <label>%1 ; <label>:0 ; %8 = load i32 , i32* @X3 ; %9 = add i32 %8 , 1 ; store i32 %9 , i32* @X3 ; %10 = sub i32 N4 , %9 ; %11 = load i32 , i32* @X14 ; %12 = sdiv i32 N12 , %11 ; %13 = srem i32 2 , %12 ; %14 = srem i32 N0 , %13 ; %15 = add i32 N6 , %14 ; %16 = sdiv i32 %15 , N18 ; %17 = add i32 %10 , %16 ; store i32 %17 , i32* @X8 ; %18 = load i32 , i32* @X12 ; %19 = mul i32 %18 , N11 ; store i32 %19 , i32* @X10 ; %20 = load i32 , i32* @X14 ; %21 = add i32 %20 , -1 ; store i32 %21 , i32* @X14 ; %22 = load i32 , i32* @X2 ; %23 = sdiv i32 %20 , %22 ; store i32 %23 , i32* @X10 ; br <label>%2 ; <label>:1 ; %25 = load i32 , i32* @X8 ; %26 = add i32 %25 , -1 ; store i32 %26 , i32* @X8 ; store i32 %25 , i32* @X13 ; br <label>%2 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X2 ; %2 = load i32 , i32* @X13 ; %3 = sdiv i32 %1 , %2 ; store i32 %3 , i32* @X5 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X11 ; store i32 %1 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N16 , i32* @X7 ; store i32 N12 , i32* @X13 ; br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X8 ; %3 = add i32 %2 , -1 ; store i32 %3 , i32* @X8 ; %4 = load i32 , i32* @X5 ; %5 = srem i32 N18 , %4 ; %6 = sub i32 %5 , N18 ; %7 = icmp sgt i32 %3 , %6 ; br i1 %7 , <label>%1 , <label>%2 ; <label>:1 ; %9 = load i32 , i32* @X8 ; %10 = add i32 %9 , -1 ; store i32 %10 , i32* @X8 ; store i32 %9 , i32* @X9 ; br <label>%0 ; <label>:2 ; br <label>%3 ; <label>:3 ; %13 = load i32 , i32* @X13 ; %14 = sdiv i32 N6 , %13 ; %15 = add i32 N6 , %14 ; %16 = icmp sle i32 N11 , %15 ; br i1 %16 , <label>%4 , <label>%5 ; <label>:4 ; %18 = load i32 , i32* @X9 ; %19 = sub i32 N6 , %18 ; %20 = load i32 , i32* @X12 ; %21 = sub i32 %19 , %20 ; store i32 %21 , i32* @X3 ; br <label>%3 ; <label>:5 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X12 ; %2 = mul i32 %1 , N11 ; %3 = sdiv i32 N17 , %2 ; store i32 %3 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X8 ; %3 = mul i32 %2 , N3 ; %4 = icmp slt i32 N6 , %3 ; br i1 %4 , <label>%1 , <label>%2 ; <label>:1 ; store i32 N5 , i32* @X0 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X14 ; %2 = load i32 , i32* @X4 ; %3 = sdiv i32 %1 , %2 ; store i32 %3 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X2 ; %2 = load i32 , i32* @X6 ; %3 = srem i32 %1 , %2 ; %4 = load i32 , i32* @X14 ; %5 = add i32 %4 , 1 ; store i32 %5 , i32* @X14 ; %6 = srem i32 %4 , N3 ; %7 = sub i32 %3 , %6 ; store i32 %7 , i32* @X12 ; store i32 N14 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X14 ; %2 = add i32 %1 , -1 ; store i32 %2 , i32* @X14 ; %3 = load i32 , i32* @X5 ; %4 = add i32 %3 , 2 ; %5 = load i32 , i32* @X14 ; %6 = sdiv i32 %4 , %5 ; %7 = mul i32 %1 , %6 ; store i32 %7 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X5 ; store i32 %1 , i32* @X1 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N3 , i32* @X3 ; %1 = load i32 , i32* @X10 ; store i32 %1 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N19 , i32* @X10 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X5 ; %2 = srem i32 N4 , %1 ; %3 = mul i32 N11 , %2 ; %4 = mul i32 %3 , N6 ; %5 = load i32 , i32* @X7 ; %6 = add i32 N11 , %5 ; %7 = load i32 , i32* @X4 ; %8 = add i32 N16 , %7 ; %9 = load i32 , i32* @X11 ; %10 = sdiv i32 N11 , %9 ; %11 = add i32 %8 , %10 ; %12 = mul i32 %6 , %11 ; %13 = srem i32 %4 , %12 ; store i32 %13 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X1 ; %3 = icmp sle i32 %2 , N14 ; br i1 %3 , <label>%1 , <label>%2 ; <label>:1 ; %5 = load i32 , i32* @X0 ; %6 = sdiv i32 0 , %5 ; %7 = mul i32 N15 , %6 ; store i32 %7 , i32* @X4 ; br <label>%0 ; <label>:2 ; %9 = load i32 , i32* @X8 ; store i32 %9 , i32* @X2 ; %10 = load i32 , i32* @X4 ; %11 = load i32 , i32* @X5 ; %12 = srem i32 %10 , %11 ; %13 = sdiv i32 %12 , N16 ; %14 = load i32 , i32* @X4 ; %15 = load i32 , i32* @X9 ; %16 = sub i32 N6 , %15 ; %17 = sub i32 %14 , %16 ; %18 = srem i32 %13 , %17 ; %19 = load i32 , i32* @X6 ; %20 = mul i32 N14 , %19 ; %21 = load i32 , i32* @X4 ; %22 = sub i32 %20 , %21 ; %23 = icmp sge i32 %18 , %22 ; br i1 %23 , <label>%3 , <label>%4 ; <label>:3 ; store i32 1 , i32* @X2 ; br <label>%4 ; <label>:4 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X9 ; %2 = sdiv i32 N0 , %1 ; store i32 %2 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X11 ; %2 = load i32 , i32* @X12 ; %3 = add i32 %1 , %2 ; %4 = load i32 , i32* @X11 ; %5 = srem i32 %3 , %4 ; %6 = srem i32 N6 , %5 ; %7 = load i32 , i32* @X13 ; %8 = sdiv i32 %6 , %7 ; %9 = srem i32 %8 , N4 ; %10 = load i32 , i32* @X6 ; %11 = sdiv i32 %10 , N18 ; %12 = load i32 , i32* @X4 ; %13 = load i32 , i32* @X4 ; %14 = sub i32 %13 , N6 ; %15 = sdiv i32 %12 , %14 ; %16 = add i32 %11 , %15 ; %17 = mul i32 %9 , %16 ; store i32 %17 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X8 ; %2 = sub i32 %1 , N17 ; store i32 %2 , i32* @X7 ; %3 = load i32 , i32* @X10 ; %4 = sub i32 N17 , %3 ; store i32 %4 , i32* @X10 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X11 ; %2 = add i32 %1 , -1 ; store i32 %2 , i32* @X11 ; store i32 %2 , i32* @X6 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X12 ; store i32 %1 , i32* @X0 ; store i32 N3 , i32* @X7 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X13 ; %3 = add i32 N9 , %2 ; %4 = sub i32 N4 , %3 ; %5 = load i32 , i32* @X5 ; %6 = srem i32 %4 , %5 ; %7 = load i32 , i32* @X4 ; %8 = sdiv i32 N16 , %7 ; %9 = load i32 , i32* @X1 ; %10 = load i32 , i32* @X8 ; %11 = mul i32 %9 , %10 ; %12 = load i32 , i32* @X2 ; %13 = add i32 %11 , %12 ; %14 = sdiv i32 %8 , %13 ; %15 = icmp sge i32 %6 , %14 ; br i1 %15 , <label>%1 , <label>%2 ; <label>:1 ; %17 = load i32 , i32* @X8 ; %18 = load i32 , i32* @X6 ; %19 = load i32 , i32* @X9 ; %20 = sub i32 %18 , %19 ; %21 = sub i32 %20 , N18 ; %22 = add i32 %17 , %21 ; store i32 %22 , i32* @X11 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X8 ; %2 = load i32 , i32* @X0 ; %3 = mul i32 %2 , N1 ; %4 = load i32 , i32* @X11 ; %5 = add i32 %3 , %4 ; %6 = sdiv i32 %1 , %5 ; store i32 %6 , i32* @X7 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X3 ; store i32 %1 , i32* @X5 ; store i32 N3 , i32* @X14 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X14 ; %2 = load i32 , i32* @X6 ; %3 = add i32 %2 , 1 ; store i32 %3 , i32* @X6 ; %4 = mul i32 %1 , %2 ; %5 = load i32 , i32* @X14 ; %6 = add i32 N6 , %5 ; %7 = add i32 %4 , %6 ; store i32 %7 , i32* @X0 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X10 ; store i32 %1 , i32* @X8 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N13 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X4 ; %2 = mul i32 %1 , N6 ; %3 = sdiv i32 %2 , N9 ; store i32 %3 , i32* @X5 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X6 ; store i32 %1 , i32* @X1 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X1 ; %2 = load i32 , i32* @X5 ; %3 = sub i32 %1 , %2 ; store i32 %3 , i32* @X1 ; %4 = load i32 , i32* @X12 ; store i32 %4 , i32* @X13 ; %5 = load i32 , i32* @X11 ; %6 = mul i32 %5 , N3 ; %7 = load i32 , i32* @X13 ; %8 = sub i32 %7 , N11 ; %9 = add i32 %8 , N10 ; %10 = srem i32 %6 , %9 ; %11 = load i32 , i32* @X8 ; %12 = mul i32 %10 , %11 ; store i32 %12 , i32* @X10 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X3 ; store i32 %1 , i32* @X5 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X5 ; %3 = srem i32 %2 , N16 ; %4 = load i32 , i32* @X9 ; %5 = sub i32 %3 , %4 ; %6 = load i32 , i32* @X4 ; %7 = srem i32 N15 , %6 ; %8 = load i32 , i32* @X9 ; %9 = add i32 %8 , -1 ; store i32 %9 , i32* @X9 ; %10 = load i32 , i32* @X7 ; %11 = load i32 , i32* @X2 ; %12 = sub i32 %10 , %11 ; %13 = add i32 %8 , %12 ; %14 = srem i32 %7 , %13 ; %15 = icmp sle i32 %5 , %14 ; br i1 %15 , <label>%1 , <label>%2 ; <label>:1 ; %17 = load i32 , i32* @X2 ; %18 = add i32 N16 , %17 ; store i32 %18 , i32* @X8 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X3 ; %2 = add i32 N10 , %1 ; store i32 %2 , i32* @X13 ; %3 = load i32 , i32* @X12 ; %4 = load i32 , i32* @X10 ; %5 = sdiv i32 %4 , N0 ; %6 = sdiv i32 %3 , %5 ; %7 = srem i32 N1 , %6 ; %8 = load i32 , i32* @X1 ; %9 = load i32 , i32* @X4 ; %10 = add i32 %8 , %9 ; %11 = mul i32 %10 , N1 ; %12 = sub i32 %11 , N19 ; %13 = mul i32 %7 , %12 ; store i32 %13 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X6 ; %2 = sdiv i32 N3 , %1 ; %3 = mul i32 N8 , %2 ; store i32 %3 , i32* @X14 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X2 ; %2 = mul i32 %1 , N0 ; %3 = srem i32 %2 , N17 ; %4 = add i32 %3 , N15 ; %5 = mul i32 N5 , %4 ; %6 = add i32 N15 , %5 ; store i32 %6 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X13 ; %2 = load i32 , i32* @X14 ; %3 = load i32 , i32* @X8 ; %4 = srem i32 %2 , %3 ; %5 = mul i32 %1 , %4 ; %6 = mul i32 N14 , %5 ; store i32 %6 , i32* @X10 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X3 ; %2 = load i32 , i32* @X9 ; %3 = sdiv i32 %1 , %2 ; %4 = load i32 , i32* @X8 ; %5 = icmp sgt i32 %3 , %4 ; br i1 %5 , <label>%0 , <label>%1 ; <label>:0 ; %7 = load i32 , i32* @X7 ; %8 = add i32 N2 , %7 ; %9 = add i32 N19 , %8 ; %10 = load i32 , i32* @X13 ; %11 = sdiv i32 N10 , %10 ; %12 = sdiv i32 N14 , %11 ; %13 = sub i32 %9 , %12 ; %14 = mul i32 N3 , %13 ; store i32 %14 , i32* @X11 ; br <label>%2 ; <label>:1 ; store i32 N1 , i32* @X6 ; br <label>%2 ; <label>:2 ; %17 = load i32 , i32* @X4 ; %18 = srem i32 N7 , %17 ; %19 = load i32 , i32* @X3 ; %20 = add i32 %19 , -1 ; store i32 %20 , i32* @X3 ; %21 = load i32 , i32* @X6 ; %22 = mul i32 %21 , N18 ; %23 = add i32 N15 , %22 ; %24 = sub i32 %23 , 1 ; %25 = add i32 %19 , %24 ; %26 = icmp sgt i32 %18 , %25 ; br i1 %26 , <label>%3 , <label>%4 ; <label>:3 ; store i32 N19 , i32* @X3 ; br <label>%5 ; <label>:4 ; %29 = load i32 , i32* @X14 ; %30 = load i32 , i32* @X13 ; %31 = sub i32 %29 , %30 ; store i32 %31 , i32* @X8 ; store i32 N4 , i32* @X14 ; br <label>%5 ; <label>:5 ; %33 = load i32 , i32* @X13 ; %34 = load i32 , i32* @X2 ; %35 = add i32 N16 , %34 ; %36 = sub i32 N3 , %35 ; %37 = srem i32 %33 , %36 ; store i32 %37 , i32* @X11 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X11 ; %2 = add i32 %1 , -1 ; store i32 %2 , i32* @X11 ; %3 = sdiv i32 %2 , N1 ; %4 = load i32 , i32* @X5 ; %5 = add i32 %4 , -1 ; store i32 %5 , i32* @X5 ; %6 = load i32 , i32* @X11 ; %7 = sub i32 %5 , %6 ; %8 = srem i32 %3 , %7 ; %9 = load i32 , i32* @X8 ; %10 = mul i32 %9 , N1 ; %11 = load i32 , i32* @X10 ; %12 = mul i32 %10 , %11 ; %13 = load i32 , i32* @X2 ; %14 = sdiv i32 N5 , %13 ; %15 = srem i32 N16 , %14 ; %16 = sdiv i32 %15 , N11 ; %17 = add i32 N0 , %16 ; %18 = sub i32 %12 , %17 ; %19 = icmp slt i32 %8 , %18 ; br i1 %19 , <label>%0 , <label>%1 ; <label>:0 ; store i32 N11 , i32* @X2 ; %21 = load i32 , i32* @X1 ; %22 = load i32 , i32* @X7 ; %23 = add i32 %22 , N9 ; %24 = sdiv i32 N8 , %23 ; %25 = load i32 , i32* @X6 ; %26 = sdiv i32 N7 , %25 ; %27 = load i32 , i32* @X9 ; %28 = add i32 N14 , %27 ; %29 = add i32 %26 , %28 ; %30 = srem i32 %24 , %29 ; %31 = mul i32 %21 , %30 ; store i32 %31 , i32* @X7 ; %32 = load i32 , i32* @X0 ; store i32 %32 , i32* @X1 ; %33 = load i32 , i32* @X2 ; store i32 %33 , i32* @X12 ; br <label>%1 ; <label>:1 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X12 ; %2 = sdiv i32 N8 , %1 ; %3 = load i32 , i32* @X6 ; %4 = add i32 %3 , 1 ; store i32 %4 , i32* @X6 ; %5 = icmp slt i32 %2 , %4 ; br i1 %5 , <label>%0 , <label>%1 ; <label>:0 ; %7 = load i32 , i32* @X4 ; %8 = mul i32 %7 , N2 ; store i32 %8 , i32* @X3 ; br <label>%1 ; <label>:1 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N3 , i32* @X1 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N15 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X2 ; %3 = load i32 , i32* @X10 ; %4 = mul i32 %2 , %3 ; %5 = load i32 , i32* @X3 ; %6 = srem i32 N14 , %5 ; %7 = sub i32 %4 , %6 ; %8 = load i32 , i32* @X2 ; %9 = sdiv i32 %7 , %8 ; %10 = load i32 , i32* @X9 ; %11 = sdiv i32 %10 , N17 ; %12 = load i32 , i32* @X0 ; %13 = srem i32 N12 , %12 ; %14 = srem i32 %11 , %13 ; %15 = sub i32 %9 , %14 ; %16 = mul i32 N18 , %15 ; %17 = load i32 , i32* @X4 ; %18 = load i32 , i32* @X14 ; %19 = load i32 , i32* @X8 ; %20 = add i32 %18 , %19 ; %21 = sdiv i32 %20 , N4 ; %22 = sdiv i32 %21 , N12 ; %23 = add i32 %17 , %22 ; %24 = add i32 %23 , N5 ; %25 = mul i32 %16 , %24 ; %26 = load i32 , i32* @X14 ; %27 = add i32 %26 , -1 ; store i32 %27 , i32* @X14 ; %28 = icmp sge i32 %25 , %26 ; br i1 %28 , <label>%1 , <label>%2 ; <label>:1 ; %30 = load i32 , i32* @X2 ; %31 = sub i32 N5 , %30 ; %32 = load i32 , i32* @X9 ; %33 = mul i32 N9 , %32 ; %34 = srem i32 %31 , %33 ; store i32 %34 , i32* @X2 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X0 ; %2 = srem i32 N14 , %1 ; %3 = srem i32 %2 , N16 ; store i32 %3 , i32* @X8 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X0 ; %2 = sdiv i32 N18 , %1 ; store i32 %2 , i32* @X10 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N13 , i32* @X1 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X7 ; %2 = load i32 , i32* @X11 ; %3 = load i32 , i32* @X8 ; %4 = srem i32 %2 , %3 ; %5 = mul i32 %1 , %4 ; %6 = mul i32 N19 , %5 ; %7 = add i32 %6 , N7 ; store i32 %7 , i32* @X11 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X8 ; %2 = srem i32 N0 , %1 ; %3 = load i32 , i32* @X2 ; %4 = sdiv i32 %2 , %3 ; %5 = mul i32 N5 , %4 ; store i32 %5 , i32* @X0 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X10 ; store i32 %1 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X5 ; %2 = sdiv i32 %1 , N10 ; %3 = mul i32 N9 , %2 ; store i32 %3 , i32* @X11 ; %4 = load i32 , i32* @X8 ; %5 = mul i32 N8 , %4 ; %6 = load i32 , i32* @X5 ; %7 = mul i32 %5 , %6 ; %8 = load i32 , i32* @X13 ; %9 = sdiv i32 N12 , %8 ; %10 = load i32 , i32* @X2 ; %11 = sub i32 %10 , N5 ; %12 = srem i32 %9 , %11 ; %13 = sub i32 N14 , %12 ; %14 = add i32 %7 , %13 ; store i32 %14 , i32* @X7 ; br <label>%0 ; <label>:0 ; %16 = load i32 , i32* @X8 ; %17 = add i32 %16 , 1 ; store i32 %17 , i32* @X8 ; %18 = load i32 , i32* @X3 ; %19 = sdiv i32 N5 , %18 ; %20 = load i32 , i32* @X2 ; %21 = sdiv i32 N0 , %20 ; %22 = add i32 N10 , %21 ; %23 = load i32 , i32* @X1 ; %24 = add i32 %22 , %23 ; %25 = srem i32 %24 , N10 ; %26 = srem i32 %25 , N6 ; %27 = mul i32 %19 , %26 ; %28 = load i32 , i32* @X0 ; %29 = srem i32 %27 , %28 ; %30 = icmp ne i32 %17 , %29 ; br i1 %30 , <label>%1 , <label>%2 ; <label>:1 ; %32 = load i32 , i32* @X11 ; %33 = add i32 %32 , N18 ; store i32 %33 , i32* @X11 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N16 , i32* @X14 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X10 ; store i32 %1 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X3 ; %2 = sub i32 %1 , N11 ; %3 = load i32 , i32* @X0 ; %4 = srem i32 %3 , N12 ; %5 = load i32 , i32* @X10 ; %6 = mul i32 %4 , %5 ; %7 = sub i32 N1 , %6 ; %8 = sub i32 %2 , %7 ; %9 = load i32 , i32* @X14 ; %10 = sub i32 %8 , %9 ; store i32 %10 , i32* @X8 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X10 ; store i32 %1 , i32* @X0 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X11 ; %2 = mul i32 %1 , N19 ; store i32 %2 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N10 , i32* @X1 ; %1 = load i32 , i32* @X13 ; %2 = load i32 , i32* @X10 ; %3 = load i32 , i32* @X0 ; %4 = sdiv i32 %2 , %3 ; %5 = sdiv i32 %1 , %4 ; %6 = load i32 , i32* @X12 ; %7 = sdiv i32 N17 , %6 ; %8 = load i32 , i32* @X1 ; %9 = sub i32 %7 , %8 ; %10 = load i32 , i32* @X11 ; %11 = sub i32 N5 , %10 ; %12 = load i32 , i32* @X0 ; %13 = add i32 %12 , -1 ; store i32 %13 , i32* @X0 ; %14 = mul i32 %11 , %12 ; %15 = sub i32 %9 , %14 ; %16 = icmp slt i32 %5 , %15 ; br i1 %16 , <label>%0 , <label>%1 ; <label>:0 ; %18 = load i32 , i32* @X1 ; %19 = load i32 , i32* @X2 ; %20 = mul i32 %18 , %19 ; store i32 %20 , i32* @X13 ; br <label>%1 ; <label>:1 ; %22 = load i32 , i32* @X4 ; %23 = load i32 , i32* @X11 ; %24 = sub i32 %23 , N19 ; %25 = srem i32 %22 , %24 ; %26 = add i32 N2 , %25 ; %27 = load i32 , i32* @X8 ; %28 = srem i32 %27 , N5 ; %29 = sub i32 %26 , %28 ; store i32 %29 , i32* @X1 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X10 ; store i32 %1 , i32* @X11 ; %2 = load i32 , i32* @X1 ; %3 = sub i32 N6 , %2 ; store i32 %3 , i32* @X0 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X9 ; %2 = srem i32 N1 , %1 ; %3 = sub i32 %2 , N8 ; %4 = load i32 , i32* @X6 ; %5 = load i32 , i32* @X5 ; %6 = add i32 N0 , %5 ; %7 = add i32 %6 , N19 ; %8 = mul i32 %4 , %7 ; %9 = add i32 %3 , %8 ; store i32 %9 , i32* @X2 ; %10 = load i32 , i32* @X6 ; store i32 %10 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X5 ; %2 = add i32 N6 , %1 ; %3 = load i32 , i32* @X5 ; %4 = load i32 , i32* @X12 ; %5 = srem i32 %3 , %4 ; %6 = add i32 N0 , %5 ; %7 = sub i32 %2 , %6 ; %8 = load i32 , i32* @X1 ; %9 = add i32 %8 , -1 ; store i32 %9 , i32* @X1 ; %10 = mul i32 %9 , N1 ; %11 = add i32 %7 , %10 ; store i32 %11 , i32* @X7 ; %12 = load i32 , i32* @X1 ; %13 = mul i32 %12 , N18 ; %14 = sub i32 %13 , N11 ; %15 = srem i32 N4 , %14 ; store i32 %15 , i32* @X2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X8 ; %2 = load i32 , i32* @X9 ; %3 = sub i32 %1 , %2 ; store i32 %3 , i32* @X5 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X4 ; %2 = srem i32 N2 , %1 ; store i32 %2 , i32* @X3 ; %3 = load i32 , i32* @X1 ; %4 = sdiv i32 %3 , N4 ; %5 = load i32 , i32* @X14 ; %6 = add i32 %5 , 1 ; store i32 %6 , i32* @X14 ; %7 = mul i32 %5 , N1 ; %8 = icmp sge i32 %4 , %7 ; br i1 %8 , <label>%0 , <label>%1 ; <label>:0 ; %10 = load i32 , i32* @X7 ; %11 = add i32 N9 , %10 ; %12 = load i32 , i32* @X12 ; %13 = add i32 %12 , -1 ; store i32 %13 , i32* @X12 ; %14 = srem i32 N4 , %12 ; %15 = sdiv i32 %11 , %14 ; store i32 %15 , i32* @X14 ; br <label>%1 ; <label>:1 ; %17 = load i32 , i32* @X14 ; %18 = mul i32 N14 , %17 ; %19 = sdiv i32 %18 , N8 ; store i32 %19 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N15 , i32* @X7 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X13 ; %2 = load i32 , i32* @X7 ; %3 = add i32 N18 , %2 ; %4 = sdiv i32 %1 , %3 ; %5 = mul i32 N8 , %4 ; %6 = load i32 , i32* @X6 ; %7 = load i32 , i32* @X8 ; %8 = sub i32 %6 , %7 ; %9 = sub i32 N11 , %8 ; %10 = mul i32 %5 , %9 ; %11 = load i32 , i32* @X11 ; %12 = load i32 , i32* @X10 ; %13 = add i32 %11 , %12 ; %14 = load i32 , i32* @X11 ; %15 = add i32 %13 , %14 ; %16 = sdiv i32 %10 , %15 ; store i32 %16 , i32* @X1 ; %17 = load i32 , i32* @X9 ; store i32 %17 , i32* @X13 ; %18 = load i32 , i32* @X5 ; store i32 %18 , i32* @X8 ; store i32 N6 , i32* @X1 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N17 , i32* @X14 ; br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X6 ; %3 = load i32 , i32* @X0 ; %4 = sdiv i32 N13 , %3 ; %5 = sdiv i32 %2 , %4 ; %6 = load i32 , i32* @X13 ; %7 = load i32 , i32* @X3 ; %8 = sdiv i32 %6 , %7 ; %9 = sub i32 %5 , %8 ; %10 = load i32 , i32* @X12 ; %11 = sdiv i32 %9 , %10 ; %12 = icmp ne i32 N1 , %11 ; br i1 %12 , <label>%1 , <label>%2 ; <label>:1 ; %14 = load i32 , i32* @X2 ; %15 = srem i32 %14 , N17 ; %16 = mul i32 N19 , %15 ; store i32 %16 , i32* @X1 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X7 ; store i32 %1 , i32* @X2 ; %2 = load i32 , i32* @X5 ; %3 = add i32 %2 , 1 ; store i32 %3 , i32* @X5 ; %4 = load i32 , i32* @X2 ; %5 = add i32 %4 , -1 ; store i32 %5 , i32* @X2 ; %6 = mul i32 %2 , %4 ; store i32 %6 , i32* @X8 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X2 ; store i32 %1 , i32* @X14 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N0 , i32* @X2 ; %1 = load i32 , i32* @X8 ; %2 = load i32 , i32* @X10 ; %3 = load i32 , i32* @X2 ; %4 = sdiv i32 %2 , %3 ; %5 = add i32 %1 , %4 ; %6 = mul i32 N19 , %5 ; store i32 %6 , i32* @X9 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X13 ; store i32 %1 , i32* @X12 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N7 , i32* @X9 ; %1 = load i32 , i32* @X4 ; %2 = load i32 , i32* @X1 ; %3 = load i32 , i32* @X12 ; %4 = mul i32 N12 , %3 ; %5 = srem i32 %2 , %4 ; %6 = mul i32 %1 , %5 ; %7 = load i32 , i32* @X9 ; %8 = sdiv i32 %7 , N17 ; %9 = srem i32 %6 , %8 ; %10 = icmp eq i32 N10 , %9 ; br i1 %10 , <label>%0 , <label>%1 ; <label>:0 ; %12 = load i32 , i32* @X11 ; %13 = add i32 %12 , N9 ; %14 = load i32 , i32* @X10 ; %15 = load i32 , i32* @X6 ; %16 = srem i32 %14 , %15 ; %17 = sub i32 N11 , %16 ; %18 = load i32 , i32* @X1 ; %19 = sdiv i32 %17 , %18 ; %20 = mul i32 N19 , %19 ; %21 = mul i32 %13 , %20 ; store i32 %21 , i32* @X1 ; br <label>%1 ; <label>:1 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X9 ; %2 = sdiv i32 N6 , %1 ; %3 = add i32 N18 , %2 ; %4 = load i32 , i32* @X8 ; %5 = srem i32 N11 , %4 ; %6 = load i32 , i32* @X3 ; %7 = add i32 %6 , 1 ; store i32 %7 , i32* @X3 ; %8 = mul i32 %5 , %6 ; %9 = add i32 N13 , %8 ; %10 = icmp ne i32 %3 , %9 ; br i1 %10 , <label>%0 , <label>%1 ; <label>:0 ; %12 = load i32 , i32* @X7 ; %13 = load i32 , i32* @X3 ; %14 = add i32 %12 , %13 ; %15 = load i32 , i32* @X14 ; %16 = load i32 , i32* @X11 ; %17 = srem i32 %15 , %16 ; %18 = load i32 , i32* @X13 ; %19 = sub i32 %17 , %18 ; %20 = load i32 , i32* @X8 ; %21 = mul i32 %19 , %20 ; %22 = add i32 %14 , %21 ; store i32 %22 , i32* @X1 ; %23 = load i32 , i32* @X6 ; %24 = add i32 %23 , 1 ; store i32 %24 , i32* @X6 ; %25 = load i32 , i32* @X14 ; %26 = sdiv i32 %24 , %25 ; %27 = mul i32 N8 , %26 ; %28 = add i32 N14 , %27 ; store i32 %28 , i32* @X2 ; br <label>%1 ; <label>:1 ; %30 = load i32 , i32* @X14 ; %31 = mul i32 2 , %30 ; %32 = add i32 %31 , N10 ; store i32 %32 , i32* @X8 ; %33 = load i32 , i32* @X4 ; %34 = sub i32 N3 , %33 ; %35 = load i32 , i32* @X10 ; %36 = sub i32 %34 , %35 ; %37 = load i32 , i32* @X13 ; %38 = sdiv i32 N14 , %37 ; %39 = icmp ne i32 %36 , %38 ; br i1 %39 , <label>%2 , <label>%3 ; <label>:2 ; store i32 N17 , i32* @X14 ; br <label>%4 ; <label>:3 ; %42 = load i32 , i32* @X7 ; %43 = sdiv i32 %42 , 1 ; %44 = load i32 , i32* @X1 ; %45 = sub i32 N6 , %44 ; %46 = add i32 %43 , %45 ; store i32 %46 , i32* @X7 ; br <label>%4 ; <label>:4 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X0 ; %3 = load i32 , i32* @X3 ; %4 = load i32 , i32* @X1 ; %5 = add i32 %4 , 1 ; store i32 %5 , i32* @X1 ; %6 = load i32 , i32* @X9 ; %7 = srem i32 %4 , %6 ; %8 = sub i32 %3 , %7 ; %9 = srem i32 %2 , %8 ; %10 = load i32 , i32* @X10 ; %11 = add i32 %10 , N2 ; %12 = icmp ne i32 %9 , %11 ; br i1 %12 , <label>%1 , <label>%2 ; <label>:1 ; store i32 N10 , i32* @X0 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = 'store i32 N0 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X1 ; %2 = srem i32 N6 , %1 ; %3 = srem i32 N14 , %2 ; %4 = load i32 , i32* @X7 ; %5 = add i32 %4 , -1 ; store i32 %5 , i32* @X7 ; %6 = load i32 , i32* @X4 ; %7 = srem i32 %5 , %6 ; %8 = add i32 %3 , %7 ; store i32 %8 , i32* @X1 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X6 ; %2 = load i32 , i32* @X2 ; %3 = mul i32 %1 , %2 ; store i32 %3 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X9 ; %2 = load i32 , i32* @X14 ; %3 = sub i32 N16 , %2 ; %4 = srem i32 %1 , %3 ; %5 = load i32 , i32* @X2 ; %6 = sub i32 %4 , %5 ; %7 = sub i32 N14 , %6 ; store i32 %7 , i32* @X11 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X10 ; %2 = load i32 , i32* @X4 ; %3 = mul i32 %1 , %2 ; %4 = srem i32 N10 , %3 ; store i32 %4 , i32* @X14 ; %5 = load i32 , i32* @X3 ; %6 = add i32 %5 , -1 ; store i32 %6 , i32* @X3 ; %7 = load i32 , i32* @X13 ; %8 = add i32 %6 , %7 ; %9 = add i32 %8 , N19 ; %10 = load i32 , i32* @X10 ; %11 = add i32 %10 , 1 ; store i32 %11 , i32* @X10 ; %12 = load i32 , i32* @X3 ; %13 = add i32 %12 , N10 ; %14 = sub i32 %11 , %13 ; %15 = mul i32 %9 , %14 ; store i32 %15 , i32* @X10 ;'
	results.append(compare_codes(x, x))
	x = 'br <label>%0 ; <label>:0 ; %2 = load i32 , i32* @X2 ; %3 = load i32 , i32* @X1 ; %4 = srem i32 N3 , %3 ; %5 = srem i32 %2 , %4 ; %6 = icmp eq i32 N0 , %5 ; br i1 %6 , <label>%1 , <label>%2 ; <label>:1 ; %8 = load i32 , i32* @X10 ; %9 = srem i32 N11 , %8 ; %10 = add i32 N11 , %9 ; %11 = load i32 , i32* @X11 ; %12 = sub i32 %10 , %11 ; store i32 %12 , i32* @X2 ; %13 = load i32 , i32* @X1 ; %14 = srem i32 %13 , N12 ; %15 = sdiv i32 N13 , %14 ; %16 = load i32 , i32* @X10 ; %17 = srem i32 %15 , %16 ; store i32 %17 , i32* @X1 ; br <label>%0 ; <label>:2 ;'
	results.append(compare_codes(x, x))
	x = '%1 = load i32 , i32* @X8 ; %2 = sdiv i32 N13 , %1 ; %3 = load i32 , i32* @X6 ; %4 = sdiv i32 N9 , %3 ; %5 = add i32 %2 , %4 ; store i32 %5 , i32* @X13 ;'
	results.append(compare_codes(x, x))
	print all(results)