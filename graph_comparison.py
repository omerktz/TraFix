import re
import itertools

class VarInstruction:
	def __init__(self, var):
		self.defines = var
		self.code = 'Var '+var
		self.is_jump = False
		self.is_label = False
		self.targets = []
		self.is_branch = False
		self.condition = None
		self.is_condition = False
		self.uses = []
		self.is_symmetric = False


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
		if re.match('^<label>[0-9]+ :$', code):
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
			self.targets = ['<label>'+x[7:]+' :' for x in labels]
		elif code.startswith('store'):
			code = code[6:]
			parts = map(lambda x: x.strip(), code.split(','))
			self.op = 'store'
			self.defines = parts[1][1:]
			self.uses.append(parts[0])
		elif ' = ' in self.code:
			self.defines = self.code.split(' = ')[0].strip()
			code = code[code.index('=')+1:].strip()
			self.op = code[:code.index(' ')]
			if code.startswith('load'):
				self.uses.append(code.split(',')[1].strip()[1:])
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
		# create nodes for vars
		all_vars = set(filter(lambda v: v is not None and re.match('^X[0-9]+$', v), set.union(*map(lambda i: set(self.instructions[i].uses), self.instructions)).union(set(map(lambda i: self.instructions[i].defines, self.instructions)))))
		for var in all_vars:
			self.instructions[var] = VarInstruction(var)
		entry_childs = self.childs[0][:]
		for e in entry_childs:
			self.parents[e].remove(0)
			self.parents[e] += list(all_vars)
		self.childs[0] = list(all_vars)
		for v in all_vars:
			self.parents[v] = [0]
			self.childs[v] = entry_childs
		# build ddg
		ddg_init = dict([(i, set()) for i in self.instructions])
		ddg_gen = dict(map(lambda i: (i, [(self.instructions[i].defines, i)]) if self.instructions[i].defines is not None else (i, []), self.instructions))
		ddg_kill = dict(map(lambda i: (i, [(self.instructions[i].defines, j) for j in self.instructions]) if self.instructions[i].defines is not None else (i, []), self.instructions))
		self.reaching_definitions = self.get_fixed_point(ddg_init, ddg_gen, ddg_kill, set.union, self.parents, self.childs)
		self.ddg = dict(map(lambda i: (i, map(lambda u: map(lambda y: y[1], filter(lambda x: x[0] == u, self.reaching_definitions[i])), self.instructions[i].uses)), self.instructions))
		self.rddg = dict([(i, set()) for i in self.instructions])
		for i in self.ddg.keys():
			for d in self.ddg[i]:
				for x in d:
					self.rddg[x].add(i)
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
			immediates = filter(lambda d: all(map(lambda x: d not in self.post_dominators[x], post_dominators)), post_dominators)
			if len(immediates) > 0:
				self.immediate_post_dominators[i] = immediates[0]
			else:
				self.immediate_post_dominators[i] = None
		self.cdg = dict([(i, set()) for i in self.instructions])
		self.rcdg = dict([(i, set()) for i in self.instructions])
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
				self.rcdg[b].add(r)


	def get_fixed_point(self, init, gen, kill, merge, predecessors, successors):
		in_states = init
		out_states = dict([(i, set()) for i in self.instructions])
		worklist = set(self.instructions.keys())
		while len(worklist) > 0:
			i = worklist.pop()
			if len(predecessors[i]) > 0:
				states = [out_states[p] for p in predecessors[i]]
				new_in_state = set(merge(*states))
			else:
				new_in_state = in_states[i]
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
		# handle VarInsturctions
		if isinstance(inst1, VarInstruction):
			return isinstance(inst2, VarInstruction)
		if isinstance(inst2, VarInstruction):
			return False
		if inst1.op != inst2.op:
			return False
		if inst1.is_condition:
			if inst1.relation != inst2.relation:
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
		rcdg1 = graph1.rcdg[index1]
		rcdg2 = graph2.rcdg[index2]
		if len(rcdg1) != len(rcdg2):
			return False
		ddg1 = graph1.ddg[index1]
		ddg2 = graph2.ddg[index2]
		if len(ddg1) != len(ddg2):
			return False
		if sorted(map(len,ddg1)) != sorted(map(len,ddg2)):
			return False
		rddg1 = graph1.rddg[index1]
		rddg2 = graph2.rddg[index2]
		if len(rddg1) != len(rddg2):
			return False
		return True
	def generate_all_dependency_pairs(index1, index2):
		cdg1 = graph1.cdg[index1]
		cdg2 = graph2.cdg[index2]
		dependency_pairs = set(list(itertools.product(cdg1, cdg2)))
		rcdg1 = graph1.rcdg[index1]
		rcdg2 = graph2.rcdg[index2]
		dependency_pairs.update(set(list(itertools.product(rcdg1, rcdg2))))
		rddg1 = graph1.rddg[index1]
		rddg2 = graph2.rddg[index2]
		dependency_pairs.update(set(list(itertools.product(rddg1, rddg2))))
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
	simple = '%1 = load i32 , i32* @X3 ; %2 = load i32 , i32* @X10 ; %3 = mul i32 %2 , 0 ; %4 = mul i32 %1 , %3 ; store i32 %4 , i32* @X11 ;'
	print compare_codes(simple, simple)
	simple2 = '%1 = load i32 , i32* @X10 ; %2 = load i32 , i32* @X4 ; %3 = mul i32 %1 , 0 ; %4 = mul i32 %3 , %2 ; store i32 %4 , i32* @X11 ;'
	print compare_codes(simple, simple2)
	loop = 'br <label>0 ; <label>0 : ; %2 = load i32 , i32* @X8 ; %3 = mul i32 %2 , 3 ; %4 = icmp slt i32 6 , %3 ; br i1 %4 , <label>1 , <label>2 ; <label>1 : ; store i32 5 , i32* @X0 ; br <label>0 ; <label>2 : ;'
	print compare_codes(loop, loop)
	branch = '%1 = load i32 , i32* @X3 ; %2 = load i32 , i32* @X7 ; %3 = mul i32 %1 , %2 ; %4 = load i32 , i32* @X5 ; %5 = srem i32 %4 , 8 ; %6 = add i32 9 , %5 ; %7 = load i32 , i32* @X9 ; %8 = mul i32 0 , %7 ; %9 = srem i32 %6 , %8 ; %10 = icmp sge i32 %3 , %9 ; br i1 %10 , <label>0 , <label>1 ; <label>0 : ; %12 = load i32 , i32* @X11 ; store i32 %12 , i32* @X11 ; br <label>2 ; <label>1 : ; %14 = load i32 , i32* @X2 ; %15 = add i32 2 , %14 ; %16 = load i32 , i32* @X1 ; %17 = srem i32 5 , %16 ; %18 = load i32 , i32* @X9 ; %19 = add i32 %17 , %18 ; %20 = mul i32 %15 , %19 ; store i32 %20 , i32* @X2 ; br <label>2 ; <label>2 : ;'
	print compare_codes(branch, branch)
	tmp = 'br <label>0 ; <label>0 : ; %2 = load , @X4 ; %3 = sub %2 , N16 ; %4 = sdiv N19 , %3 ; %5 = load , @X4 ; %6 = load , @X1 ; %7 = sub %5 , %6 ; %8 = srem %7 , N7 ; %9 = sub N2 , %8 ; %10 = sub %9 , N11 ; %11 = sub N10 , %10 ; %12 = icmp ne %4 , %11 ; br %12 , <label>1 , <label>2 ; <label>1 : ; %14 = load , @X14 ; %15 = add %14 , N14 ; %16 = load , @X9 ; %17 = add %15 , %16 ; %18 = load , @X14 ; %19 = load , @X6 ; %20 = load , @X9 ; %21 = add %19 , %20 ; %22 = mul %18 , %21 ; %23 = sdiv %17 , %22 ; store %23 , @X11 ; br <label>0 ; <label>2 : ;'
	print compare_codes(tmp, tmp)
