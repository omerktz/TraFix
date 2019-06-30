import re
import itertools
import tempfile

# overriden with Instruction class from compiler api
from distutils.command.install import install

Instruction = None
compiler_api_equivalent_ops = None
def set_compiler_api(compiler_api):
	global Instruction
	global compiler_api_equivalent_ops
	Instruction = compiler_api.Instruction
	compiler_api_equivalent_ops = compiler_api.equivalent_ops

class VarInstruction:
	def __init__(self, var):
		self.op = ''
		self.defines = [var]
		self.code = 'Var '+var
		self.is_jump = False
		self.is_label = False
		self.targets = []
		self.is_branch = False
		self.is_condition = False
		self.uses = []
		self.is_symmetric = False
		self.can_be_reduced = False

class Graph:
	def __init__(self, code, simplify=True):
		self.bad_graph = False
		self.simplify = simplify
		# remove garbage
		cleaned_code = ' __entry__ ; ' + re.sub('i32\*?', '', re.sub('i1', '', code)).replace('  ', ' ') + ' __exit__ ; '
		# parse code
		split_code = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), cleaned_code.split(';')))
		self.instructions = dict(zip(range(len(split_code)), [Instruction(split_code[i], i) for i in range(len(split_code))]))
		# build cfg
		self.childs = dict([(i, []) for i in self.instructions])
		self.parents = dict([(i, []) for i in self.instructions])
		for i in self.instructions:
			if self.instructions[i].is_jump:
				for label in self.instructions[i].targets:
					indexes = filter(lambda j: label in self.instructions[j].labels, self.instructions.keys())
					if len(indexes) == 0:
						print "Missing label"
						self.bad_graph = True
						return
					index = indexes[0]
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
		all_vars = set(filter(lambda v: v is not None and re.match('^X[0-9]+$', v), set.union(*map(lambda i: set(self.instructions[i].uses), self.instructions)).union(set.union(*map(lambda i: set(self.instructions[i].defines), self.instructions)))))
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
		ddg_gen = dict(map(lambda i: (i, [(d, i) for d in self.instructions[i].defines]), self.instructions))
		ddg_kill = dict(map(lambda i: (i, list(itertools.product(self.instructions[i].defines, self.instructions.keys()))), self.instructions))
		self.reaching_definitions = self.get_fixed_point(ddg_init, ddg_gen, ddg_kill, set.union, self.parents, self.childs)
		ddg_tmp = map(lambda i: (i, map(lambda u: map(lambda y: (y[1], bool(re.match("^X[0-9]+$",y[0]))), filter(lambda x: x[0] == u, self.reaching_definitions[i])), self.instructions[i].uses)), self.instructions)
		reducable_instructions = filter(lambda i: self.instructions[i].can_be_reduced and not any(map(lambda x: re.match("^X[0-9]+$", x), self.instructions[i].defines)), self.instructions.keys())
		if self.simplify:
			def compute_new_ddg_tmp(old_ddg_tmp):
				new_ddg_tmp = []
				for x in old_ddg_tmp:
					i = x[0]
					dependencies = []
					for dependency_list in x[1]:
						new_dependency_list = []
						for dependency in dependency_list:
							if dependency[0] in reducable_instructions:
								other_dependencies = dict(old_ddg_tmp)[dependency[0]]
								for other_dependency_list in other_dependencies:
									for other_dependency in other_dependency_list:
										new_dependency_list.append((other_dependency[0], other_dependency[1] or dependency[1]))
							else:
								new_dependency_list.append((dependency))
						dependencies.append(new_dependency_list)
					new_ddg_tmp.append((i, dependencies))
				return new_ddg_tmp
			new_ddg_tmp = compute_new_ddg_tmp(ddg_tmp)
			while new_ddg_tmp != ddg_tmp:
				ddg_tmp = new_ddg_tmp[:]
				new_ddg_tmp = compute_new_ddg_tmp(ddg_tmp)
		self.ddg = dict(map(lambda x: (x[0], map(lambda y: map(lambda z: z[0], y), x[1])), ddg_tmp))
		self.ddg_marked = dict(map(lambda x: (x[0], map(lambda y: map(lambda z: z, y), x[1])), ddg_tmp))
		self.rddg = dict([(i, set()) for i in self.instructions])
		for i in self.ddg.keys():
			if (not simplify) or (i not in reducable_instructions):
				for d in self.ddg[i]:
					for x in d:
						self.rddg[x].add(i)
		# compute dominators
		dom_init = dict([(i, set(self.instructions.keys())) for i in self.instructions])
		last_instruction = filter(lambda x: len(self.childs[x]) == 0, self.instructions)[0]
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
				if (not self.simplify) or (r not in reducable_instructions):
					self.cdg[r].add(b)
					self.rcdg[b].add(r)
		if simplify:
			for i in reducable_instructions:
				del self.ddg[i]
				del self.rddg[i]
				del self.cdg[i]
				del self.rcdg[i]
				del self.instructions[i]

	def get_all_ops(self):
		return set(filter(lambda x: len(x) > 0, map(lambda s: s.op, self.instructions.values())))

	def get_fixed_point(self, init, gen, kill, merge, predecessors, successors):
		in_states = init.copy()
		out_states = init.copy()
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

	def print_graph(self, print_source=False, save_source=False, save_png=False, view=False, name='PDG', mark_variable_dependecies=False):
		try:
			import graphviz
		except:
			print 'Error: graphviz package not installed'
			return
		g = graphviz.Digraph(name, format='png')
		g.attr(rankdir='LR')
		ignored_nodes = set()
		for i in self.instructions.keys():
			instruction = self.instructions[i]
			if isinstance(instruction, VarInstruction):
				if (len(self.cdg[i]) > 0) or (len(self.ddg[i]) > 0) or (len(self.rcdg[i]) > 0) or (
						len(self.rddg[i]) > 0):
					g.node('n_'+str(i), label=instruction.code[4:], shape='circle')
			else:
				if instruction.code not in ['__entry__', '__exit__']:
					g.node('n_' + str(i), label=instruction.code, shape='box')
				else:
					ignored_nodes.add(i)
		if mark_variable_dependecies:
			for i in self.ddg_marked.keys():
				if i not in ignored_nodes:
					for x in self.ddg_marked[i]:
						for j in x:
							if j[0] not in ignored_nodes:
								if j[1]:
									g.edge('n_'+str(j[0]), 'n_'+str(i), color='black:invis:black')
								else:
									g.edge('n_'+str(j[0]), 'n_'+str(i))
		else:
			for i in self.ddg.keys():
				if i not in ignored_nodes:
					for x in self.ddg[i]:
						for j in x:
							if j not in ignored_nodes:
								g.edge('n_'+str(j), 'n_'+str(i))
		for i in self.cdg.keys():
			if i not in ignored_nodes:
				for j in self.cdg[i]:
					if j not in ignored_nodes:
						g.edge('n_'+str(j), 'n_'+str(i), style='dashed')
		if print_source:
			print g.source
		if save_source:
			g.save(name)
		if save_png:
			g.render(name)
		if view:
			g.view(tempfile.mktemp('.gv'))

def compare_graphs(graph1, graph2):
	if graph1.bad_graph or graph2.bad_graph:
		return (False, [])
	if len(graph1.instructions) != len(graph2.instructions):
		return (False, [])
	def add_all_equivalent_ops(ops):
		for op_pair in compiler_api_equivalent_ops:
			if op_pair[0] in ops:
				ops.add(op_pair[1])
			if op_pair[1] in ops:
				ops.add(op_pair[0])
		return ops
	if add_all_equivalent_ops(graph1.get_all_ops()) != add_all_equivalent_ops(graph2.get_all_ops()):
		return (False, [])
	def is_matching_instructions(index1, index2):
		def is_number(x):
			return bool(re.match('^\-?[0-9]+$', x)) or bool(re.match('^N[0-9]+$', x))
		inst1 = graph1.instructions[index1]
		inst2 = graph2.instructions[index2]
		# handle VarInsturctions
		if isinstance(inst1, VarInstruction):
			return (isinstance(inst2, VarInstruction), [])
		if isinstance(inst2, VarInstruction):
			return (False, [])
		if inst1.op != inst2.op:
			if ((inst1.op, inst2.op) not in compiler_api_equivalent_ops) and \
					((inst2.op, inst1.op) not in compiler_api_equivalent_ops):
				return (False, [])
		if inst1.is_condition:
			if inst1.relation != inst2.relation:
				return (False, [])
		if len(inst1.uses) != len(inst2.uses):
			return (False, [])
		numeric_args1 = map(lambda i: (i, is_number(i)), inst1.uses)
		numeric_args2 = map(lambda i: (i, is_number(i)), inst2.uses)
		numeric_count1 = len(filter(lambda x: x[1], numeric_args1))
		numeric_count2 = len(filter(lambda x: x[1], numeric_args2))
		if numeric_count1 != numeric_count2:
			return (False, [])
		if numeric_count1 > 0:
			numeric_values1 = map(lambda x: int(x[0]), filter(lambda x: x[1], numeric_args1))
			numeric_values2 = map(lambda x: int(x[0]), filter(lambda x: x[1], numeric_args2))
			if inst1.is_symmetric:
				numeric_replacements = map(lambda x: filter(lambda (i, j): i != j, zip(numeric_values1, x)), list(itertools.permutations(numeric_values2)))
				if any(map(lambda l: len(l) == 0, numeric_replacements)):
					numeric_replacements = []
				else:
					if len(numeric_replacements) > 1:
						print 'multiple possible replacements'
					numeric_replacements = sorted(numeric_replacements, key=lambda l: len(l))[0]
			else:
				if map(lambda x: x[1], numeric_args1) != map(lambda x: x[1], numeric_args2):
					return (False, [])
				numeric_replacements = filter(lambda (i, j): i != j, zip(numeric_values1, numeric_values2))
		else:
			numeric_replacements = []
		cdg1 = graph1.cdg[index1]
		cdg2 = graph2.cdg[index2]
		if len(cdg1) != len(cdg2):
			return (False, [])
		rcdg1 = graph1.rcdg[index1]
		rcdg2 = graph2.rcdg[index2]
		if len(rcdg1) != len(rcdg2):
			return (False, [])
		ddg1 = graph1.ddg[index1]
		ddg2 = graph2.ddg[index2]
		if len(ddg1) != len(ddg2):
			return (False, [])
		if sorted(map(len,ddg1)) != sorted(map(len,ddg2)):
			return (False, [])
		rddg1 = graph1.rddg[index1]
		rddg2 = graph2.rddg[index2]
		if len(rddg1) != len(rddg2):
			return (False, [])
		return (True, numeric_replacements)
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
		for (x,y) in list(func(ddg1, ddg2)):
			if len(x) == len(y):
				dependency_pairs.update(list(itertools.product(x, y)))
		return len(set(map(lambda x: x[0], dependency_pairs))), dependency_pairs
	all_pairs = list(itertools.product(graph1.instructions.keys(), graph2.instructions.keys()))
	pairs_with_replacements = dict(map(lambda (x, y): ((x, y), is_matching_instructions(x, y)), all_pairs))
	initial_pairs = filter(lambda (x, y): pairs_with_replacements[(x, y)][0], all_pairs)
	perfect_matches = filter(lambda x: len(pairs_with_replacements[x][1]) == 0, initial_pairs)
	non_perfect_matches = filter(lambda x: x not in perfect_matches, initial_pairs)
	redundant_pairs = filter(lambda x: x[0] in map(lambda y: y[0], perfect_matches), non_perfect_matches)
	initial_pairs = filter(lambda x: x not in redundant_pairs, initial_pairs)
	if set(map(lambda x: x[0], initial_pairs)) != set(graph1.instructions.keys()):
		return (False, [])
	if set(map(lambda x: x[1], initial_pairs)) != set(graph2.instructions.keys()):
		return (False, [])
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
		return (False, [])
	if set(map(lambda x: x[1], pairs_dependencies.keys())) != set(graph2.instructions.keys()):
		return (False, [])
	required_replacements = dict(map(lambda (i, j): ((i - 1, j - 1), pairs_with_replacements[(i, j)][1]), sorted(filter(lambda (x, y): isinstance(x, int), pairs_dependencies.keys()))[1:-1]))
	return (True, required_replacements)


def compare_codes(code1, code2, simplify=True):
	return compare_graphs(Graph(code1, simplify=simplify), Graph(code2, simplify=simplify))


def load_external(f):
	if f.endswith('.py'):
		f = f[:-3]
	if f.endswith('.pyc'):
		f = f[:-4]
	return __import__(f)


if __name__ == "__main__":
	import argparse
	parser = argparse.ArgumentParser(description="Parse codes to PDG and compare graphs")
	parser.add_argument('compiler', type=str, help="file containing implementation of 'Instruction' class")
	parser.add_argument('--simplify', action='store_true', help='Simplify graphs')
	args = parser.parse_args()
	set_compiler_api(load_external(args.compiler))
	Graph('jmp .L1 ; .L0 : ; movl X5 , %eax ; movl %eax , X9 ; .L1 : ; movl X2 , %eax ; cmpl 8 , %eax ; jle .L0 ;', simplify=args.simplify).print_graph(view=True)
	# print compare_codes('movl X13 , %eax ; cmpl 62 , %eax ; jne .L0 ; movl X8 , %ebx ; movl X11 , %ecx ; movl 780903145 , %edx ; movl %ecx , %eax ; imull %edx ; sarl 2 , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl X7 , %eax ; subl %eax , %edx ; movl %edx , %eax ; subl %eax , %ebx ; movl %ebx , %eax ; movl %eax , X12 ; .L0 : ;', 'movl X13 , %eax ; cmpl 62 , %eax ; jne .L0 ; movl X8 , %ebx ; movl X11 , %ecx ; movl 780903145 , %edx ; movl %ecx , %eax ; imull %edx ; sarl 2 , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl X7 , %eax ; subl %eax , %ecx ; movl %ecx , %eax ; subl %eax , %ebx ; movl %ebx , %eax ; movl %eax , X12 ; .L0 : ;', simplify=args.simplify)
	# print compare_codes('movl X7 , %eax ; addl 1 , %eax ; movl %eax , X7 ;', 'movl X7 , %eax ; leal 1 ( %eax ) , %edx ; movl %edx , X7 ;', simplify=args.simplify)