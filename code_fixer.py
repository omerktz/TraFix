import re
import itertools

class hl_wrapper:
	def __init__(self, hl):
		self.hl = hl
		self.vars = set(filter(lambda x: re.findall("^X[0-9]+$", x.strip()), hl.split(' ')))

	def __str__(self):
		return self.hl

	def collect_vars(self):
		return self.vars

def get_new_values(hl_value, ll_replacements, is_div_or_mul, is_if):
	hl_num = int(hl_value)
	values = set()
	for ll_replacement in ll_replacements:
		ll_num = int(ll_replacement[0][0])
		target_num = int(ll_replacement[0][1])
		if hl_num == ll_num:
			values.add(target_num)
		if is_if:
			values.add(hl_num - ll_num + target_num)
		if is_div_or_mul:
			values.add(int(round(hl_num / float(ll_num) * target_num)))
			if hl_num == 2**ll_num:
				values.add(2**target_num)
	return map(str, values)

def found_right_replacement(remaining_replacements, replacements, relevant_replacements):
	if len(remaining_replacements.keys()) >= len(replacements.keys()):
		return False
	if any(map(lambda x: x not in replacements.keys(), remaining_replacements.keys())):
		return False
	return set(filter(lambda x: x not in remaining_replacements.keys(), replacements.keys())) == set(relevant_replacements)

def try_new_value(new_value, hl_parts, i, ll, compiler, comparison):
	hl_parts[i] = new_value
	fixed_compiled = compiler.compiler(hl_wrapper(' '.join(hl_parts)), True)
	if fixed_compiled is None:
		return None
	comparison_result = comparison.compare_codes(fixed_compiled, ll)
	if not comparison_result[0]:
		return None
	remaining_replacements = comparison_result[1]
	remaining_replacements = dict(map(lambda y: (y, remaining_replacements[y]),
									  filter(lambda x: len(remaining_replacements[x]) > 0,
											 remaining_replacements.keys())))
	return remaining_replacements

def fix_code(hl, ll, compiler, comparison, original_compiled, replacements):
	actual_replacements = dict(filter(lambda x: len(x[1]) > 0, list(replacements.iteritems())))
	if any(map(lambda k: k not in actual_replacements.keys(), filter(lambda y: y[0] in map(lambda x: x[0], actual_replacements.keys()), replacements.keys()))):
		return None
	replacements = actual_replacements
	if any(map(lambda y: len(list(y[1])) > 1, itertools.groupby(replacements.keys(), key=lambda x: x[0]))):
		return None
	if any(map(lambda y: len(y) > 1, replacements.values())):
		return None
	replacements = dict(map(lambda y: (y, replacements[y]), filter(lambda x: len(replacements[x]) > 0, replacements.keys())))
	original_compiled_parts = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), original_compiled.split(';')))
	normalized_original_compiled = re.sub('X[0-9]+', 'X', re.sub(' \-?[0-9]+ ', ' N ', original_compiled))
	hl_parts = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), hl.split(' ')))
	interesting_instructions = map(lambda x: x[0], replacements.keys())
	numbers = filter(lambda x: re.match('^[0-9]+$', hl_parts[x]), range(len(hl_parts)))
	remaining_replacements = replacements
	for i in numbers:
		original_value = hl_parts[i]
		hl_parts[i] = str(int(hl_parts[i]) * 2)
		new_compiled = compiler.compiler(hl_wrapper(' '.join(hl_parts)), True)
		hl_parts[i] = original_value
		normalized_new_compiled = re.sub('X[0-9]+', 'X', re.sub(' \-?[0-9]+ ', ' N ', new_compiled))
		if normalized_new_compiled != normalized_original_compiled:
			continue
		new_compiled_parts = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), new_compiled.split(';')))
		changed_instructions = filter(lambda j: new_compiled_parts[j] != original_compiled_parts[j], range(len(new_compiled_parts)))
		if all(map(lambda j: j not in interesting_instructions, changed_instructions)):
			continue
		relevant_replacements = sorted(filter(lambda x: x[0] in changed_instructions, replacements.keys()))
		hl_parts[i] = original_value
		is_div_or_mul = (hl_parts[i - 1] == '/') or (hl_parts[i - 1] == '*') or (hl_parts[i + 1] == '*')
		is_if = (hl_parts[i - 1] in ['==', '!=', '<', '<=', '>', '>=']) or (hl_parts[i + 1] in ['==', '!=', '<', '<=', '>', '>='])
		for new_value in get_new_values(original_value, map(lambda x: replacements[x], relevant_replacements), is_div_or_mul, is_if):
			new_remaining_replacements = try_new_value(new_value, hl_parts[:], i, ll, compiler, comparison)
			if new_remaining_replacements is None:
				continue
			if found_right_replacement(new_remaining_replacements, replacements, relevant_replacements):
				hl_parts[i] = new_value
				remaining_replacements = new_remaining_replacements
				if len(remaining_replacements.keys()) == 0:
					return ' '.join(hl_parts)
				break
	if len(remaining_replacements) > 0:
		# Most likely need to fix a division
		divs = filter(lambda x: hl_parts[x] == '/', range(len(hl_parts)))
		numbers = map(lambda i: i + 1, divs)
		last_changed = 0
		for i in numbers:
			original_value = hl_parts[i]
			if not re.match('^\-?[0-9]+$', original_value):
				continue
			hl_parts[i] = str(int(original_value) * 2)
			new_compiled = compiler.compiler(hl_wrapper(' '.join(hl_parts)), True)
			hl_parts[i] = original_value
			new_compiled_parts = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), new_compiled.split(';')))
			if len(new_compiled_parts) != len(original_compiled_parts):
				continue
			changed_instructions = filter(lambda j: new_compiled_parts[j] != original_compiled_parts[j], range(len(original_compiled_parts)))
			if len(changed_instructions) != 1:
				# print "Unexpected changed instructions"
				continue
			changed = changed_instructions[0]
			relevant_replacements = sorted(filter(lambda x: x[0] > last_changed and x[0] <= changed, remaining_replacements.keys()))
			if len(relevant_replacements) == 0:
				continue
			original_int = int(original_value)
			new_values = set()
			replacement = replacements[relevant_replacements[0]][0]
			constant0 = int(replacement[0])
			constant1 = int(replacement[1])
			if len(relevant_replacements) == 1:
				if (constant0 > 0) and (constant0 <= 32):
					if (constant1 > 0) and (constant1 <= 32):
						if constant0 - constant1 > 0:
							new_values.add(original_int >> (constant0 - constant1))
						else:
							new_values.add(original_int << (constant1 - constant0))
				else:
					new_values.add(original_int * constant0 / float(constant1))
					new_values.add(original_int * (constant0 + (1 << 32)) / float(constant1 + (1 << 32)))
			elif len(replacements) == 2:
				power_replacement = map(lambda x: int(x), replacements[relevant_replacements[1]][0])
				if (power_replacement[0] > 0) and (power_replacement[0] <= 32) and (power_replacement[1] > 0) and (power_replacement[1] <= 32):
					try:
						if original_int * constant0 >> (power_replacement[0] + 32) == 1:
							new_values.add((1 << (32 + power_replacement[1])) / float(constant1))
						elif original_int * (constant0 + (1 << 32)) >> (power_replacement[0] + 32) == 1:
							new_values.add((1 << (32 + power_replacement[1])) / float(constant1 + (1 << 32)))
						else:
							# print "Unknown div to mul pattern"
							# print map(lambda x: (x, replacements[x]), relevant_replacements)
							pass
					except OverflowError:
						pass
			for new_value in new_values:
				new_value_str = str(int(round(new_value)))
				new_remaining_replacements = try_new_value(str(new_value_str), hl_parts[:], i, ll, compiler, comparison)
				if new_remaining_replacements is None:
					continue
				if found_right_replacement(new_remaining_replacements, replacements, relevant_replacements):
					hl_parts[i] = str(new_value_str)
					remaining_replacements = new_remaining_replacements
					if len(remaining_replacements.keys()) == 0:
						return ' '.join(hl_parts)
					break
			last_changed = changed
	return None


def fix_conditions_equality(hl, ll, compiler, comparison):
	def is_correct_conditions(original, candidate):
		original_no_nums = re.sub(' \-?[0-9]+ ', ' 1337 ', re.sub(' X[0-9]+$ ', ' X1 ', original))
		compiled_candidate = compiler.compiler(hl_wrapper(candidate), True)
		if compiled_candidate is None:
			return False
		compiled_candidate_no_nums = re.sub(' \-?[0-9]+ ', ' 1337 ', re.sub(' X[0-9]+$ ', ' X1 ', compiled_candidate))
		comparison_result = comparison.compare_codes(compiled_candidate_no_nums, original_no_nums)
		return comparison_result[0]
	def count_conditions(code):
		conds = filter(lambda c: c.strip() in ['je', 'jne'], code.split(' '))
		res = {}
		for c in conds:
			if c not in res.keys():
				res[c] = 1
			else:
				res[c] += 1
		return res
	def diff_counts(lhs, rhs):
		res = {}
		for k in lhs.keys():
			if k not in rhs.keys():
				res[k] = lhs[k]
			else:
				if lhs[k] > rhs[k]:
					res[k] = lhs[k] - rhs[k]
		return res
	def effective_change(hl_parts, compiled, i, to_replace):
		def opposite_cond(cond):
			if cond == '==':
				return '!='
			if cond == '!=':
				return '=='
		normalized_compiled = re.sub(' \-?[0-9]+ ', ' N ', re.sub(' X[0-9]+$ ', ' X ', compiled)).split(' ')
		cond = hl_parts[i]
		hl_parts[i] = opposite_cond(cond)
		new_compiled = compiler.compiler(hl_wrapper(' '.join(hl_parts)), True)
		hl_parts[i] = cond
		normalized_new_compiled = re.sub(' \-?[0-9]+ ', ' N ', re.sub(' X[0-9]+$ ', ' X ', new_compiled)).split(' ')
		if len(normalized_compiled) != len(normalized_new_compiled):
			return None
		indexes = filter(lambda i: normalized_compiled[i] != normalized_new_compiled[i], range(len(normalized_compiled)))
		if len(filter(lambda i: normalized_compiled[i] in to_replace, indexes)) > 0:
			return (i, hl_parts[i], normalized_compiled[indexes[0]])
		else:
			return None
	def categorize_cond_change(input, output):
		if (input == '==' and output == 'jne') or (input == '!=' and output == 'je'):
			return True
		return False
	def apply_cond_change(target, negate):
		def target_to_cond(target):
			if target == 'je':
				return '=='
			if target == 'jne':
				return '!='
		if negate:
			if target == 'je':
				target = 'jne'
			else:
				target = 'je'
		return target_to_cond(target)
	ll_conds = count_conditions(ll)
	compiled = compiler.compiler(hl_wrapper(hl), True)
	compiled_conds = count_conditions(compiled)
	to_replace = diff_counts(compiled_conds, ll_conds)
	replace_with = diff_counts(ll_conds, compiled_conds)
	hl_parts = hl.split(' ')
	hl_conds = filter(lambda i: hl_parts[i].strip() in ['==', '!='], range(len(hl_parts)))
	effective_changes = filter(lambda x: x is not None, map(lambda i: effective_change(hl_parts[:], compiled, i, to_replace.keys()), hl_conds))
	categorized_changes = map(lambda x: (x[0], categorize_cond_change(x[1], x[2])), effective_changes)

	print hl_conds, to_replace, replace_with, effective_changes, categorized_changes

def fix_conditions(hl, ll, compiler, comparison):
	def is_correct_conditions(original, candidate):
		original_no_nums = re.sub(' \-?[0-9]+ ', ' 1337 ', re.sub(' X[0-9]+$ ', ' X1 ', original))
		compiled_candidate = compiler.compiler(hl_wrapper(candidate), True)
		if compiled_candidate is None:
			return False
		compiled_candidate_no_nums = re.sub(' \-?[0-9]+ ', ' 1337 ', re.sub(' X[0-9]+$ ', ' X1 ', compiled_candidate))
		comparison_result = comparison.compare_codes(compiled_candidate_no_nums, original_no_nums)
		return comparison_result[0]
	def count_conditions(code):
		conds = filter(lambda c: c.strip().startswith('j') and c not in ['jmp', 'je', 'jne'], code.split(' '))
		res = {}
		for c in conds:
			if c not in res.keys():
				res[c] = 1
			else:
				res[c] += 1
		return res
	def diff_counts(lhs, rhs):
		res = {}
		for k in lhs.keys():
			if k not in rhs.keys():
				res[k] = lhs[k]
			else:
				if lhs[k] > rhs[k]:
					res[k] = lhs[k] - rhs[k]
		return res
	def effective_change(hl_parts, compiled, i, to_replace):
		def opposite_cond(cond):
			if cond == '<':
				return '>'
			if cond == '>':
				return '<'
			if cond == '<=':
				return '>='
			if cond == '>=':
				return '<='
		normalized_compiled = re.sub(' \-?[0-9]+ ', ' N ', re.sub(' X[0-9]+$ ', ' X ', compiled)).split(' ')
		cond = hl_parts[i]
		hl_parts[i] = opposite_cond(cond)
		new_compiled = compiler.compiler(hl_wrapper(' '.join(hl_parts)), True)
		hl_parts[i] = cond
		normalized_new_compiled = re.sub(' \-?[0-9]+ ', ' N ', re.sub(' X[0-9]+$ ', ' X ', new_compiled)).split(' ')
		if len(normalized_compiled) != len(normalized_new_compiled):
			return None
		indexes = filter(lambda i: normalized_compiled[i] != normalized_new_compiled[i], range(len(normalized_compiled)))
		if len(filter(lambda i: normalized_compiled[i] in to_replace, indexes)) > 0:
			return (i, hl_parts[i], normalized_compiled[indexes[0]])
		else:
			return None
	def categorize_cond_change(i, input, output):
		add_equlity = False
		negate_direction = False
		if input in ['>', '<'] and output in ['jle', 'jge']:
			add_equlity = True
		if input in ['>=', '<='] and output in ['jl', 'jg']:
			add_equlity = True
		if input in ['>', '>='] and output in ['jl', 'jle']:
			negate_direction = True
		if input in ['<', '<='] and output in ['jg', 'jgr']:
			negate_direction = True
		return (i, negate_direction, add_equlity)
	def apply_cond_change(target, negate_direction, add_equality):
		def target_to_cond(target):
			if target == 'jg':
				return '>'
			if target == 'jge':
				return '>='
			if target == 'jl':
				return '<'
			if target == 'jle':
				return '<='
		if negate_direction:
			if target.startswith('jl'):
				target = 'jg'+target[2:]
			if target.startswith('jg'):
				target = 'jl' + target[2:]
		if add_equality:
			if len(target) == 3:
				target = target[:2]
			else:
				target += 'e'
		return target_to_cond(target)
	ll_conds = count_conditions(ll)
	compiled = compiler.compiler(hl_wrapper(hl), True)
	compiled_conds = count_conditions(compiled)
	to_replace = diff_counts(compiled_conds, ll_conds)
	replace_with = diff_counts(ll_conds, compiled_conds)
	hl_parts = hl.split(' ')
	hl_conds = filter(lambda i: hl_parts[i].strip() in ['==', '!=', '>', '>=', '<', '<='], range(len(hl_parts)))
	effective_changes = filter(lambda x: x is not None, map(lambda i: effective_change(hl_parts[:], compiled, i, to_replace.keys()), hl_conds))
	categorized_changes = map(lambda x: categorize_cond_change(*x), effective_changes)
	print hl_conds, to_replace, replace_with, effective_changes, categorized_changes

def fix_variables(hl, ll, compiler, comparison):
	def is_correct_variables(original, candidate):
		original_no_nums = re.sub(' \-?[0-9]+ ', ' 1337 ', original)
		compiled_candidate = compiler.compiler(hl_wrapper(candidate), True)
		if compiled_candidate is None:
			return False
		compiled_candidate_no_nums = re.sub(' \-?[0-9]+ ', ' 1337 ', compiled_candidate)
		comparison_result = comparison.compare_codes(compiled_candidate_no_nums, original_no_nums)
		return comparison_result[0]
	def count_variables(code):
		vars = filter(lambda c: re.match('^X[0-9]+$', c.strip()), code.split(' '))
		res = {}
		for v in vars:
			if v not in res.keys():
				res[v] = 1
			else:
				res[v] += 1
		return res
	def diff_counts(lhs, rhs):
		res = {}
		for k in lhs.keys():
			if k not in rhs.keys():
				res[k] = lhs[k]
			else:
				if lhs[k] > rhs[k]:
					res[k] = lhs[k] - rhs[k]
		return res
	def effective_change(hl_parts, compiled, i, to_replace):
		normalized_compiled = re.sub(' \-?[0-9]+ ', ' N ', compiled).split(' ')
		hl_parts[i] += '0'
		new_compiled = compiler.compiler(hl_wrapper(' '.join(hl_parts)), True)
		hl_parts[i] = hl_parts[i][:-1]
		normalized_new_compiled = re.sub(' \-?[0-9]+ ', ' N ', new_compiled).split(' ')
		if len(normalized_compiled) != len(normalized_new_compiled):
			return False
		indexes = filter(lambda i: normalized_compiled[i] != normalized_new_compiled[i], range(len(normalized_compiled)))
		return len(filter(lambda i: normalized_compiled[i] in to_replace, indexes)) > 0
	ll_vars = count_variables(ll)
	compiled = compiler.compiler(hl_wrapper(hl), True)
	compiled_vars = count_variables(compiled)
	to_replace = diff_counts(compiled_vars, ll_vars)
	replace_with = diff_counts(ll_vars, compiled_vars)
	hl_parts = hl.split(' ')
	hl_vars = filter(lambda i: re.match('^X[0-9]+$', hl_parts[i].strip()), range(len(hl_parts)))
	effective_changes = filter(lambda i: effective_change(hl_parts[:], compiled, i, to_replace.keys()), hl_vars)
	print hl_vars, to_replace, replace_with, effective_changes

if __name__ == "__main__":
	import x86Util
	import graph_comparison
	fix_variables('X2 = X2 + 1 ;', 'movl X2 , %eax ; addl 1 , %eax ; movl %eax , X1 ;', x86Util, graph_comparison)
	fix_conditions('if ( X1 > 10 ) { X2 = 3 ; }', 'movl X1 , %eax ; cmpl 9 , %eax ; jg .L0 ; movl 3 , X2 ; .L0 : ;', x86Util, graph_comparison)
	fix_conditions_equality('if ( X1 == 10 ) { X2 = 3 ; }', 'movl X1 , %eax ; cmpl 10 , %eax ; je .L0 ; movl 3 , X2 ; .L0 : ;', x86Util, graph_comparison)
