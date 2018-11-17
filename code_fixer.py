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
			values.add(hl_num / float(ll_num) * target_num)
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
	comparison_result = comparison.compare_codes(fixed_compiled, ll)
	if not comparison_result[0]:
		return None
	remaining_replacements = comparison_result[1]
	remaining_replacements = dict(map(lambda y: (y, remaining_replacements[y]),
									  filter(lambda x: len(remaining_replacements[x]) > 0,
											 remaining_replacements.keys())))
	return remaining_replacements

def fix_code(hl, ll, compiler, comparison, original_compiled, replacements):
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
		normalized_new_compiled = re.sub('X[0-9]+', 'X', re.sub(' \-?[0-9]+ ', ' N ', new_compiled))
		if normalized_new_compiled != normalized_original_compiled:
			hl_parts[i] = original_value
			continue
		new_compiled_parts = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), new_compiled.split(';')))
		changed_instructions = filter(lambda j: new_compiled_parts[j] != original_compiled_parts[j], range(len(new_compiled_parts)))
		if all(map(lambda j: j not in interesting_instructions, changed_instructions)):
			hl_parts[i] = original_value
			continue
		relevant_replacements = sorted(filter(lambda x: x[0] in changed_instructions, replacements.keys()))
		hl_parts[i] = original_value
		is_div_or_mul = (hl_parts[i - 1] == '/') or (hl_parts[i - 1] == '*') or (hl_parts[i + 1] == '*')
		is_if = (hl_parts[i - 1] in ['==', '!=', '<', '<=', '>', '>=']) or (hl_parts[i + 1] in ['==', '!=', '<', '<=', '>', '>='])
		for new_value in get_new_values(original_value, map(lambda x: replacements[x], relevant_replacements), is_div_or_mul, is_if):
			new_remaining_replacements = try_new_value(new_value, hl_parts, i, ll, compiler, comparison)
			if new_remaining_replacements is None:
				hl_parts[i] = original_value
				continue
			if len(new_remaining_replacements.keys()) == 0:
				hl_parts[i] = new_value
				return ' '.join(hl_parts)
			if found_right_replacement(new_remaining_replacements, replacements, relevant_replacements):
				remaining_replacements = new_remaining_replacements
				break
			hl_parts[i] = original_value
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
			new_compiled_parts = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), new_compiled.split(';')))
			if len(new_compiled_parts) != len(original_compiled_parts):
				hl_parts[i] = original_value
				continue
			changed_instructions = filter(lambda j: new_compiled_parts[j] != original_compiled_parts[j], range(len(original_compiled_parts)))
			if len(changed_instructions) != 1:
				# print "Unexpected changed instructions"
				hl_parts[i] = original_value
				continue
			changed = changed_instructions[0]
			relevant_replacements = sorted(filter(lambda x: x[0] > last_changed and x[0] <= changed, remaining_replacements.keys()))
			if len(relevant_replacements) == 0:
				hl_parts[i] = original_value
				continue
			original_int = int(original_value)
			new_values = set()
			replacement = replacements[relevant_replacements[0]][0]
			constant0 = int(replacement[0])
			constant1 = int(replacement[1])
			if len(relevant_replacements) == 1:
				if (constant0 > 0) and (constant0 <= 32):
					try:
						new_values.add(original_int / float(2 ** (constant0 - constant1)))
					except ZeroDivisionError:
						pass
				else:
					new_values.add(original_int * constant0 / float(constant1))
					new_values.add(original_int * (constant0 + (2 ** 32))/float(constant1 + (2 ** 32)))
			elif len(replacements) == 2:
				power_replacement = replacements[relevant_replacements[1]][0]
				try:
					if int(round(original_int * constant0 / float(2**int(power_replacement[0])) / float(2**32))) == 1:
						new_values.add(2**(32 + int(power_replacement[1]))/float(constant1))
					elif int(round(original_int * (constant0 + 2**32) / float(2**int(power_replacement[0])) / float(2**32))) == 1:
						new_values.add(2**(32 + int(power_replacement[1]))/float(constant1 + 2**32))
					else:
						# print "Unknown div to mul pattern"
						# print map(lambda x: (x, replacements[x]), relevant_replacements)
						pass
				except ZeroDivisionError:
					pass
				except OverflowError:
					pass
			for new_value in new_values:
				new_value_str = str(int(round(new_value)))
				new_remaining_replacements = try_new_value(str(new_value_str), hl_parts, i, ll, compiler, comparison)
				if new_remaining_replacements is None:
					hl_parts[i] = original_value
					continue
				if len(new_remaining_replacements.keys()) == 0:
					hl_parts[i] = str(new_value_str)
					return ' '.join(hl_parts)
				if found_right_replacement(new_remaining_replacements, replacements, relevant_replacements):
					remaining_replacements = new_remaining_replacements
					break
				hl_parts[i] = original_value
			last_changed = changed
	return None
