import numpy.random as npr


def generate_number_replacements(line, config, hl2ll):
	min_abstracted_number = config.getint("Number", "MinAbstractedValue")
	max_abstracted_number = config.getint("Number", "MaxAbstractedValue")
	max_constants = config.getint("Number", "NumbersPerStatement")
	replacements = {}
	parts = line.strip().split(" ")
	for i in range(len(parts)):
		if hl2ll.is_number(parts[i]):
			number = hl2ll.get_number(parts[i])
			if (int(number) >= min_abstracted_number) and (int(number) <= max_abstracted_number):
				if number in replacements.keys():
					constant = replacements[number]
				else:
					free_constants = filter(lambda n: n not in replacements.values(), ['N'+str(j) for j in range(max_constants)])
					if len(free_constants) == 0:
						constant = 'N' + str(npr.randint(0, max_constants))
					else:
						constant = free_constants[npr.randint(0,len(free_constants))]
					replacements[number] = constant
				parts[i] = constant
	return (" ".join(parts), replacements)


def apply_number_replacements(line, replacements):
	parts = line.strip().split(" ")
	for i in range(len(parts)):
		if parts[i] in replacements.keys():
			parts[i] = replacements[parts[i]]
	return " ".join(parts)


def reverse_mapping(replacements):
	reverse_replacement = {}
	for k in replacements.keys():
		reverse_replacement[replacements[k]] = k
	return reverse_replacement