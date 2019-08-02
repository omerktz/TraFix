import re

def merge_digits_to_numbers(line):
	tokens = line.split(' ')
	new_tokens = []
	number = ''
	for i in range(len(tokens)):
		token = tokens[i]
		if token == '-N':
			number = '-'
		elif token in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']:
			number += token
		else:
			if len(number) > 0:
				new_tokens += [number]
				number = ''
			if token != 'NS':
				new_tokens += [token]
	if len(number) > 0:
		new_tokens += [number]
	return ' '.join(new_tokens)

def split_numbers_to_digits(tokens):
    new_tokens = []
    for i in range(len(tokens)):
        token = tokens[i]
        if re.match('^\-?[0-9]+$', token):
            digits = list(token)
            if digits[0] == '-':
                digits = ['-N'] + digits[1:]
            if i+1 < len(tokens):
                if re.match('^\-?[0-9]+$', tokens[i+1]):
                    digits += ['NS']
            new_tokens += digits
        else:
            new_tokens += [token]
    return new_tokens

