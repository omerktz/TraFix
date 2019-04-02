import logging
import re

def parse_vocabulary(path, split_numbers):
	vocab = []
	with open(path, 'r') as f:
		for l in f.readlines():
			new_words = filter(lambda x: len(x) > 0, map(lambda y: y.strip(), l.split()))
			if split_numbers:
				new_words = filter(lambda z: not re.match('^\-?[0-9]+$', z), new_words)
			vocab += new_words
	return set(vocab)

def generate_vocabs(datasets, out, split_ll_numbers, split_hl_numbers):
	vocab_hl = set()
	vocab_ll = set()
	initial_vocab = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '-N', '|']
	if split_ll_numbers:
		vocab_ll.update(initial_vocab)
	if split_hl_numbers:
		vocab_hl.update(initial_vocab)
	logging.info('Generating vocabularies for ' + str(datasets))
	for dataset in datasets:
		vocab_ll.update(parse_vocabulary(dataset+'.corpus.ll', split_ll_numbers))
		vocab_hl.update(parse_vocabulary(dataset+'.corpus.hl', split_hl_numbers))
	with open(out+'.vocabs.ll', 'w') as f:
		f.write(' '.join(list(vocab_ll))+'\n')
	with open(out+'.vocabs.hl', 'w') as f:
		f.write(' '.join(list(vocab_hl))+'\n')