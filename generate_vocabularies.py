import logging

def parse_vocabulary(path):
	vocab = []
	with open(path, 'r') as f:
		for l in f.readlines():
			vocab += filter(lambda x: len(x) > 0, l.split())
	return set(vocab)

def generate_vocabs(datasets, out):
	vocab_hl = set()
	vocab_ll = set()
	logging.info('Generating vocabularies for ' + str(datasets))
	for dataset in datasets:
		vocab_ll.update(parse_vocabulary(dataset+'.corpus.ll'))
		vocab_hl.update(parse_vocabulary(dataset+'.corpus.hl'))
	with open(out+'.vocabs.ll', 'w') as f:
		f.write(' '.join(list(vocab_ll))+'\n')
	with open(out+'.vocabs.hl', 'w') as f:
		f.write(' '.join(list(vocab_hl))+'\n')