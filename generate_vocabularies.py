import codecs
import logging

def parse_vocabulary(path):
	vocab = []
	with codecs.open(path, encoding='utf8') as f:
		# split sequences by spaces
		for l in f.readlines():
			vocab += filter(lambda x: len(x) > 0, l.split())
	return list(set(vocab))

def generate_vocabs(dataset):
	logging.info('Generating vocabularies for '+dataset)
	with open(dataset+'.vocabs.ll', 'w') as f:
		f.write(' '.join(parse_vocabulary(dataset+'.corpus.ll'))+'\n')
	with open(dataset + '.vocabs.hl', 'w') as f:
		f.write(' '.join(parse_vocabulary(dataset + '.corpus.hl')) + '\n')

def vocabs_contained(container, containee):
	hl_container = set()
	with open(container + '.vocabs.hl', 'w') as f:
		hl_container.update(set(f.readline().strip().split(' ')))
	ll_container = set()
	with open(container + '.vocabs.ll', 'w') as f:
		ll_container.update(set(f.readline().strip().split(' ')))
	hl_containee = set()
	with open(containee + '.vocabs.hl', 'w') as f:
		hl_containee.update(set(f.readline().strip().split(' ')))
	ll_containee = set()
	with open(containee + '.vocabs.ll', 'w') as f:
		ll_containee.update(set(f.readline().strip().split(' ')))
	return hl_containee.issubset(hl_container) and ll_containee.issubset(ll_container)