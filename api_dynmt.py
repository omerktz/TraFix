from digits_utils import merge_digits_to_numbers
import os
import ConfigParser


def main(args):
	config = ConfigParser.ConfigParser()
	dynmt = os.path.abspath('dynmt/dynmt.py')
	config.read(args['nmt_config'])
	train = os.path.abspath(args['training_dataset'])
	validation = os.path.abspath(args['validation_dataset'])
	test = os.path.abspath(args['test_dataset'])
	vocabs = os.path.abspath(args['vocabs'])
	model = os.path.abspath(args['model_path'] + '.dynmt')
	previous = (' --previous-model=%s' % os.path.abspath(args['previous_model'] + '.dynmt')) if args['previous_model'] is not None else ''
	split_in_numbers_to_digits = config.getboolean('NMT', 'split_ll_numbers_to_digits')
	split_out_numbers_to_digits = config.getboolean('NMT', 'split_hl_numbers_to_digits')
	command = 'python ' + dynmt + ' --dynet-autobatch 0 {0}.corpus.ll {0}.corpus.hl {1}.corpus.ll {1}.corpus.hl ' \
								  '{2}.corpus.ll {2}.corpus.hl {3} {4}.vocabs.ll {4}.vocabs.hl --epochs={5} ' \
								  '--batch-size={6} --eval-after={7} --max-patience={8} --beam-size={9} --max-pred={10} ' \
								  '--max-len={11} --min-epochs={12} --lstm-layers={13} --split-numbers-in={14} ' \
								  '--split-numbers-out={15} --models-to-save={16}{17}{18}' \
		.format(train, validation, test, model, vocabs, config.getint('NMT', 'epochs'),
				config.getint('NMT', 'batch_size'), config.getint('NMT', 'eval_after'),
				config.getint('NMT', 'max_patience'), 1 if args['train'] else args['num_translations'],
				config.getint('NMT', 'max_pred'), config.getint('NMT', 'max_len'), config.getint('NMT', 'min_epochs'),
				config.getint('NMT', 'lstm_layers'), split_in_numbers_to_digits, split_out_numbers_to_digits,
				config.getint('NMT', 'models_to_save'), ' --eval' if args['translate'] else '',
				(' --seed=%d' % args['seed']) if args['seed'] else '')
	command = command.strip()
	if args['train']:
		os.system(command)
	if args['translate']:
		import subprocess
		import re
		with open(test + '.corpus.' + str(args['num_translations']) + '.out', 'w') as f:
			translations = False
			current = None
			for line in subprocess.Popen(command.split(' '), stdout=subprocess.PIPE).stdout:
				print line,
				line = line.strip()
				if not translations:
					if line == 'predicting...':
						translations = True
				else:
					if re.match('^[0-9]+/[0-9]+$', line):
						current = line[:line.find('/')]
					if re.match('^[0-9]+\-best\: ', line):
						translation = line[line.find(':') + 1:].strip()
						if split_out_numbers_to_digits:
							translation = merge_digits_to_numbers(translation)
						f.write(current + ' ||| ' + translation + ' ||| \n')


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Train and test translation model")
	parser.add_argument('training_dataset', type=str, help="dataset for training")
	parser.add_argument('validation_dataset', type=str, help="dataset for validation")
	parser.add_argument('test_dataset', type=str, help="dataset for evaluation")
	parser.add_argument('vocabs', type=str, help="vocabularies for datasets")
	parser.add_argument('-m', '--model_path', type=str, default='model',
						help="name of trained model (default: \'%(default)s\')")
	parser.add_argument('--train', help="train a new model", action='count')
	parser.add_argument('--translate', help="translate using an existing model", action='count')
	parser.add_argument('-n', '--num_translations', type=int, default=5,
						help="number of translations for each input (default: %(default)s)")
	parser.add_argument('-c', '--nmt_config', type=str, default='configs/nmt.config',
						help="configuration file (default: \'%(default)s\')")
	parser.add_argument('-t', '--framework_config', type=str, help="Ignored!")
	parser.add_argument('-s', '--seed', type=int, help="random seed")
	parser.add_argument('-p', '--previous_model', type=str, help="previous model to use as baseline")
	parser.add_argument('-v', '--previous_vocabs', type=str, help="Ignored!")
	parser.add_argument('-i', '--iteration_num', type=int, default=0, help="Ignored!")
	args = parser.parse_args()

	if (args.train and args.translate) or not (args.train or args.translate):
		parser.error('You should choose either --train or --translate (exactly one, not both)')

	main(vars(args))
