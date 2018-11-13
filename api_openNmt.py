import math
import re


def main(args):
	import os
	import ConfigParser
	config = ConfigParser.ConfigParser()
	train_py = os.path.abspath('open_nmt/train.py')
	translate_py = os.path.abspath('open_nmt/translate.py')
	config.read(args['config'])
	train_dataset = os.path.abspath(args['training_dataset'])
	test_dataset = os.path.abspath(args['test_dataset']) + '.corpus.ll'
	first_translation_output = os.path.abspath(args['test_dataset']) + '.translated'
	model = os.path.abspath(args['model_path'] + '.ll_hl_openNmt')
	previous = (' -train_from %s' % os.path.abspath(args['previous'] + '.ll_hl_openNmt')) if args['previous'] is not None else ''
	# default value 300. mostly for times that we use translate
	valid_steps = int(math.floor(args['data_set_size'] / config.getint('OpenNmt', 'batch_size'))) if args['data_set_size'] is not None else 300
	if valid_steps == 0:
		valid_steps = 10

	train_command = ('python ' + train_py + ' -data {0} -save_model {1} -encoder_type brnn -word_vec_size {2} -rnn_size {3} -layers {4} ' \
		'-global_attention general -valid_steps {5} -batch_size {6} -min_epochs {7} -max_patience {8} ' + previous) \
		.format(train_dataset, model, config.getint('OpenNmt', 'word_vec_size') , config.getint('OpenNmt', 'rnn_size'),
				config.getint('OpenNmt', 'lstm_layers'), valid_steps, config.getint('OpenNmt', 'batch_size'), config.getint('OpenNmt', 'min_epochs'),
				config.getint('OpenNmt', 'max_patience'))

	train_command = train_command.strip()

	translate_command = ('python ' + translate_py + ' -model {0} -src {1} -output {2} -n_best {3}') \
		.format(model, test_dataset, first_translation_output, args['num_translations'])

	translate_command = translate_command.strip()

	if args['train']:
		os.system(train_command)

	if args['translate']:
		os.system(translate_command)
		with open(first_translation_output) as fp:
			w = open(os.path.abspath(args['test_dataset']) + '.corpus.' + str(args['num_translations']) + '.out', "w+")
			lines = fp.readlines()
			lines = filter(lambda x: not re.match('\n',x), lines)
			i = 0
			for line in lines:
				lineToWrite = str(int(math.floor(i / args['num_translations']))) + ' ||| ' + line.replace('\n',' ||| \n')
				w.write(lineToWrite)
				i += 1
			w.close()

	if args['cleanup']:
		import glob
		files = filter(os.path.isfile, glob.glob(model + '*[0-9].*txt'))
		for f in files:
			os.remove(f)
		files = filter(os.path.isfile, glob.glob(model + '*[0-9].*png'))
		for f in files:
			os.remove(f)


if __name__ == "__main__":
	import argparse
	parser = argparse.ArgumentParser(description="Train and test translation model")
	parser.add_argument('training_dataset', type=str, help="dataset for training")
	parser.add_argument('test_dataset', type=str, help="dataset for evaluation")
	parser.add_argument('-m', '--model_path', type=str, default='model',
						help="name of trained model (default: \'%(default)s\')")
	parser.add_argument('--train', help="train a new model", action='count')
	parser.add_argument('--translate', help="translate using an existing model", action='count')
	parser.add_argument('-n', '--num_translations', type=int, default=5,
						help="number of translations for each input (default: %(default)s)")
	parser.add_argument('-c', '--config', type=str, default='configs/openNmt.config',
						help="configuration file (default: \'%(default)s\')")
	parser.add_argument('--cleanup', help="remove all intermediate files after training", action='count')
	parser.add_argument('--silent', help="hide all output", action='count')
	parser.add_argument('--override', help="override existing model", action='count')
	parser.add_argument('-s', '--seed', type=int, help="random seed")
	parser.add_argument('-e', '--epochs', type=int, help="number of epochs to train")
	parser.add_argument('-p', '--previous', type=str, help="previous model to use as baseline")
	parser.add_argument('-d', '--data_set_size', type=int, help="number of sentences in the data_set")
	args = parser.parse_args()

	if (args.train and args.translate) or not (args.train or args.translate):
		parser.error('You should choose either --train or --translate (exactly one, not both)')

	main(vars(args))
