import math


def main(args):
	import os
	import ConfigParser
	config = ConfigParser.ConfigParser()
	tf_nmt = os.path.abspath('tf_nmt/src/tf_nmt.py')
	train_py = 'nmt.nmt'
	config.read(args['config'])
	train_dataset = os.path.abspath(args['training_dataset'])
	validation_dataset = os.path.abspath(args['validation_dataset'])
	test = os.path.abspath(args['test_dataset'])
	vocabs = os.path.abspath(args['vocabs'])
	model_path = os.path.abspath(args['model_path'])
	previous = (' --previous-model=%s' % os.path.abspath(args['previous'] + '.ll-hl.tf_nmt')) if args['previous'] is not None else ''
	num_train_steps = config.getint('TensorFlow', 'batch_size') * config.getint('TensorFlow', 'epochs')
	valid_steps = int(math.floor(args['data_set_size'] / config.getint('TensorFlow', 'batch_size'))) if args[
																									 'data_set_size'] is not None else 300
	train_command = (
				'python -m ' + train_py + ' --vocab_prefix={0} --train_prefix={1} --dev_prefix={2} --out_dir={3} --num_train_steps={4} --steps_per_stats={5} --num_layers={6} --num_units={7} --metrics={8} --src=ll --tgt=hl --attention=bahdanau --batch_size={9} --src_max_len=1500 --tgt_max_len=150 --max_gradient_norm={10} --optimizer={11} --encoder_type=bi --num_keep_ckpts={12}'.format(
				vocabs, train_dataset, validation_dataset, model_path, num_train_steps, valid_steps, config.getint('TensorFlow', 'lstm_layers'), config.getint('TensorFlow', 'rnn_size'), 'bleu', config.getint('TensorFlow', 'batch_size'), config.getint('TensorFlow', 'max_gradient_norm'), config.getstr('TensorFlow', 'optimizer'), config.getint('TensorFlow', 'models_to_save')))

	train_command = train_command.strip()

	trans_command = ''

	if args['train']:
		os.system(train_command)
	if args['translate']:
		import subprocess
		import re
		with open(test + '.corpus.' + str(args['num_translations']) + '.out', 'w') as f:
			translations = False
			current = None
			for line in subprocess.Popen(trans_command.split(' '), stdout=subprocess.PIPE).stdout:
				print line,
				line = line.strip()
				if not translations:
					if line == 'predicting...':
						translations = True
				else:
					if re.match('^[0-9]+/[0-9]+$', line):
						current = line[:line.find('/')]
					if re.match('^[0-9]+\-best\: ', line):
						f.write(current + ' ||| ' + line[line.find(':') + 1:].strip() + ' ||| \n')
	# if args['cleanup']:
	# 	import glob
	# 	files = filter(os.path.isfile, glob.glob(model + '*[0-9].*txt'))
	# 	for f in files:
	# 		os.remove(f)
	# 	files = filter(os.path.isfile, glob.glob(model + '*[0-9].*png'))
	# 	for f in files:
	# 		os.remove(f)


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
	parser.add_argument('-c', '--config', type=str, default='configs/tf_nmt.config',
						help="configuration file (default: \'%(default)s\')")
	parser.add_argument('--cleanup', help="remove all intermediate files after training", action='count')
	parser.add_argument('--silent', help="hide all output", action='count')
	parser.add_argument('--override', help="override existing model", action='count')
	parser.add_argument('-s', '--seed', type=int, help="random seed")
	parser.add_argument('-e', '--epochs', type=int, help="number of epochs to train")
	parser.add_argument('-p', '--previous', type=str, help="previous model to use as baseline")
	args = parser.parse_args()

	if (args.train and args.translate) or not (args.train or args.translate):
		parser.error('You should choose either --train or --translate (exactly one, not both)')

	main(vars(args))
