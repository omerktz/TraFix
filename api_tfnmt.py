import math
from digits_utils import merge_digits_to_numbers
import os
import ConfigParser


def main(args):
	nmt_config = ConfigParser.ConfigParser()
	tf_config = ConfigParser.ConfigParser()
	tfnmt = 'tfnmt.nmt'
	nmt_config.read(args['nmt_config'])
	tf_config.read(args['framework_config'])
	model = os.path.abspath(args['model_path'] + '.tfnmt')
	src_suffix = 'll'
	tgt_suffix = 'hl'
	vocabs = os.path.abspath(args['vocabs'])
	split_in_numbers_to_digits = nmt_config.getboolean('NMT', 'split_ll_numbers_to_digits')
	split_out_numbers_to_digits = nmt_config.getboolean('NMT', 'split_hl_numbers_to_digits')
	if (args['previous_model'] is not None) and (args['previous_vocabs'] is not None):
		os.mkdir(model)
		old_vocabs = args['previous_vocabs']
		# update the vocabulary of new model
		os.system(
			'python -m tfnmt.scripts.update_vocab --model_dir {0} --output_dir {1} --src_vocab {2} --tgt_vocab {3} --new_src_vocab {4} --new_tgt_vocab {5} --mode replace'.format(
				args['previous_model'] + '.tfnmt', model, old_vocabs + '.' + src_suffix, old_vocabs + '.' + tgt_suffix,
				vocabs + '.' + src_suffix, vocabs + '.' + tgt_suffix))
	if args['train']:
		train_dataset = os.path.abspath(args['training_dataset']+'.corpus')
		validation_dataset = os.path.abspath(args['validation_dataset']+'.corpus')
		if args['iteration_num'] == 0:
			learning_rate = tf_config.getfloat('TensorFlow', 'learning_rate_initial')
			max_gradient_norm = tf_config.getint('TensorFlow', 'max_gradient_norm_initial')
		else:
			learning_rate = tf_config.getfloat('TensorFlow', 'learning_rate')
			max_gradient_norm = tf_config.getint('TensorFlow', 'max_gradient_norm')
		train_command = (
				'python -m ' + tfnmt + ' --vocab_prefix={0} --train_prefix={1} --dev_prefix={2} --out_dir={3} ' \
				'--num_train_steps=10000000 --steps_per_stats={4} --num_layers={5} --num_units={6} --metrics=bleu ' \
				'--src={7} --tgt={8} --attention=luong --batch_size={9} --max_gradient_norm={10} --optimizer={11} ' \
				'--encoder_type=bi --num_keep_ckpts={12} --learning_rate={13} --steps_per_valid={14} --patience={15} '\
				'--src_max_len={16} --tgt_max_len={17} --split_numbers_in={18} --split_numbers_out={19}'.format(
			vocabs, train_dataset, validation_dataset, model, nmt_config.getint('NMT', 'eval_after'),
			nmt_config.getint('NMT', 'lstm_layers') * 2, tf_config.getint('TensorFlow', 'rnn_size'), src_suffix,
			tgt_suffix, nmt_config.getint('NMT', 'batch_size'),	max_gradient_norm,
			tf_config.get('TensorFlow', 'optimizer'), nmt_config.getint('NMT', 'models_to_save'),
			learning_rate, nmt_config.getint('NMT', 'eval_after'), nmt_config.getint('NMT', 'max_patience'),
			nmt_config.getint('NMT', 'max_len'), nmt_config.getint('NMT', 'max_pred'),
			split_in_numbers_to_digits, split_out_numbers_to_digits)).strip()
		os.system(train_command)
	if args['translate']:
		test = os.path.abspath(args['test_dataset'])
		tmp_output = test + '.translated'
		trans_command = 'python -m ' + tfnmt + ' --out_dir={0} --inference_input_file={1} --inference_output_file={2} ' \
						'--num_translations_per_input={3} --infer_mode=beam_search --beam_width={3} --attention=luong ' \
						'--tgt_max_len_infer={4} --split_numbers_in={5} --split_numbers_out={6}'.format(
			model, test + '.corpus.'+src_suffix, tmp_output, str(args['num_translations']),
			nmt_config.getint('NMT', 'max_pred'), split_in_numbers_to_digits, split_out_numbers_to_digits).strip()
		os.system(trans_command)
		with open(tmp_output) as fp:
			with open(test + '.corpus.' + str(args['num_translations']) + '.out', "w+") as w:
				lines = [l.strip() for l in fp.readlines()]
				if split_out_numbers_to_digits:
					lines = map(merge_digits_to_numbers, lines)
				i = 0
				for line in lines:
					w.write(str(int(math.floor(i / args['num_translations']))) + ' ||| ' + line + ' ||| \n')
					i += 1
		os.remove(tmp_output)


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
						help="nmt configuration file (default: \'%(default)s\')")
	parser.add_argument('-t', '--framework_config', type=str, default='configs/tensorflow.config',
						help="tensorflow configuration file (default: \'%(default)s\')")
	parser.add_argument('-s', '--seed', type=int, help="random seed")
	parser.add_argument('-p', '--previous_model', type=str, help="previous model to use as baseline")
	parser.add_argument('-v', '--previous_vocabs', type=str, help="previous vocabularies to use as baseline (ignored)")
	parser.add_argument('-i', '--iteration_num', type=int, default=0, help="iteration number, used to distinguish first iteration from the rest")
	args = parser.parse_args()

	if (args.train and args.translate) or not (args.train or args.translate):
		parser.error('You should choose either --train or --translate (exactly one, not both)')

	main(vars(args))
