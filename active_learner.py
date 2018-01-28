import os
from subprocess import Popen, check_output
import random
import csv
import logging
from utils.colored_logger_with_timestamp import init_colorful_root_logger


###
# given a test dataset, active learner iteratively:
# 1) increase train set size
# 2) refereshes validation size
# 3) retrains model
# 4) translates test dataset
# until enough entries from the test dataset have been successfully translated
###
class ActiveLearner:
	def __init__(self, input, output_dir, experiment=False, codenator_config='configs/codenator.config',
				 codenator_setting='configs/codenator_setting.config', dynmt_config='configs/dynmt.config',
				 num_translations=5, success_percentage=0.99, validation_size=1000, train_size_initial=1000,
				 train_size_increment=1000, initial_model=None):
		# store parameters
		self.input = input
		self.output_dir = output_dir
		self.codenator_config = codenator_config
		self.codenator_setting = codenator_setting
		self.dynmt_config = dynmt_config
		self.num_translations = num_translations
		self.success_percentage = success_percentage
		self.validation_size = validation_size
		self.train_size_initial = train_size_initial
		self.train_size_increment = train_size_increment
		self.initial_model = initial_model
		# set external scripts paths
		self.codenator = 'codenator.py'
		self.api_dynmt = 'api_dynmt.py'
		self.evaluate = 'evaluate.py'
		# set work paths
		self.datasets_path = os.path.join(self.output_dir, 'datasets')
		self.models_path = os.path.join(self.output_dir, 'models')
		self.outputs_path = os.path.join(self.output_dir, 'outputs')
		self.vocab_path = os.path.join(self.output_dir, 'vocab')
		# initialize
		self.initialize_datasets(experiment)

	def initialize_datasets(self, experiment):
		logging.info('Initializing ActiveLearner')
		# clear output dir
		if os.path.exists(self.output_dir):
			if os.path.isdir(self.output_dir):
				import shutil
				shutil.rmtree(self.output_dir)
			else:
				os.remove(self.output_dir)
		os.makedirs(self.output_dir)
		os.system('cp {0} {1}'.format(self.codenator_config,
									  os.path.join(self.output_dir, os.path.basename(self.codenator_config))))
		os.system('cp {0} {1}'.format(self.codenator_setting,
									  os.path.join(self.output_dir, os.path.basename(self.codenator_setting))))
		os.system(
			'cp {0} {1}'.format(self.dynmt_config, os.path.join(self.output_dir, os.path.basename(self.dynmt_config))))
		# update config paths
		self.codenator_config = os.path.join(self.output_dir, os.path.basename(self.codenator_config))
		self.codenator_setting = os.path.join(self.output_dir, os.path.basename(self.codenator_setting))
		self.dynmt_config = os.path.join(self.output_dir, os.path.basename(self.dynmt_config))
		# create work directories
		os.makedirs(self.models_path)
		os.makedirs(self.outputs_path)
		os.makedirs(self.datasets_path)
		# copy initial model
		if self.initial_model:
			if os.path.exists(self.initial_model):
				os.system('cp {0} {1}'.format(self.initial_model, os.path.join(self.output_dir, 'initial_model')))
				self.initial_model = os.path.join(self.output_dir, 'initial_model')
			else:
				logging.info('Initial model does not exist, starting from empty model')
				self.initial_model = None
		# generate vocabularies
		logging.info('Generating vocabularies')
		os.system(
			'python {0} --vocabs -o {1} -c {2} -s {3}'.format(self.codenator, self.vocab_path, self.codenator_config,
															  self.codenator_setting))
		# create initial datasets
		logging.info('Generating initial datasets')
		basename = os.path.basename(self.input)
		if not experiment:
			os.system('cp {0} {1}'.format(self.input + '.*', self.output_dir))
		else:
			os.system('python {0} -n {1} -c {2} -o {3} -s {4}'.format(self.codenator, 1000, self.codenator_config,
																	  os.path.join(self.output_dir, basename),
																	  self.codenator_setting))
		for ext in ['ll', 'c', 'po']:
			os.system('cp {0} {1}'.format(os.path.join(self.output_dir, basename + '.corpus.' + ext),
										  os.path.join(self.datasets_path, 'test0.corpus.' + ext)))
		os.system('cp {0} {1}'.format(os.path.join(self.output_dir, basename + '.constants'),
									  os.path.join(self.datasets_path, 'test0.constants')))
		self.initial_test_size = int(
			check_output('cat {0} | wc -l'.format(os.path.join(self.datasets_path, 'test0.corpus.ll')),
						 shell=True).strip())
		logging.info('Initial test dataset size is {0}'.format(self.initial_test_size))
		os.system(
			'python {0} -o {1} -c {2} -n {3} -s {4}'.format(self.codenator,
															os.path.join(self.datasets_path, 'validate0'),
															self.codenator_config,
															0 if self.initial_model else self.validation_size,
															self.codenator_setting))
		os.system('rm {0}.stats.csv'.format(os.path.join(self.datasets_path, 'validate0')))
		os.system(
			'python {0} -o {1} -c {2} -n {3} -s {4}'.format(self.codenator,
															os.path.join(self.datasets_path, 'train0'),
															self.codenator_config,
															0 if self.initial_model else self.train_size_initial,
															self.codenator_setting))
		os.system('rm {0}.stats.csv'.format(os.path.join(self.datasets_path, 'train0')))

	# train model until no more progress is made on validation set and translate test set
	def train_and_translate(self, i, previous=None):
		# train
		if (i == 0) and self.initial_model:
			logging.info('Using initial model (iteration {0})'.format(i))
			os.system('cp {0} {1}'.format(self.initial_model,
										  os.path.join(self.models_path, 'model0.ll-po.dynmt_bestmodel.txt')))
		else:
			logging.info('Training model (iteration {0})'.format(i))
			with open(os.path.join(self.outputs_path, 'train%d' % i), 'w') as f:
				Popen('python {0} {1} {2} {3} {4} -m {5} -c {6} --train{7}'.format(self.api_dynmt,
																				   os.path.join(self.datasets_path,
																								'train%d' % i),
																				   os.path.join(self.datasets_path,
																								'validate%d' % i),
																				   os.path.join(self.datasets_path,
																								'test%d' % i),
																				   self.vocab_path,
																				   os.path.join(self.models_path,
																								'model%d' % i),
																				   self.dynmt_config, (
																						   ' -p %s' % os.path.join(
																					   self.models_path,
																					   'model%d' % previous)) if (
							previous is not None) else '').split(' '), stdout=f, stderr=f).wait()
		# translate
		logging.info('Translating dataset (iteration {0})'.format(i))
		with open(os.path.join(self.outputs_path, 'translate%d' % i), 'w') as f:
			Popen('python {0} {1} {2} {3} {4} -m {5} -c {6} --translate -n {7}'.format(self.api_dynmt, os.path.join(
				self.datasets_path, 'train%d' % i), os.path.join(self.datasets_path, 'validate%d' % i), os.path.join(
				self.datasets_path, 'test%d' % i), self.vocab_path, os.path.join(self.models_path, 'model%d' % i),
																					   self.dynmt_config,
																					   self.num_translations).split(
				' '), stdout=f, stderr=f).wait()

	# generate new datasets and combine with previous set of datasets
	def update_datasets(self, i):

		# combine two dataset to a single dataset and shuffle it
		# if limit is not None, keep only the top <limit> entries
		def combine_dataset(new_dataset, old_dataset, limit=None):
			datasets = {}
			for ext in ['ll', 'c', 'po']:
				datasets[ext] = []
				with open('{0}.corpus.{1}'.format(new_dataset, ext), 'r') as f:
					datasets[ext] += map(lambda x: x.strip(), f.readlines())
				with open('{0}.corpus.{1}'.format(old_dataset, ext), 'r') as f:
					datasets[ext] += map(lambda x: x.strip(), f.readlines())
			indexes = range(len(datasets.values()[0]))
			random.shuffle(indexes)
			if limit:
				limit = min(limit, len(indexes))
				indexes = indexes[0: limit]
			for ext in ['ll', 'c', 'po']:
				with open('{0}.corpus.{1}'.format(new_dataset, ext), 'w') as f:
					f.write('\n'.join([datasets[ext][i] for i in indexes] + ['']))

		logging.info('Updating validation dataset (iteration {0})'.format(i))
		os.system(
			'python {0} -o {1} -c {2} -n {3} -s {4}'.format(self.codenator,
															os.path.join(self.datasets_path, 'validate%d' % i),
															self.codenator_config, self.validation_size,
															self.codenator_setting))
		os.system('rm {0}.stats.csv'.format(os.path.join(self.datasets_path, 'validate%d' % i)))
		combine_dataset(os.path.join(self.datasets_path, 'validate%d' % i),
						os.path.join(self.datasets_path, 'validate%d' % (i - 1)), limit=self.validation_size)
		logging.info('Updating training dataset (iteration {0})'.format(i))
		os.system('python {0} -o {1} -c {2} -n {3} -s {4}'.format(self.codenator,
																  os.path.join(self.datasets_path, 'train%d' % i),
																  self.codenator_config, self.train_size_increment,
																  self.codenator_setting))
		os.system('rm {0}.stats.csv'.format(os.path.join(self.datasets_path, 'train%d' % i)))
		for ext in ['ll', 'c', 'po']:
			os.system(
				'cat {0}.corpus.{2} >> {1}.corpus.{2}'.format(os.path.join(self.datasets_path, 'failed%d' % (i - 1)),
															  os.path.join(self.datasets_path, 'train%d' % i), ext))
		combine_dataset(os.path.join(self.datasets_path, 'train%d' % i),
						os.path.join(self.datasets_path, 'train%d' % (i - 1)))

	# return True if successfully translated *enough* entries
	def results_sufficient(self, i):

		# update test dataset keeping only unsolved entries
		def update_testset(i):
			num_remaining = 0
			with open(os.path.join(self.datasets_path, 'test%d.corpus.c' % (i + 1)), 'w') as fc:
				with open(os.path.join(self.datasets_path, 'test%d.corpus.po' % (i + 1)), 'w') as fpo:
					with open(os.path.join(self.datasets_path, 'test%d.corpus.ll' % (i + 1)), 'w') as fll:
						with open(os.path.join(self.datasets_path, 'test%d.constants' % (i + 1)), 'w') as fconstants:
							with open(
									os.path.join(self.datasets_path, 'test%d.fail.%d.csv' % (i, self.num_translations)),
									'r') as fin:
								for l in list(csv.reader(fin))[1:]:
									fc.write(l[1] + '\n')
									fpo.write(l[2] + '\n')
									fll.write(l[3] + '\n')
									fconstants.write(l[4] + '\n')
									num_remaining += 1
			with open(os.path.join(self.output_dir, 'successes.csv'), 'a') as fout:
				csvout = csv.writer(fout)
				with open(os.path.join(self.datasets_path, 'test%d.success.%d.csv' % (i, self.num_translations)),
						  'r') as fin:
					for l in list(csv.reader(fin))[1:]:
						csvout.writerow(l[1:])
			return num_remaining

		logging.info('Evaluating latest results (iteration {0})'.format(i))
		with open(os.path.join(self.outputs_path, 'evaluate%d' % i), 'w') as f:
			Popen('python {0} {1} {2} -d {3}'.format(self.evaluate,
													 os.path.join(self.datasets_path, 'test%d' % i),
													 self.num_translations,
													 os.path.join(self.datasets_path, 'failed%d' % i)).split(' '),
				  stdout=f,
				  stderr=f).wait()
		remaining = update_testset(i)
		logging.info('{0} entries left to translate'.format(remaining))
		return (remaining <= (self.initial_test_size * (1 - self.success_percentage)))

	def run(self, cleanup=False):
		import time
		with open(os.path.join(self.output_dir, 'successes.csv'), 'w') as fout:
			csv.writer(fout).writerow(['c', 'po', 'll', 'constants', 'out'])
		i = 0
		logging.info('Starting ActiveLearner')
		start_time = time.time()
		self.train_and_translate(i)
		while not self.results_sufficient(i):
			i += 1
			self.update_datasets(i)
			self.train_and_translate(i, previous=i - 1)
		end_time = time.time()
		logging.info('ActiveLearner finished (duration: {0} seconds)'.format(end_time - start_time))
		num_failures = 0
		with open(os.path.join(self.output_dir, 'failures.csv'), 'w') as fout:
			csvout = csv.writer(fout)
			csvout.writerow(['c', 'po', 'll', 'constants'])
			with open(os.path.join(self.datasets_path, 'test%d.fail.%d.csv' % (i, self.num_translations)),
					  'r') as fin:
				for l in list(csv.reader(fin))[1:]:
					csvout.writerow(l[1:])
					num_failures += 1
		logging.info(
			'Successfully translated {0} entries out of {1} ({2}%) in {3} iterations'.format(
				self.initial_test_size - num_failures,
				self.initial_test_size,
				100.0 * num_failures / float(
					self.initial_test_size), i + 1))
		os.system('cp {0} {1}'.format(os.path.join(self.models_path, 'model{0}.ll-po.dynmt_bestmodel.txt'.format(i)),
									  os.path.join(self.output_dir, 'final_model')))
		if cleanup:
			logging.info('Cleanup')
			for f in os.listdir('.'):
				if f.startswith('tmp') and (f.endswith('.c') or f.endswith('ll')):
					os.remove(f)


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Evaluate NMT as active learner")
	parser.add_argument('input', type=str, help="Input dataset for translation")
	parser.add_argument('output', type=str, help="Output directory")
	parser.add_argument('-e', '--experiment', action='store_const', const=True,
						help='Generate own test input and run as experiment')
	parser.add_argument('-c', '--codenator_config', type=str, default='configs/codenator.config',
						help="Codenator configuration file (default: \'%(default)s\')")
	parser.add_argument('-s', '--codenator_setting', type=str, default='configs/codenator_setting.config',
						help="Codenator settings file (default: \'%(default)s\')")
	parser.add_argument('-d', '--dynmt-config', type=str, default='configs/dynmt.config',
						help="Dynmt configuration file (default: \'%(default)s\')")
	parser.add_argument('-k', '--num-translations', type=int, default=5,
						help="Number of translations per entry (default: %(default)s)")
	parser.add_argument('-p', '--percentage', type=float, default=0.99,
						help="Required percentage (between 0 and 1) of inputs successfully translated before termination (default: %(default)s)", )
	parser.add_argument('-t', '--validation-size', type=int, default=1000,
						help="Number of samples in validation dataset (default: %(default)s)")
	parser.add_argument('-i', '--train-size-initial', type=int, default=5000,
						help="Initial number of samples in training dataset (default: %(default)s)")
	parser.add_argument('-n', '--train-size-increment', type=int, default=5000,
						help="Number of samples to add to training dataset at each round (default: %(default)s)")
	parser.add_argument('-m', '--initial-model', type=str,
						help="trained model to to use as basis for current active learner")
	parser.add_argument('--cleanup', action='store_const', const=True, help='Cleanup any remaining temporary files')
	parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
	parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')
	args = parser.parse_args()
	init_colorful_root_logger(logging.getLogger(''), vars(args))

	ActiveLearner(input=args.input, output_dir=args.output, experiment=args.experiment,
				  codenator_config=args.codenator_config, codenator_setting=args.codenator_setting,
				  dynmt_config=args.dynmt_config, num_translations=args.num_translations,
				  success_percentage=args.percentage, validation_size=args.validation_size,
				  train_size_initial=args.train_size_initial, train_size_increment=args.train_size_increment,
				  initial_model=args.initial_model).run(cleanup=args.cleanup)
