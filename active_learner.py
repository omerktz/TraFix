import os
from subprocess import Popen, check_output
import random
import csv
import logging
from utils.colored_logger_with_timestamp import init_colorful_root_logger
import generate_vocabularies as vocabs_utils


###
# given a test dataset, active learner iteratively:
# 1) increase train set size
# 2) refereshes validation size
# 3) retrains model
# 4) translates test dataset
# until enough entries from the test dataset have been successfully translated
###
class ActiveLearner:
	def __init__(self, input, output_dir, compiler, experiment=False, codenator_config='configs/codenator.config',
				 dynmt_config='configs/dynmt.config', patience=10, num_translations=5, success_percentage=0.99,
				 validation_size=1000, train_size_initial=10000, train_size_increment=10000, initial_model=None):
		# store parameters
		self.input = input
		self.output_dir = output_dir
		self.compiler = compiler
		self.codenator_config = codenator_config
		self.dynmt_config = dynmt_config
		self.patience = patience
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
		os.system(
			'cp {0} {1}'.format(self.dynmt_config, os.path.join(self.output_dir, os.path.basename(self.dynmt_config))))
		# update config paths
		self.codenator_config = os.path.join(self.output_dir, os.path.basename(self.codenator_config))
		self.dynmt_config = os.path.join(self.output_dir, os.path.basename(self.dynmt_config))
		# create work directories
		os.makedirs(self.models_path)
		os.makedirs(self.outputs_path)
		os.makedirs(self.datasets_path)
		# copy initial model
		if self.initial_model:
			if os.path.exists(self.initial_model):
				os.system('cp {0} {1}'.format(self.initial_model, os.path.join(self.output_dir, 'initial_model')))
				os.system('cp {0} {1}'.format(self.initial_model+'.vocabs.in',
											  os.path.join(self.output_dir, 'initial_model.vocabs.in')))
				os.system('cp {0} {1}'.format(self.initial_model+'.vocabs.out',
											  os.path.join(self.output_dir, 'initial_model.vocabs.out')))
				self.initial_model = os.path.join(self.output_dir, 'initial_model')
			else:
				logging.info('Initial model does not exist, starting from empty model')
				self.initial_model = None
		# create initial datasets
		logging.info('Generating initial datasets')
		basename = os.path.basename(self.input)
		if not experiment:
			os.system('cp {0} {1}'.format(self.input + '.*', self.output_dir))
		else:
			os.system('python {0} {4} -n {1} -c {2} -o {3} -v'.format(self.codenator, 2000, self.codenator_config,
																	  os.path.join(self.output_dir, basename),
																	  self.compiler))
		for ext in ['ll', 'hl']:
			os.system('cp {0} {1}'.format(os.path.join(self.output_dir, basename + '.corpus.' + ext),
										  os.path.join(self.datasets_path, 'test0.corpus.' + ext)))
		self.initial_test_size = int(
			check_output('cat {0} | wc -l'.format(os.path.join(self.datasets_path, 'test0.corpus.ll')),
						 shell=True).strip())
		logging.info('Initial test dataset size is {0}'.format(self.initial_test_size))
		self.remaining = self.initial_test_size

		os.system(
			'python {0} {5} -o {1} -c {2} -n {3} -e {4} -v'.format(self.codenator,
															os.path.join(self.datasets_path, 'train0'),
															self.codenator_config,
															0 if self.initial_model else self.train_size_initial,
															os.path.join(self.datasets_path, 'test0'),
																   self.compiler))
		os.system(
			'python {0} {5} -o {1} -c {2} -n {3} -e {4} -v'.format(self.codenator,
															   os.path.join(self.datasets_path, 'validate0'),
															   self.codenator_config,
															   0 if self.initial_model else self.validation_size,
															   os.path.join(self.datasets_path, 'test0'),
																   self.compiler))
		vocabs_utils.generate_vocabs([os.path.join(self.datasets_path, 'test0'),
									  os.path.join(self.datasets_path, 'train0'),
									  os.path.join(self.datasets_path, 'validate0')],
									 os.path.join(self.datasets_path, 'vocabs0'))


	# train model until no more progress is made on validation set and translate test set
	def train_and_translate(self, i, previous=None):
		# train
		if (i == 0) and self.initial_model:
			logging.info('Using initial model (iteration {0})'.format(i))
			os.system('cp {0} {1}'.format(self.initial_model,
										  os.path.join(self.models_path, 'model0.ll-po.dynmt_bestmodel.txt')))
			os.system('cp {0} {1}'.format(self.initial_model+'.vocabs.in',
										  os.path.join(self.models_path, 'model0.ll-po.dynmt.vocabs.in')))
			os.system('cp {0} {1}'.format(self.initial_model+'.vocabs.out',
										  os.path.join(self.models_path, 'model0.ll-po.dynmt.vocabs.out')))
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
																				   os.path.join(self.datasets_path,
																								'vocabs%d' % i),
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
			Popen('python {0} {1} {2} {3} {4} -m {5} -c {6} --translate -n {7}'.format(self.api_dynmt,
																					   os.path.join(self.datasets_path,
																									'train%d' % i),
																					   os.path.join(self.datasets_path,
																									'validate%d' % i),
																					   os.path.join(self.datasets_path,
																									'test%d' % i),
																					   os.path.join(self.datasets_path,
																									'vocabs%d' % i),
																					   os.path.join(self.models_path,
																									'model%d' % i),
																					   self.dynmt_config,
																					   self.num_translations).split(
				' '), stdout=f, stderr=f).wait()

	# generate new datasets and combine with previous set of datasets
	def update_datasets(self, i):

		logging.info('Updating training dataset (iteration {0})'.format(i))
		os.system('python {0} {6} -o {1} -c {2} -n {3} -e {4} -a {5} -v'.format(self.codenator,
																  os.path.join(self.datasets_path, 'train%d' % i),
																  self.codenator_config, self.train_size_increment,
																  os.path.join(self.datasets_path, 'test0'),
																  os.path.join(self.datasets_path, 'train%d' % (i-1)),
																  self.compiler))
		for ext in ['ll', 'hl']:
			os.system(
				'cat {0}.corpus.{2} >> {1}.corpus.{2}'.format(os.path.join(self.datasets_path, 'failed%d' % (i - 1)),
															  os.path.join(self.datasets_path, 'train%d' % i), ext))

		logging.info('Updating validation dataset (iteration {0})'.format(i))
		os.system(
			'python {0} {6} -o {1} -c {2} -n {3} -e {4} -a {5} -v'.format(self.codenator,
															os.path.join(self.datasets_path, 'validate%d' % i),
															self.codenator_config, self.validation_size,
															os.path.join(self.datasets_path, 'test0'),
															os.path.join(self.datasets_path, 'validate%d' % (i - 1)),
															self.compiler))
		vocabs_utils.generate_vocabs([os.path.join(self.datasets_path, 'test0'),
									  os.path.join(self.datasets_path, 'train%d' % i),
									  os.path.join(self.datasets_path, 'validate%d' % i)],
									 os.path.join(self.datasets_path, 'vocabs%d' % i))


	# return True if successfully translated *enough* entries
	def results_sufficient(self, i):

		# update test dataset keeping only unsolved entries
		def update_testset(i):
			num_remaining = 0
			with open(os.path.join(self.datasets_path, 'test%d.corpus.hl' % (i + 1)), 'w') as fhl:
				with open(os.path.join(self.datasets_path, 'test%d.corpus.ll' % (i + 1)), 'w') as fll:
					with open(
							os.path.join(self.datasets_path, 'test%d.fail.%d.csv' % (i, self.num_translations)),
							'r') as fin:
						for l in list(csv.reader(fin))[1:]:
							fhl.write(l[1] + '\n')
							fll.write(l[3] + '\n')
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
			Popen('python {0} {1} {2} {3} -d {4} -v'.format(self.evaluate,
													 os.path.join(self.datasets_path, 'test%d' % i),
													 self.num_translations, self.compiler,
													 os.path.join(self.datasets_path, 'failed%d' % i)).split(' '),
				  stdout=f,
				  stderr=f).wait()
		self.remaining = update_testset(i)
		logging.info('{0} entries left to translate'.format(self.remaining))
		return (self.remaining <= (self.initial_test_size * (1 - self.success_percentage)))

	def run(self, cleanup=False):
		import time
		with open(os.path.join(self.output_dir, 'successes.csv'), 'w') as fout:
			csv.writer(fout).writerow(['hl', 'll', 'out'])
		i = 0
		logging.info('Starting ActiveLearner')
		start_time = time.time()
		self.train_and_translate(i)
		remaining_update_counter = 0
		remaining_last = self.remaining
		while not self.results_sufficient(i):
			if self.remaining != remaining_last:
				remaining_last = self.remaining
				remaining_update_counter = 0
			else:
				remaining_update_counter += 1
				if remaining_update_counter >= self.patience:
					break
			i += 1
			self.update_datasets(i)
			self.train_and_translate(i, previous=i - 1)
		end_time = time.time()
		if remaining_update_counter >= self.patience:
			logging.info('ActiveLearner stopped, no progress made for last {0} iterations (duration: {1} seconds)'.
						 format(self.patience, end_time - start_time))
		else:
			logging.info('ActiveLearner finished (duration: {0} seconds)'.format(end_time - start_time))
		num_failures = 0
		with open(os.path.join(self.output_dir, 'failures.csv'), 'w') as fout:
			csvout = csv.writer(fout)
			csvout.writerow(['hl', 'll'])
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
		os.system('cp {0} {1}'.format(os.path.join(self.models_path, 'model{0}.ll-po.dynmt.vocabs.in'.format(i)),
									  os.path.join(self.output_dir, 'final_model.vocabs.in')))
		os.system('cp {0} {1}'.format(os.path.join(self.models_path, 'model{0}.ll-po.dynmt.vocabs.out'.format(i)),
									  os.path.join(self.output_dir, 'final_model.vocabs.out')))
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
	parser.add_argument('compiler', type=str, help="file containing implementation of 'compiler' function")
	parser.add_argument('-e', '--experiment', action='store_const', const=True,
						help='Generate own test input and run as experiment')
	parser.add_argument('-c', '--codenator_config', type=str, default='configs/codenator.config',
						help="Codenator configuration file (default: \'%(default)s\')")
	parser.add_argument('-d', '--dynmt-config', type=str, default='configs/dynmt.config',
						help="Dynmt configuration file (default: \'%(default)s\')")
	parser.add_argument('-k', '--num-translations', type=int, default=5,
						help="Number of translations per entry (default: %(default)s)")
	parser.add_argument('-p', '--percentage', type=float, default=0.99,
						help="Required percentage (between 0 and 1) of inputs successfully translated before termination (default: %(default)s)", )
	parser.add_argument('-t', '--validation-size', type=int, default=1000,
						help="Number of samples in validation dataset (default: %(default)s)")
	parser.add_argument('-i', '--train-size-initial', type=int, default=10000,
						help="Initial number of samples in training dataset (default: %(default)s)")
	parser.add_argument('-n', '--train-size-increment', type=int, default=10000,
						help="Number of samples to add to training dataset at each round (default: %(default)s)")
	parser.add_argument('-m', '--initial-model', type=str,
						help="trained model to to use as basis for current active learner")
	parser.add_argument('-w', '--patience', type=int, default=10,
						help="Number of iterations without progress before early-stop (default: %(default)s)")
	parser.add_argument('--cleanup', action='store_const', const=True, help='Cleanup any remaining temporary files')
	parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
	parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')
	args = parser.parse_args()
	init_colorful_root_logger(logging.getLogger(''), vars(args))

	ActiveLearner(input=args.input, output_dir=args.output, compiler=args.compiler, experiment=args.experiment,
				  codenator_config=args.codenator_config, dynmt_config=args.dynmt_config, patience=args.patience,
				  num_translations=args.num_translations, success_percentage=args.percentage,
				  validation_size=args.validation_size, train_size_initial=args.train_size_initial,
				  train_size_increment=args.train_size_increment, initial_model=args.initial_model).\
		run(cleanup=args.cleanup)
