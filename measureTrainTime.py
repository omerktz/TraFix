from multiprocessing import Pool
from subprocess import Popen
from itertools import product
import time
from evaluate import evaluate
import sys


def run((nums, length)):
	with open('outputs/dynmt_train_{0}_{1}.out'.format(nums, length),'w') as f:
		train_start = time.time()
		Popen(
			'time python api_dynmt.py datasets/train_{0}_{1} datasets/validate_{0}_{1} datasets/test_{0}_{1} -m models/model_{0}_{1} -po -c configs/dynmt.config --train --cleanup'.format(
				nums, length).split(' '), stdout=f, stderr=f).wait()
		train_end = time.time()
	with open('outputs/dynmt_train_{0}_{1}.out'.format(nums, length), 'r') as f:
		lines = f.readlines()
	epochs = int(filter(lambda x: x.startswith('last epoch is '), lines)[0].strip()[14:])
	dev_blue_line = filter(lambda x: x.startswith('epoch: ' + str(epochs)), lines)[0]
	dev_blue_line = dev_blue_line[dev_blue_line.index('best dev bleu ') + 14:]
	dev_bleu = float(dev_blue_line[:dev_blue_line.index(' ')])
	dev_blue_line = dev_blue_line[dev_blue_line.index('(epoch ') + 7:]
	best_epoch = int(dev_blue_line[:dev_blue_line.index(')')])
	with open('outputs/dynmt_translate_{0}_{1}.out'.format(nums, length), 'w') as f:
		translate_start = time.time()
		Popen(
			'time python api_dynmt.py datasets/train_{0}_{1} datasets/validate_{0}_{1} datasets/test_{0}_{1} -m models/model_{0}_{1} -po -c configs/dynmt.config --translate --cleanup'.format(
				nums, length).split(' '), stdout=f, stderr=f).wait()
		translate_end = time.time()
	with open('outputs/dynmt_translate_{0}_{1}.out'.format(nums, length), 'r') as f:
		lines = f.readlines()
	test_blue = float(filter(lambda x: x.startswith('test bleu: '), lines)[0].strip()[11:-1])
	with open('datasets/test_{0}_{1}.corpus.c'.format(nums, length), 'r') as fc:
		with open('datasets/test_{0}_{1}.corpus.ll'.format(nums, length), 'r') as fll:
			with open('datasets/test_{0}_{1}.corpus.5.out'.format(nums, length), 'r') as fout:
				(nidentical, nsuccess, nparse, nfail, ntimeout) = evaluate(5, fc, fll, fout, True, True)
	return (nums, length, train_end - train_start, epochs, best_epoch, dev_bleu,
			translate_end - translate_start, test_blue, nidentical + nsuccess, nparse, nfail + ntimeout)


print 'Using %s processes' % sys.argv[1]
pool = Pool(processes=int(sys.argv[1]))
results = pool.map(run, product(range(100, 0, -10), range(10000, 0, -1000)))
pool.close()
pool.join()
import csv

with open('results.csv', 'w') as f:
	csvf = csv.writer(f)
	csvf.writerow(
		['MaxNum', 'TrainDatsetSize', 'TrainTime', 'TotalEpochs', 'BestEpoch', 'BestDevBleu', 'TranslationTime',
		 'TestBleu', 'Successes', 'UnParsable', 'Failures'])
	for r in results:
		csvf.writerow([r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10]])
