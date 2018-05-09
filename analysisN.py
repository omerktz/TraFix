import os
import csv
import logging
from dateutil.parser import parse
from utils.colored_logger_with_timestamp import init_colorful_root_logger


def analyze_all_results(logic, keys, logs, outputs):
	return map(lambda k: logic(logs[k], outputs[k]), keys)


def analyze_all_results_average(logic, keys, logs, outputs, missing_is_zero):
	results = map(lambda k: logic(logs[k], outputs[k]), keys)
	inner_keys = set(reduce(lambda x, y: x + y, map(lambda r: r.keys(), results)))
	for i in range(max(inner_keys)):
		if i not in inner_keys:
			inner_keys.add(i)
	inner_keys = sorted(inner_keys)
	for result in results:
		for ik in inner_keys:
			if ik not in result.keys():
				if missing_is_zero:
					result[ik] = 0
				else:
					result[ik] = result[ik - 1]
	final_results = {}
	for ik in inner_keys:
		data = map(lambda r: r[ik], results)
		final_results[ik] = (sum(data) / float(len(data)), min(data), max(data))
	return final_results


def get_datasets_size(folder, prefix, suffix, n):
	result = {}
	for i in range(n+1):
		if os.path.exists(os.path.join(folder, 'datasets', '{0}{1}{2}'.format(prefix, i, suffix))):
			with open(os.path.join(folder, 'datasets', '{0}{1}{2}'.format(prefix, i, suffix)), 'r') as f:
				result[i] = len(filter(lambda l: len(l.strip()) > 0, f.readlines()))
	return result


def get_timings(log, marker, n, until=1):
	def get_time(line):
		index = line.find(' ')
		return parse(line[index - 10: index + 8])

	result = {}
	with open(log, 'r') as f:
		lines = filter(lambda y: len(y) > 0, map(lambda x: x.strip(), f.readlines()))
		for i in range(len(lines)):
			if i < len(lines) - 1:
				if marker in lines[i]:
					line = lines[i][:]
					line = line[line.find(' (iteration ') + 12:]
					line = line[:line.find(')')]
					if int(line) < n:
						result[int(line)] = (get_time(lines[i + until]) - get_time(lines[i])).total_seconds()
	return result


def remaining_test_size(keys, logs, outputs, out, n):
	def logic(log, output):
		return get_datasets_size(output, 'test', '.corpus.hl', n)

	data = analyze_all_results_average(logic, keys, logs, outputs, missing_is_zero=False)
	out.writerow(['Remaining test size'])
	out.writerow(['', 'Average:'])
	out.writerow(['', '', 'Raw:'] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', '', 'Ratio:'] + map(lambda k: data[k][0] / float(data[0][0]), sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow(['', '', 'Raw:'] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', '', 'Ratio:'] + map(lambda k: data[k][1] / float(data[0][1]), sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow(['', '', 'Raw:'] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow(['', '', 'Ratio:'] + map(lambda k: data[k][2] / float(data[0][2]), sorted(data.keys())))
	out.writerow([])
	out.writerow(['Successful test samples'])
	out.writerow(['', 'Average:'])
	out.writerow(['', '', 'Raw:'] + map(lambda k: data[0][0] - data[k][0], sorted(data.keys())))
	out.writerow(['', '', 'Ratio:'] + map(lambda k: (data[0][0] - data[k][0]) / float(data[0][0]), sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow(['', '', 'Raw:'] + map(lambda k: data[0][2] - data[k][2], sorted(data.keys())))
	out.writerow(['', '', 'Ratio:'] + map(lambda k: (data[0][2] - data[k][2]) / float(data[0][2]), sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow(['', '', 'Raw:'] + map(lambda k: data[0][1] - data[k][1], sorted(data.keys())))
	out.writerow(['', '', 'Ratio:'] + map(lambda k: (data[0][1] - data[k][1]) / float(data[0][1]), sorted(data.keys())))
	out.writerow([])


def train_size(keys, logs, outputs, out, n):
	def logic(log, output):
		return get_datasets_size(output, 'train', '.corpus.hl', n)

	data = analyze_all_results_average(logic, keys, logs, outputs, missing_is_zero=False)
	out.writerow(['Train set size'])
	out.writerow(['', 'Average:'])
	out.writerow([''] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow([''] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow([''] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow([])


def train_time(keys, logs, outputs, out, n):
	def logic(log, output):
		return get_timings(log, 'Training model ', n)

	data = analyze_all_results_average(logic, keys, logs, outputs, missing_is_zero=True)
	out.writerow(['Training time (seconds)'])
	out.writerow(['', 'Average:'])
	out.writerow([''] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow([''] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow([''] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow([])


def translate_time(keys, logs, outputs, out, n):
	def logic(log, output):
		return get_timings(log, 'Translating dataset ', n)

	data = analyze_all_results_average(logic, keys, logs, outputs, missing_is_zero=True)
	out.writerow(['Translation time (seconds)'])
	out.writerow(['', 'Average:'])
	out.writerow([''] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow([''] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow([''] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow([])


def evaluate_time(keys, logs, outputs, out, n):
	def logic(log, output):
		return get_timings(log, 'Evaluating latest results ', n)

	data = analyze_all_results_average(logic, keys, logs, outputs, missing_is_zero=True)
	out.writerow(['Evaluation time (seconds)'])
	out.writerow(['', 'Average:'])
	out.writerow([''] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow([''] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow([''] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow([])


def iteration_time(keys, logs, outputs, out, n):
	def logic(log, output):
		return get_timings(log, 'Training model ', n, until=4)

	data = analyze_all_results_average(logic, keys, logs, outputs, missing_is_zero=True)
	out.writerow(['Iteration time (seconds)'])
	out.writerow(['', 'Average:'])
	out.writerow([''] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow([''] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow([''] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow([])


def train_epochs(keys, logs, outputs, out, n):
	def logic_last(log, output):
		result = {}
		for i in range(n):
			with open(os.path.join(output, 'outputs', '{0}{1}'.format('train', i)), 'r') as f:
				lines = filter(lambda l: len(l.strip()) > 0, f.readlines())
				if 'last epoch is' in lines[-3]:
					last_epoch = int(lines[-3][len('last epoch is '):])
					result[i] = last_epoch
		return result
	def logic_best(log, output):
		result = {}
		for i in range(n):
			with open(os.path.join(output, 'outputs', '{0}{1}'.format('train', i)), 'r') as f:
				lines = filter(lambda l: len(l.strip()) > 0, f.readlines())
				if 'best epoch is' in lines[-2]:
					best_epoch = int(lines[-2][len('best epoch is '):])
					result[i] = best_epoch
		return result

	data = analyze_all_results_average(logic_last, keys, logs, outputs, missing_is_zero=True)
	out.writerow(['Last training epoch'])
	out.writerow(['', 'Average:'])
	out.writerow([''] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow([''] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow([''] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow([])
	data = analyze_all_results_average(logic_best, keys, logs, outputs, missing_is_zero=True)
	out.writerow(['Best training epoch'])
	out.writerow(['', 'Average:'])
	out.writerow([''] + map(lambda k: data[k][0], sorted(data.keys())))
	out.writerow(['', 'Min:'])
	out.writerow([''] + map(lambda k: data[k][1], sorted(data.keys())))
	out.writerow(['', 'Max:'])
	out.writerow([''] + map(lambda k: data[k][2], sorted(data.keys())))
	out.writerow([])


analysis_funcs = [remaining_test_size, train_size, train_time, translate_time, evaluate_time,
				  iteration_time, train_epochs]


def analyze_results(input, output, n, funcs=analysis_funcs):
	logs = {}
	outputs = {}
	for f in os.listdir(input):
		path = os.path.join(input, f)
		if os.path.isdir(path) and f.startswith('output'):
			outputs[int(f[6:])] = path
		if os.path.isfile(path) and f.startswith('log'):
			logs[int(f[3:])] = path
	keys = set()
	for i in logs.keys():
		if i not in outputs.keys():
			logging.info('Ignoring log{0}, no matching output folder'.format(i))
		else:
			keys.add(i)
	for i in outputs.keys():
		if i not in logs.keys():
			logging.info('Ignoring output{0}, no matching log file'.format(i))
		else:
			keys.add(i)
	with open(output, 'w') as fout:
		csvout = csv.writer(fout)
		csvout.writerow(['Number of experiments:', len(keys)])
		csvout.writerow([])
		csvout.writerow(['Number of Iterations:', n])
		csvout.writerow([])
		for f in funcs:
			f(sorted(keys), logs, outputs, csvout, n)


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Analyze results of Active Learner")
	parser.add_argument('input', type=str, help="Folder used as input")
	parser.add_argument('output', type=str, help="Output file name")
	parser.add_argument('n', type=int, help="Number of iterations")
	parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
	parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')

	args = parser.parse_args()
	init_colorful_root_logger(logging.getLogger(''), vars(args))

	analyze_results(input=args.input, output=args.output, n=args.n)
