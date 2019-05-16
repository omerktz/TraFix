import logging
from utils.colored_logger_with_timestamp import init_colorful_root_logger
import postOrderUtil
import csv
import statistics


def parsePostOrcer(x):
	parse_result = postOrderUtil.parse(x)
	if not parse_result[0]:
		logging.error("Cannot parse post order code!")
	return parse_result[1].c()

def handle_file(f, preprocess=None):
	logging.info('Parsing file {}'.format(f))
	def split_line(l):
		return filter(lambda x: len(x) > 0, l.split(' '))
	with open(f, 'r') as f_in:
		lines = [l.strip() for l in f_in.readlines()]
	if preprocess is not None:
		lines = map(preprocess, lines)
	lines = map(split_line, lines)
	lens = map(lambda x: len(x), lines)
	return (len(lines), min(lens), max(lens), statistics.mean(lens), statistics.median(lens))


def get_stats(dataset):
	logging.info('Getting statistics for dataset {}'.format(dataset))
	ll_stats = handle_file(dataset+'.corpus.ll')
	hl_stats = handle_file(dataset+'.corpus.hl', parsePostOrcer)
	if hl_stats[0] != ll_stats[0]:
		logging.error('Dataset sizes do not match!')
	stats = ll_stats + hl_stats[1:]
	logging.info('Statistics:\tnumber of lines: {}'.format(ll_stats[0]))
	logging.info('min input length: {}\tmax input length: {}\taverage input length: {}\tmedian input length: {}'.format(*ll_stats[1:]))
	logging.info('min output length: {}\tmax output length: {}\taverage output length: {}\tmedian output length: {}'.format(*hl_stats[1:]))
	return stats


def handle_csv(f):
	logging.info('Parsing csv file {}'.format(f))
	def split_line(l):
		return filter(lambda x: len(x) > 0, l.split(' '))
	with open(f, 'r') as f_in:
		f_csv = csv.reader(f_in)
		lines = [l for l in f_csv][1:]
	lls = map(lambda l: split_line(l[1]), lines)
	hls = map(lambda l: split_line(l[-1]), lines)
	ll_lens = map(lambda x: len(x), lls)
	hl_lens = map(lambda x: len(x), hls)
	ll_stats = (len(ll_lens), min(ll_lens), max(ll_lens), statistics.mean(ll_lens), statistics.median(ll_lens))
	hl_stats = (len(hl_lens), min(hl_lens), max(hl_lens), statistics.mean(hl_lens), statistics.median(hl_lens))
	if hl_stats[0] != ll_stats[0]:
		logging.error('Dataset sizes do not match!')
	stats = ll_stats + hl_stats[1:]
	logging.info('Statistics:\tnumber of lines: {}'.format(ll_stats[0]))
	logging.info('min input length: {}\tmax input length: {}\taverage input length: {}\tmedian input length: {}'.format(*ll_stats[1:]))
	logging.info('min output length: {}\tmax output length: {}\taverage output length: {}\tmedian output length: {}'.format(*hl_stats[1:]))
	return stats


if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Get statistics of number of word in a dataset")
	parser.add_argument('--dataset', type=str, help="Input dataset")
	parser.add_argument('--csv', type=str, help="Input csv file")
	parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
	parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')
	args = parser.parse_args()
	init_colorful_root_logger(logging.getLogger(''), vars(args))

	if args.dataset is not None:
		get_stats(args.dataset)
	if args.csv is not None:
		handle_csv(args.csv)