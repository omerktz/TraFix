import re
import math

def tokenize_for_bleu(x):
	x = ' ' + re.sub(r'<skipped>', r'', x.strip()) + ' '
	x = re.sub(r'([\{-\~\[-\` -\&\(-\+\:-\@\/])', r' \1 ', x)
	x = re.sub(r'([^0-9])([\.,])', r'\1 \2 ', x)
	x = re.sub(r'([\.,])([^0-9])', r' \1 \2', x)
	x = re.sub(r'([0-9])(-)', r'\1 \2 ', x)
	x = re.sub(r'[ \t]+', r' ', x).strip().split(' ')
	return x

def compute_bleu_from_files(gold_outputs_path, output_file_path):
	with open(gold_outputs_path, 'r') as f_gold:
		with open(output_file_path, 'r') as f_output:
			return compute_bleu_from_lists(f_gold.readlines(), f_output.readlines())

def compute_bleu_from_lists(gold_lines, output_lines):
	gold_lines = map(lambda l: tokenize_for_bleu(l), gold_lines)
	output_lines = map(lambda l: tokenize_for_bleu(l), output_lines)
	s = 0
	total = dict(map(lambda i: (i, 0), range(1,5)))
	correct = dict(map(lambda i: (i, 0), range(1,5)))
	length_translation = 0
	length_reference = 0
	for word in output_lines:
		length_translation += len(word)
		if s < len(gold_lines):
			reference = gold_lines[s]
			length_reference += len(reference)
		else:
			reference = ''
			length_reference += 9999
		ref_ngrams = {}
		for n in range(1,5):
			for start in range(len(reference)+1-n):
				ngram = str(n)+' '+' '.join(reference[start:start+n])
				if ngram in ref_ngrams.keys():
					count = ref_ngrams[ngram] + 1
				else:
					count = 1
				ref_ngrams[ngram] = count
		for n in range(1, 5):
			word_ngrams = {}
			for start in range(len(word) + 1 - n):
				ngram = str(n)+' '+' '.join(word[start:start+n])
				if ngram in word_ngrams.keys():
					count = word_ngrams[ngram] + 1
				else:
					count = 1
				word_ngrams[ngram] = count
			for ngram in word_ngrams.keys():
				total[n] += word_ngrams[ngram]
				if ngram in ref_ngrams.keys():
					if ref_ngrams[ngram] >= word_ngrams[ngram]:
						correct[n] += word_ngrams[ngram]
					else:
						correct[n] += ref_ngrams[ngram]
		s += 1

	brevity_penalty = 1;
	bleu_map = {}
	for n in range(1, 5):
		if n in total.keys():
			bleu_map[n] = (correct[n]/float(total[n])) if (total[n] > 0) else 0
		else:
			bleu_map[n] = 0

	if length_reference == 0:
		return (0,0,0,0,0,0,0,0,0)

	if length_translation < length_reference:
		brevity_penalty = math.exp(1 - length_reference/float(length_translation))

	def log_wrapper(x):
		if x == 0:
			return -9999999999
		return math.log(x)

	bleu = brevity_penalty * math.exp((log_wrapper(bleu_map[1]) + log_wrapper(bleu_map[2]) + log_wrapper(bleu_map[3]) + log_wrapper(bleu_map[4])) / 4.0)
	return ("{:.2f}".format(100*bleu),
			"{:.1f}".format(100*bleu_map[1]),
			"{:.1f}".format(100*bleu_map[2]),
			"{:.1f}".format(100*bleu_map[3]),
			"{:.1f}".format(100*bleu_map[4]),
			"{:.3f}".format(brevity_penalty),
			"{:.3f}".format(length_translation/float(length_reference)),
			"{:d}".format(length_translation),
			"{:d}".format(length_reference))

if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Compute bleu score between two files")
	parser.add_argument('reference', type=str, help="File containing reference/gold translations")
	parser.add_argument('predictions', type=str, help="File containing predicted translations")
	args = parser.parse_args()

	result = compute_bleu_from_files(args.reference, args.predictions)
	print "BLEU = {}, {}/{}/{}/{} (BP={}, ratio={}, hyp_len={}, ref_len={})".format(*result)