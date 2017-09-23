import os
import numpy

def copy_unknown_words(filename, out_filename, unk_token = 'UNK'):
	for line in filename:
		items = line.split(' ||| ')
		if len(items) > 1:
			src = items[3].split()
			target = items[1].split()
			index = items[0].strip()
			alignments = []
		elif line.strip():
			alignment = map(float,line.split())
			hard_alignment = numpy.argmax(alignment, axis=0)
			alignments.append(hard_alignment)
		elif line == '\n':
			#print alignments
			for i, word in enumerate(target):
				if word == unk_token:
					j = alignments[i]
					if j < len(src):
						target[i] = src[alignments[i]]
					else:
						if j == len(src):
							target[i] = '$'
			out_filename.write(index+' ||| '+' '.join(target) + ' ||| \n')

def main(f,m,k,ext):
	decode_command = 'python nematus/nematus/translate.py -m {} -i {} -o {} -a {} -p 5 --n-best -k {}'.format(m, f+'.corpus.'+ext, f+'.corpus.'+str(k)+'.tmp', f+'.'+str(k)+'.alignment',k)
	os.system(decode_command)
	with open(f+'.'+str(k)+'.alignment','r') as fin:
		with open(f+'.corpus.'+str(k)+'.out','w') as fout:
			copy_unknown_words(fin, fout)
	os.remove(f+'.corpus.'+str(k)+'.tmp')

if __name__ == "__main__":
	import argparse
	parser = argparse.ArgumentParser(description="Transalte dataset")
	parser.add_argument('dataset', type=str, help="dataset to translate")
	parser.add_argument('model_directory', type=str, help="directory in which to save trained model")
	parser.add_argument('model_name', type=str, help="name of trained model")
	parser.add_argument('num_translations', type=int, help="number of top translations to output for each input")
	parser.add_argument('-ll', '--llvm', dest='l', help="translate LLVM code", action='count')
	parser.add_argument('-pt', '--parse-tree', dest='p', help="translate parse tree code", action='count')
	args = parser.parse_args()

	if (not (args.l or args.p)) or (args.l and args.p):
		parser.error('You need to exactly one input option (-ll or -pt, not both)')

	main(args.dataset,os.path.join(args.model_directory,args.model_name),args.num_translations,'ll' if args.l else 'pt')