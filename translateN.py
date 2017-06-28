import sys
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
					target[i] = src[alignments[i]]
			out_filename.write(index+' ||| '+' '.join(target) + ' ||| \n')

def main(f,m,k):
	decode_command = 'python nematus/nematus/translate.py -m {} -i {} -o {} -a {} -p 5 --n-best -k {}'.format(m, f+'.corpus.ll', f+'.corpus.'+str(k)+'.tmp', f+'.'+str(k)+'.alignment',k)
	os.system(decode_command)
	with open(f+'.'+str(k)+'.alignment','r') as fin:
		with open(f+'.corpus.'+str(k)+'.out','w') as fout:
			copy_unknown_words(fin, fout)
	os.remove(f+'.corpus.'+str(k)+'.tmp')

if __name__ == "__main__":
	main(sys.argv[1],os.path.join(sys.argv[2],sys.argv[3]),int(sys.argv[4]))