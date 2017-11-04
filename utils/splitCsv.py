import os
def filter(c,ll,out):
	if os.path.exists('tmp.corpus.1.out'):
		with open('tmp.corpus.1.out','r') as f:
			i = len([l for l in f.readlines()])
	else:
		i = 0
	print i
	with open('tmp.corpus.c','a') as fc:
		with open('tmp.corpus.ll','a') as fll:
			with open('tmp.corpus.1.out','a') as fout:
				fc.write(c.strip()+'\n')
				fll.write(ll.strip()+'\n')
				fout.write(str(i)+' ||| '+out[0].strip()+' ||| \n')
