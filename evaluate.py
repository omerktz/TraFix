import sys
import os
import subprocess

varCount = 10
def compareProgs(c,out):
	with open('cbmc.c','w') as fcbmc:
		c = filter(lambda x:len(x)>0,c.strip().split(' '))
		for i in range(len(c)):
			if c[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
				c[i] = c[i]+'_0'
		c = ' '.join(c)
		out = filter(lambda x:len(x)>0,out.strip().split(' '))
		for i in range(len(out)):
			if out[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
				out[i] = out[i]+'_1'
		out = ' '.join(out)
		fcbmc.write('void main() {\n')
		fcbmc.write('\tint Y_0,Y_1')
		for i in range(varCount):
			fcbmc.write(',X'+str(i)+'_0,X'+str(i)+'_1')
		fcbmc.write(';\n')
		for i in range(varCount):
			fcbmc.write('\t__CPROVER_assume(X'+str(i)+'_0==X'+str(i)+'_1);\n')
		fcbmc.write('\t'+c+'\n')
		fcbmc.write('\t'+out+'\n')
		fcbmc.write('\t__CPROVER_assert(Y_0==Y_1,"computations not equivalent");\n')
		fcbmc.write('}')
	with open(os.devnull,'w') as fnull:
		ret = subprocess.call(['cbmc','cbmc.c'], stdout=fnull, stderr=subprocess.STDOUT)
	os.remove('cbmc.c')
	return ret

def evaluate(fc,fll,fout,fi=None,fs=None,ff=None,fp=None):
	nidentical = 0
	nsuccess = 0
	nfail = 0
	nparse = 0
	for c in fc.readlines():
		c = c.strip()
		ll = fll.readline().strip()
		out = fout.readline().strip()
		if c == out:
			if fi:
				fi.write(c+'\t'+ll+'\t'+out+'\n')
			nidentical += 1
			
		else:
			res = compareProgs(c,out)
			if res == 0:
				if fs:
					fs.write(c+'\t'+ll+'\t'+out+'\n')
				nsuccess += 1
			else:
				if res == 6:
					if fp:
						fp.write(c + '\t' + ll + '\t' + out + '\n')
					nparse += 1
				else:
					if ff:
						ff.write(c + '\t' + ll + '\t' + out + '\n')
					nfail += 1
	return (nidentical,nsuccess,nparse,nfail)

def main(f):
	with open(f+'.identical.out','w') as fidentical:
		with open(f+'.success.out','w') as fsuccess:
			with open(f+'.fail.out', 'w') as ffail:
				with open(f+'.parse.out', 'w') as fparse:
					fidentical.write('c\tll\tout\n')
					fsuccess.write('c\tll\tout\n')
					ffail.write('c\tll\tout\n')
					fparse.write('c\tll\tout\n')
					with open(f+'.corpus.c','r') as fc:
						with open(f+'.corpus.ll', 'r') as fll:
							with open(f+'.corpus.out', 'r') as fout:
								(nidentical,nsuccess,nparse,nfail) = evaluate(fc,fll,fout,fidentical,fsuccess,ffail,fparse)
	print str(nidentical)+' statements translated identically'
	print str(nsuccess)+' statements translated equivalently'
	print str(nparse)+' translated statements failed to parse'
	print str(nfail)+' translated statements are not equivalent'

if __name__ == "__main__":
	main(sys.argv[1])