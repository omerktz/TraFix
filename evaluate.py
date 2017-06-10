import sys
import os
import subprocess
import multiprocessing
import time

def runCbmc(timeout):
	with open(os.devnull,'w') as fnull:
		s = subprocess.Popen(['cbmc','cbmc'+str(os.getpid())+'.c'], stdout=fnull, stderr=subprocess.STDOUT)
		poll_period = 0
		s.poll()
		while s.returncode is None and timeout > 0:
			time.sleep(poll_period)
			timeout -= poll_period
			poll_period = min(timeout,poll_period+1)
			s.poll()
		if timeout > 0:
			if s.returncode == 0:
				return 0 #equivalent
			if s.returncode == 6:
				return 1 #parse
			return 2 #fail
		else:
			s.kill()
			return 3 #timeout
	
varCount = 10
def compareProgs(c,out):
	with open('cbmc'+str(os.getpid())+'.c','w') as fcbmc:
		c = filter(lambda x:len(x)>0,c.strip().split(' '))
		yi_c = 0
		for i in range(len(c)):
			if c[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
				if c[i] == 'Y':
					c[i] = c[i]+'_'+str(yi_c)+'_1'
					yi_c += 1
				else:
					c[i] = c[i]+'_0'
		c = ' '.join(c)
		out = filter(lambda x:len(x)>0,out.strip().split(' '))
		yi_out = 0
		for i in range(len(out)):
			if out[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
				if out[i] == 'Y':
					out[i] = out[i]+'_'+str(yi_out)+'_1'
					yi_out += 1
				else:
					out[i] = out[i]+'_1'
		out = ' '.join(out)
		if yi_c != yi_out:
			return 2 #fail
		fcbmc.write('void main() {\n')
		fcbmc.write('\tint '+','.join(map(lambda i:'Y_'+str(i)+'_0,Y_'+str(i)+'_1',range(yi_c))))
		for i in range(varCount):
			fcbmc.write(',X'+str(i)+'_0,X'+str(i)+'_1')
		fcbmc.write(';\n')
		for i in range(varCount):
			fcbmc.write('\t__CPROVER_assume(X'+str(i)+'_0==X'+str(i)+'_1);\n')
		fcbmc.write('\t'+c+'\n')
		fcbmc.write('\t'+out+'\n')
		for i in range(yi_c):
			fcbmc.write('\t__CPROVER_assert(Y_'+str(i)+'_0==Y_'+str(i)+'_1,"computations not equivalent ('+str(i)+')");\n')
		fcbmc.write('}')
	ret = runCbmc(60)
	os.remove('cbmc'+str(os.getpid())+'.c')
	return ret

def evaluateProg((c,ll,out)):
	if len(out) == 0:
		return (c,ll,out,3) #fail
	else:
		if c == out:
			return (c,ll,out,0) #identical
		else:
			res = compareProgs(c,out)
			if res == 0:
				return (c,ll,out,1) #equivalent
			else:
				if res == 1:
					return (c,ll,out,2) #parse
				else:
					if res == 2:
						return (c,ll,out,3) #fail
					else:
						return (c,ll,out,4) #timeout

def evaluate(fc,fll,fout,fi=None,fs=None,ff=None,fp=None,ft=None):
	nidentical = 0
	nsuccess = 0
	nfail = 0
	nparse = 0
	ntimeout = 0
	cs = [l.strip() for l in fc.readlines()]
	lls = [l.strip() for l in fll.readlines()]
	outs = [l.strip() for l in fout.readlines()]
	max_len = max(len(cs),len(lls),len(outs))
	cs = cs + ['']*(max_len-len(cs))
	lls = lls + ['']*(max_len-len(lls))
	outs = outs + ['']*(max_len-len(outs))
	pool = multiprocessing.Pool(processes=5)
	results = pool.map(evaluateProg,map(lambda i:(cs[i],lls[i],outs[i]),range(len(cs))))
	for x in results:
		if x[3] == 0:
			if fi:
				fi.write(x[0]+'\t'+x[1]+'\t'+x[2]+'\n')
			nidentical += 1
		else:
			if x[3] == 1:
				if fs:
					fs.write(x[0]+'\t'+x[1]+'\t'+x[2]+'\n')
				nsuccess += 1
			else:
				if x[3] == 2:
					if fp:
						fp.write(x[0]+'\t'+x[1]+'\t'+x[2]+'\n')
					nparse += 1
				else:
					if x[3] == 3:
						if ff:
							ff.write(x[0]+'\t'+x[1]+'\t'+x[2]+'\n')
						nfail += 1
					else:
						if ft:
							ft.write(x[0]+'\t'+x[1]+'\t'+x[2]+'\n')
						ntimeout += 1
	return (nidentical,nsuccess,nparse,nfail,ntimeout)

def main(f):
	with open(f+'.identical.tsv','w') as fidentical:
		with open(f+'.equivalent.tsv','w') as fsuccess:
			with open(f+'.fail.tsv', 'w') as ffail:
				with open(f+'.parse.tsv', 'w') as fparse:
					with open(f+'.timeout.tsv', 'w') as ftimeout:
						fidentical.write('c\tll\tout\n')
						fsuccess.write('c\tll\tout\n')
						ffail.write('c\tll\tout\n')
						fparse.write('c\tll\tout\n')
						ftimeout.write('c\tll\tout\n')
						with open(f+'.corpus.c','r') as fc:
							with open(f+'.corpus.ll', 'r') as fll:
								with open(f+'.corpus.out', 'r') as fout:
									(nidentical,nsuccess,nparse,nfail,ntimeout) = evaluate(fc,fll,fout,fidentical,fsuccess,ffail,fparse,ftimeout)
	print str(nidentical)+' statements translated identically'
	print str(nsuccess)+' statements translated equivalently'
	print str(nparse)+' translated statements failed to parse'
	print str(nfail)+' translated statements are not equivalent'
	print str(ntimeout)+' translation evaluations timed-out'

if __name__ == "__main__":
	main(sys.argv[1])
 