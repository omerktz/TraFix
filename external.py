from evaluate import evaluate
from translate import main as translate
import os
import sys
import shutil
v = sys.argv[1]
mdir = sys.argv[2]
m = sys.argv[3]
p = int(sys.argv[4])
h = sys.argv[5]

translate(v, os.path.join(mdir,m+'.dev.npz'))
with open(v+'.corpus.c','r') as fc:
	with open(v+'.corpus.ll', 'r') as fll:
		with open(v+'.corpus.out', 'r') as fout:
			(ni,ns,np,nf) = evaluate(fc,fll,fout)
			print 'external progress: '+str((ni,ns,np,nf))

os.remove(v+'.corpus.out')

if os.path.exists(h):
	with open(h,'r') as history:
		vals = map(lambda x:int(x), history.readline().strip().split('\t'))
	hi = vals[0]
	hs = vals[1]
	hp = vals[2]
	hf = vals[3]
	count = vals[4]
	better = False
	if (ns+ni) > (hs+hi):
		better = True
	else:
		if np < hp:
			better = True
	with open(h,'w') as history:
		if better:
			shutil.copy(m+'.dev.npz',m+'.best.npz')
			shutil.copy(m+'.dev.npz.json',m+'.best.npz.json')
			history.write(str(ni)+'\t'+str(ns)+'\t'+str(np)+'\t'+str(nf)+'\t0\n')
		else:
			count += 1
			if count > p:
				print 'No progress for last '+str(p)+' validations. Terminating!'
				os.kill(pid, signal.SIGKILL)
			else:
				history.write(str(hi)+'\t'+str(hs)+'\t'+str(hp)+'\t'+str(hf)+'\t'+str(count)+'\n')
else:
	with open(h,'w') as history:
		shutil.copy(m+'.dev.npz',m+'.best.npz')
		shutil.copy(m+'.dev.npz.json',m+'.best.npz.json')
		history.write(str(ni)+'\t'+str(ns)+'\t'+str(np)+'\t'+str(nf)+'\t0\n')