import sys
import os
from nematus.translate import main as translate

def worker(p,m):
	#print 'translating '+p
	with open(p+'.ll','r') as fin:
		with open(p+'.out','w') as fout:
			translate([m],fin,fout,n_process=6)#suppress_unk=True)

def main(dir):
	for d in os.listdir(os.path.join(dir,'line')):
		x = os.path.join(dir,'line',d)
		fs = set([os.path.join(x,f[:f.find('.')]) for f in os.listdir(x)])
		map(lambda f:worker(f),fs)

if __name__ == "__main__":
	main(sys.argv[1],sys.argv[2])
