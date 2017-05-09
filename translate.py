import sys
import os
from nematus.translate import main as translate

def main(f,m):
	with open(f+'.corpus.ll','r') as fin:
		with open(f+'corpus.out','w') as fout:
			translate([m],fin,fout,n_process=6)#suppress_unk=True)

if __name__ == "__main__":
	main(sys.argv[1],os.path.join(sys.argv[2],sys.argv[3]))
