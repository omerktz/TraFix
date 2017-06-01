import sys
import os

def main(f,m,k):
	decode_command = 'python nematus/nematus/translate.py -m {} -i {} -o {} -a {} -p 5 --suppress-unk --n-best -k {}'.format(m, f+'.corpus.ll', f+'.corpus.out'+str(k), f+'.alignment'+str(k),k)
	os.system(decode_command)

if __name__ == "__main__":
	main(sys.argv[1],os.path.join(sys.argv[2],sys.argv[3]),int(sys.argv[4]))