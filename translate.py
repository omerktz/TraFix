import sys
import os

def main(f,m):
	decode_command = 'python nematus/nematus/translate.py -m {} -i {} -o {} -a {} -p 5 --suppress-unk'.format(m, f+'.corpus.ll', f+'.corpus.out', f+'.alignment')
	os.system(decode_command)

if __name__ == "__main__":
	main(sys.argv[1],os.path.join(sys.argv[2],sys.argv[3]))