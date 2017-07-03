import sys
import os

def main(f,n):
	with open(f+'.alignment','r') as fin:
		current = -1
		while current != n:
			line = fin.readline().strip()
			current = int(line[:line.find(' ')])
			if current != n:
				line = fin.readline().strip()
				while len(line) > 0:
					line = fin.readline().strip()
		with open('tmp','w') as fout:
			fout.write('0'+line[line.find(' '):]+'\n')
			while len(line) > 0:
				line = fin.readline().strip()
				fout.write(line+'\n')
	decode_command = 'python nematus/utils/plot_heatmap.py -i tmp'
	os.system(decode_command)
	os.remove('tmp')

if __name__ == "__main__":
	main(sys.argv[1],int(sys.argv[2])-1)