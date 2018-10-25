def create_out_file(filename):
	with open(filename+'.corpus.hl', 'r') as f:
		lines = [x.strip() for x in f.readlines()]
	with open(filename+'.corpus.1.out', 'w') as f:
		for i in range(len(lines)):
			f.write(str(i)+' ||| '+lines[i]+'\n')

if __name__ == "__main__":
	import argparse
	parser = argparse.ArgumentParser(description="Generate out file from hl file")
	parser.add_argument('dataset', type=str, help="name of dataset file to use as input hl file")
	args = parser.parse_args()
	create_out_file(args.dataset)