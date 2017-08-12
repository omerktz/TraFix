import argparse
import os
import csv

parser = argparse.ArgumentParser(description="convert TSV file to CSV")
parser.add_argument('-r', '--reverse', help="reverse conversion", action='count', required=False, default=False)
parser.add_argument('file', help="file to convert")
args = parser.parse_args()

f = args.file
if f.endswith('.tsv') or f.endswith('.csv'):
    f = f[:-4]

if not args.reverse:
    with open(f+'.tsv','r') as fin:
        with open(f+'.csv','w') as fout:
            csvout = csv.write(fout)
            for l in fin.readlines():
                csvout.writerow(l.strip().split('\t'))
    os.remove(f+'.tsv')
else:
    with open(f+'.csv','r') as fin:
        csvin = csv.reader(fin)
        with open(f+'.tsv','w') as fout:
            for l in list(csvin):
                fout.write('\t'.join(l)+'\n')
    os.remove(f+'.csv')
