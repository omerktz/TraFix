import argparse
import os

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
            for l in fin.readlines():
                fout.write(l.replace(',','","').replace('\t',','))
    os.remove(f+'.tsv')
else:
    with open(f+'.csv','r') as fin:
        with open(f+'.tsv','w') as fout:
            for l in fin.readlines():
                fout.write(l.replace('\t',' ').replace('","','~_~').replace(',','\t').replace('~_~',','))
    os.remove(f+'.csv')
