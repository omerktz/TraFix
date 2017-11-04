import sys
import shutil
import ConfigParser
import os
import argparse

parser = argparse.ArgumentParser(description="Count inputs that match given filters")
parser.add_argument('-d', '--dataset', type=str, help="filter a dataset file", metavar="DDD", required=True)
parser.add_argument('-i', '--input', help="replace in corpus.c file", action='count')
parser.add_argument('-o', '--output', help="replace in corpus.out file", action='count')
parser.add_argument('-r', '--replacement', help="replacement for '-' (default: taken from codenator.config if exists)", type=str)
args = parser.parse_args()

print args
sys.exit(0)

if not args.replacement:
    if os.path.exists('codenator.config'):
        config = ConfigParser.ConfigParser()
        config.read('codenator.config')
        replacement = config.get('General', 'MinusReplacement')
    else:
        parser.error("No replacement available")
else:
    replacement = args.replacement

def input(d,r):
    if os.path.exists(d+'.corpus.c'):
        shutil.copy(d+'corpus.c', d+'corpus.c.bak')
        with open(d+'.corpus.c.bak','r') as fin:
            with open(d+'.corpus.c', 'w') as fout:
                for l in fin:
                    fout.write(l.replace(' - ', ' '+r+' '))

def output(d,r):
    if os.path.exists(d+'.corpus.out'):
        shutil.copy(d+'corpus.out', d+'corpus.out.bak')
        with open(d+'.corpus.out.bak','r') as fin:
            with open(d+'.corpus.out', 'w') as fout:
                for l in fin:
                    fout.write(l.replace(' '+r+' ', ' - '))

if args.input:
    input(args.dataset,replacement)

if args.output:
    output(args.dataset,replacement)


