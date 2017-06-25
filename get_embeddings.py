import sys
import os
import numpy
if (len(sys.argv) < 3) or (len(sys.argv) > 4):
  print 'Usage: python '+sys.argv[0]+' <model npz file> <output file> [<vocabulary file>]'
  sys.exit(1)
embedding = numpy.load(sys.argv[1])['Wemb']
numpy.savetxt(sys.argv[2],embedding)
if len(sys.argv) == 4:
  with open(sys.argv[2],'r') as f:
    embeddings = [l.strip() for l in f.readlines()]
  with open(sys.argv[3],'r') as f:
    vocab = [l.strip() for l in f.readlines()][1:-1]
  vocab = map(lambda x: x[:x.rfind(':')][1:-1], vocab)
  with open(sys.argv[2]+'.tsv','w') as f:
    f.write('Word\tRaw\t\tParsed\n')
    for i in range(len(vocab)):
      f.write(vocab[i]+'\t'+embeddings[i]+'\t\t'+embeddings[i].replace(' ','\t')+'\n')
  os.remove(sys.argv[2])