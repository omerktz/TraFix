import sys
import os
import numpy

from scipy.spatial import distance
def embedding_distance(x,y):
  return distance.euclidean(x,y)

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
  with open(sys.argv[2]+'.csv','w') as f:
    f.write('Word,Raw,,Parsed\n')
    for i in range(len(vocab)):
      f.write(vocab[i]+','+embeddings[i]+',,'+embeddings[i].replace(' ',',')+'\n')
  os.remove(sys.argv[2])
  with open(sys.argv[2]+'.dist.csv', 'w') as f:
    f.write(','+','.join(map(lambda i:vocab[i], range(len(vocab))))+'\n')
    for i in range(len(embeddings)):
      embeddings[i] = map(lambda y: float(y), filter(lambda x: len(x)>0, embeddings[i].split(' ')))
    for i in range(len(vocab)):
      f.write(vocab[i]+','+','.join(map(lambda j:str(embedding_distance(embeddings[j], embeddings[i])), range(len(vocab))))+'\n')