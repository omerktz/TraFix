import sys
import os
import numpy

from scipy.spatial import distance
def embedding_distance(x,y):
  return distance.euclidean(x,y)

import re

import enum
Types = enum.Enum('Types', 'Var Tmp Num Op Assign Other Model')

def getType(w):
  if w in ['eos', 'UNK']:
    return Types.Model
  if w == '=':
    return Types.Assign
  if w.startswith('%'):
    if re.match('%[0-9]+$',w):
      return Types.TmpVar
    return Types.Var
  if re.match('^\-?[0-9]+$',w):
    return Types.Num
  if w in ['add','sub','load','store','sdiv','mul','srem']:
    return Types.Op
  return Types.Other

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
      f.write('"'+vocab[i].replace('"','""')+'","'+embeddings[i].replace('"','""')+'",,"'+embeddings[i].replace('"','""').replace(' ','","')+'"\n')
  os.remove(sys.argv[2])
  with open(sys.argv[2]+'.dist.csv', 'w') as f:
    f.write(','+','.join(map(lambda i:vocab[i].replace('"','""'), range(len(vocab))))+'\n')
    for i in range(len(embeddings)):
      embeddings[i] = map(lambda y: float(y), filter(lambda x: len(x)>0, embeddings[i].split(' ')))
    for i in range(len(vocab)):
      f.write('"'+vocab[i].replace('"','""')+'","'+'","'.join(map(lambda j:str(embedding_distance(embeddings[j], embeddings[i])), range(len(vocab))))+'"\n')
  with open('embeddings.js', 'w') as fjs:
    fjs.write('var vocab = [' + ','.join(map(lambda x: '"' + x + '"', vocab)) + '];\n')
    fjs.write('var types = [' + ','.join(map(lambda x: '"' + getType(x).name + '"', vocab)) + '];\n')
    fjs.write('var title = "' + sys.argv[1] + ' embeddings";\n')
    fjs.write('var matrix = [')
    for i in range(len(vocab)):
      if i > 0:
        fjs.write(',')
      fjs.write('[' + ','.join(map(lambda j: str(embedding_distance(embeddings[i], embeddings[j])), range(len(vocab)))) + ']')
    fjs.write('];\n')
