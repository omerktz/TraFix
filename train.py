import nematus.nmt as nmt
import sys
import os
f = sys.argv[1]
v = sys.argv[2]
mdir = sys.argv[3]
m = sys.argv[4]
e = sys.argv[5]
nmt.train(saveto=os.path.join(mdir,m), datasets=[f+'.corpus.ll', f+'.corpus.c'], dictionaries=[f+'.vocab.ll.json', f+'.vocab.c.json'], batch_size=200, valid_datasets=[v+'.corpus.ll', v+'.corpus.c'], validFreq=1000, patience=20, valid_batch_size=200, external_validation_script=e)
          
