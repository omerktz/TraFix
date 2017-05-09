import nematus.nmt as nmt
import sys
import os
f = sys.argv[1]
mdir = sys.argv[2]
m = sys.argv[3]
nmt.train(saveto=os.path.join(mdir,m), datasets=[f+'.corpus.ll', f+'.corpus.c'], dictionaries=[f+'.vocab.ll.json', f+'.vocab.c.json'], valid_datasets=None, domain_interpolation_indomain_datasets=None,batch_size=80)#, finish_after=10000000)
          
