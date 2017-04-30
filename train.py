import nematus.nmt as nmt
import sys
import os
d = sys.argv[1]
mdir = sys.argv[2]
m = sys.argv[3]
nmt.train(saveto=os.path.join(mdir,m), datasets=[os.path.join(d,'corpus.ll'), os.path.join(d,'corpus.c')], dictionaries=[os.path.join(d,'vocab.ll.json'), os.path.join(d,'vocab.c.json')], valid_datasets=None, domain_interpolation_indomain_datasets=None,batch_size=80)#, finish_after=10000000)
          
