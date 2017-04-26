import nematus.nmt as nmt
nmt.train(saveto='model.ll-c.npz', datasets=['data/corpus.ll', 'data/corpus.c'], dictionaries=['data/vocab.ll.json', 'data/vocab.c.json'], valid_datasets=None, domain_interpolation_indomain_datasets=None)#, finish_after=10000000)
          