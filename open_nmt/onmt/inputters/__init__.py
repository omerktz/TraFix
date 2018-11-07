"""Module defining inputters.

Inputters implement the logic of transforming raw data to vectorized inputs,
e.g., from a line of text to a sequence of embeddings.
"""
from open_nmt.onmt.inputters.inputter import collect_feature_vocabs, make_features, \
    collect_features, get_num_features, \
    load_fields_from_vocab, get_fields, \
    save_fields_to_vocab, build_dataset, \
    build_vocab, merge_vocabs, OrderedIterator
from open_nmt.onmt.inputters.dataset_base import DatasetBase, PAD_WORD, BOS_WORD, \
    EOS_WORD, UNK
from open_nmt.onmt.inputters.text_dataset import TextDataset, ShardedTextCorpusIterator
from open_nmt.onmt.inputters.image_dataset import ImageDataset
from open_nmt.onmt.inputters.audio_dataset import AudioDataset, \
    ShardedAudioCorpusIterator


__all__ = ['PAD_WORD', 'BOS_WORD', 'EOS_WORD', 'UNK', 'DatasetBase',
           'collect_feature_vocabs', 'make_features',
           'collect_features', 'get_num_features',
           'load_fields_from_vocab', 'get_fields',
           'save_fields_to_vocab', 'build_dataset',
           'build_vocab', 'merge_vocabs', 'OrderedIterator',
           'TextDataset', 'ImageDataset', 'AudioDataset',
           'ShardedTextCorpusIterator', 'ShardedAudioCorpusIterator']
