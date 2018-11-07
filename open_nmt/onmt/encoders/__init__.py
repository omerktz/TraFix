"""Module defining encoders."""
from open_nmt.onmt.encoders.encoder import EncoderBase
from open_nmt.onmt.encoders.transformer import TransformerEncoder
from open_nmt.onmt.encoders.rnn_encoder import RNNEncoder
from open_nmt.onmt.encoders.cnn_encoder import CNNEncoder
from open_nmt.onmt.encoders.mean_encoder import MeanEncoder

__all__ = ["EncoderBase", "TransformerEncoder", "RNNEncoder", "CNNEncoder",
           "MeanEncoder"]
