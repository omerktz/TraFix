"""  Attention and normalization modules  """
from open_nmt.onmt.modules.util_class import LayerNorm, Elementwise
from open_nmt.onmt.modules.gate import context_gate_factory, ContextGate
from open_nmt.onmt.modules.global_attention import GlobalAttention
from open_nmt.onmt.modules.conv_multi_step_attention import ConvMultiStepAttention
from open_nmt.onmt.modules.copy_generator import CopyGenerator, CopyGeneratorLossCompute
from open_nmt.onmt.modules.multi_headed_attn import MultiHeadedAttention
from open_nmt.onmt.modules.embeddings import Embeddings, PositionalEncoding
from open_nmt.onmt.modules.weight_norm import WeightNormConv2d
from open_nmt.onmt.modules.average_attn import AverageAttention

__all__ = ["LayerNorm", "Elementwise", "context_gate_factory", "ContextGate",
           "GlobalAttention", "ConvMultiStepAttention", "CopyGenerator",
           "CopyGeneratorLossCompute", "MultiHeadedAttention", "Embeddings",
           "PositionalEncoding", "WeightNormConv2d", "AverageAttention"]
