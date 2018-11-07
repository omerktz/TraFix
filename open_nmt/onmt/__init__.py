""" Main entry point of the ONMT library """
from __future__ import division, print_function

import open_nmt.onmt.inputters
import open_nmt.onmt.encoders
import open_nmt.onmt.decoders
import open_nmt.onmt.models
import open_nmt.onmt.utils
import open_nmt.onmt.modules
from open_nmt.onmt.trainer import Trainer
import sys
import open_nmt.onmt.utils.optimizers
open_nmt.onmt.utils.optimizers.Optim = open_nmt.onmt.utils.optimizers.Optimizer
sys.modules["onmt.Optim"] = open_nmt.onmt.utils.optimizers

# For Flake
__all__ = [open_nmt.onmt.inputters, open_nmt.onmt.encoders, open_nmt.onmt.decoders, open_nmt.onmt.models,
           open_nmt.onmt.utils, open_nmt.onmt.modules, "Trainer"]

__version__ = "0.5.0"
