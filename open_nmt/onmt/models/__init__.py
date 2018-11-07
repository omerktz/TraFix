"""Module defining models."""
from open_nmt.onmt.models.model_saver import build_model_saver, ModelSaver
from open_nmt.onmt.models.model import NMTModel

__all__ = ["build_model_saver", "ModelSaver",
           "NMTModel", "check_sru_requirement"]
