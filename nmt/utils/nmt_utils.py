# Copyright 2017 Google Inc. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

"""Utility functions specifically for NMT."""
from __future__ import print_function

import codecs
import time
import numpy as np
import tensorflow as tf

from ..utils import evaluation_utils
from ..utils import misc_utils as utils
from ..utils import show_attentions_nicely

__all__ = ["decode_and_evaluate", "get_translation"]

def decode_and_evaluate_for_attn(
                        model,
                        sess,
                        trans_file,
                        subword_option,
                        tgt_eos,
                        infer_data,
                        failed_translations_csv):
    """Decode a test set and compute a score according to the evaluation task."""
    # Decode
    import pandas as pd
    utils.print_out("  decoding to output %s" % trans_file)
    sentence_numbers_to_translate = pd.read_csv(failed_translations_csv).index
    start_time = time.time()
    num_sentences = 0
    batch_size = 1
    with codecs.getwriter("utf-8")(
        tf.gfile.GFile(trans_file, mode="wb")) as trans_f:
      trans_f.write("")  # Write empty string to ensure file is created.
      num_translations_per_input = 1

      while True:
        try:
          num_sentences += batch_size
          sentence_id = num_sentences - batch_size
          nmt_outputs, infer_summary = model.decode(sess)
          nmt_outputs = np.expand_dims(nmt_outputs, 0)
          if (not sentence_numbers_to_translate.contains(sentence_id)):
              print(str(sentence_id) + ' not in fails')
              continue
          print(str(sentence_id) + ' yes in fails')
          word_file_path = trans_file + '_%d' %sentence_id + '.txt'
          # print(infer_data[sentence_id])
          for sent_id in range(batch_size):
            for beam_id in range(num_translations_per_input):
              translation = get_translation(
                  nmt_outputs[beam_id],
                  sent_id,
                  tgt_eos=tgt_eos,
                  subword_option=subword_option)
              trans_f.write((translation + b"\n").decode("utf-8"))
              if num_translations_per_input == 1:
                  if infer_summary is not None:  # Attention models
                      image_file = "/tmp/tmp.png"
                      utils.print_out("  save attention image to %s*" % image_file)
                      image_summ = tf.Summary()
                      image_summ.ParseFromString(infer_summary)
                      with tf.gfile.GFile(image_file, mode="w") as img_f:
                          img_f.write(image_summ.value[0].image.encoded_image_string)
                      import matplotlib.image as mpimg
                      import pandas as pd
                      img = mpimg.imread(image_file)
                      imgTrans = img.transpose()
                      print(translation.split(' ').__len__())
                      t = translation + ' ' + tgt_eos
                      print(t.split(' ').__len__())
                      df = pd.DataFrame(imgTrans,index=t.split(' ')[:350])
                      columns = infer_data[sentence_id].split(' ')
                      new_columns = []
                      columns_visited = []
                      for column in columns:
                          columns_visited.append(column)
                          new_columns.append(column + '.%d' %columns_visited.count(column))
                      df.columns = new_columns
                      show_attentions_nicely.from_df_total(df, word_file_path, 5, 20)
                      df.to_csv(word_file_path,sep='&')
        except tf.errors.OutOfRangeError:
          utils.print_time(
              "  done, num sentences %d, num translations per input %d" %
              (num_sentences, num_translations_per_input), start_time)
          break



def decode_and_evaluate(name,
                        model,
                        sess,
                        trans_file,
                        ref_file,
                        metrics,
                        subword_option,
                        beam_width,
                        tgt_eos,
                        num_translations_per_input=1,
                        decode=True,
                        infer_mode="greedy"):
  """Decode a test set and compute a score according to the evaluation task."""
  # Decode
  if decode:
    utils.print_out("  decoding to output %s" % trans_file)

    start_time = time.time()
    num_sentences = 0
    with codecs.getwriter("utf-8")(
        tf.gfile.GFile(trans_file, mode="wb")) as trans_f:
      trans_f.write("")  # Write empty string to ensure file is created.

      if infer_mode == "greedy":
        num_translations_per_input = 1
      elif infer_mode == "beam_search":
        num_translations_per_input = min(num_translations_per_input, beam_width)

      while True:
        try:
          nmt_outputs, _ = model.decode(sess)
          if infer_mode != "beam_search":
            nmt_outputs = np.expand_dims(nmt_outputs, 0)

          batch_size = nmt_outputs.shape[1]
          num_sentences += batch_size

          for sent_id in range(batch_size):
            for beam_id in range(num_translations_per_input):
              translation = get_translation(
                  nmt_outputs[beam_id],
                  sent_id,
                  tgt_eos=tgt_eos,
                  subword_option=subword_option)
              trans_f.write((translation + b"\n").decode("utf-8"))
        except tf.errors.OutOfRangeError:
          utils.print_time(
              "  done, num sentences %d, num translations per input %d" %
              (num_sentences, num_translations_per_input), start_time)
          break

  # Evaluation
  evaluation_scores = {}
  if ref_file and tf.gfile.Exists(trans_file):
    for metric in metrics:
      score = evaluation_utils.evaluate(
          ref_file,
          trans_file,
          metric,
          subword_option=subword_option)
      evaluation_scores[metric] = score
      utils.print_out("  %s %s: %.1f" % (metric, name, score))

  return evaluation_scores


def get_translation(nmt_outputs, sent_id, tgt_eos, subword_option):
  """Given batch decoding outputs, select a sentence and turn to text."""
  if tgt_eos: tgt_eos = tgt_eos.encode("utf-8")
  # Select a sentence
  output = nmt_outputs[sent_id, :].tolist()

  # If there is an eos symbol in outputs, cut them at that point.
  if tgt_eos and tgt_eos in output:
    output = output[:output.index(tgt_eos)]

  if subword_option == "bpe":  # BPE
    translation = utils.format_bpe_text(output)
  elif subword_option == "spm":  # SPM
    translation = utils.format_spm_text(output)
  else:
    translation = utils.format_text(output)

  return translation
