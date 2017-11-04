import os
import codecs
import re
import numpy as np
import matplotlib
# to run on headless server
matplotlib.use('Agg')
# noinspection PyPep8
from matplotlib import pyplot as plt


# consts
UNK = 'UNK'
BEGIN_SEQ = '<s>'
END_SEQ = '</s>'
PAD = 'PAD'


def argmax(arr, k):

    k = min(k, arr.size)

    # get k best indices
    indices = np.argpartition(arr, -k)[-k:]

    # sorted
    indices = indices[np.argsort(arr[indices])]

    # flip so first has largest value
    return np.flip(indices, 0)

def write_model_config_file(hyper_params, train_inputs_path, train_outputs_path, dev_inputs_path, dev_outputs_path,
                        test_inputs_path, test_outputs_path, output_file_path):

    # write hyperparams
    with codecs.open(output_file_path + '.modelinfo.txt', 'w', encoding='utf8') as f:
        f.write('train inputs path = ' + str(train_inputs_path) + '\n')
        f.write('train outputs path = ' + str(train_outputs_path) + '\n')

        f.write('dev inputs path = ' + str(dev_inputs_path) + '\n')
        f.write('dev outputs path = ' + str(dev_outputs_path) + '\n')

        f.write('test inputs path = ' + str(test_inputs_path) + '\n')
        f.write('test outputs path = ' + str(test_outputs_path) + '\n')

        for param in hyper_params:
            f.write(param + ' = ' + str(hyper_params[param]) + '\n')

def write_results_files(output_file_path, final_results):

    # write predictions
    predictions_path = output_file_path + '.predictions'
    with codecs.open(predictions_path, 'w', encoding='utf8') as predictions:
        for i, line in enumerate(final_results):
            predictions.write(u'{}\n'.format(line))

    return predictions_path

# evaluates bleu over two lists of unicode strings (u'')
def evaluate_bleu(gold, predictions, predictions_file_path=None):
    if not predictions_file_path:
        predictions_file_path = os.path.dirname(__file__) + '/predictions.tmp'
        gold_path = os.path.dirname(__file__) + '/gold.tmp'
    else:
        gold_path = predictions_file_path + '.gold'

    with codecs.open(predictions_file_path, 'w', encoding='utf8') as predictions_file:
        for i, line in enumerate(predictions):
            predictions_file.write(u'{}\n'.format(line))

    with codecs.open(gold_path, 'w', encoding='utf8') as gold_file:
        for i, line in enumerate(gold):
            gold_file.write(u'{}\n'.format(line))

    print 'evaluating {} vs. {}'.format(predictions_file_path, gold_path)
    bleu = evaluate_bleu_from_files(gold_path, predictions_file_path)
    # os.remove(predictions_path)
    # os.remove(gold_path)
    return bleu


def evaluate_bleu_from_files(gold_outputs_path, output_file_path):
    os.chdir(os.path.dirname(__file__))
    bleu_path = output_file_path + '.eval'
    os.system('perl utils/multi-bleu-detok.perl {} < {} > {}'.format(gold_outputs_path, output_file_path, bleu_path))
    with codecs.open(bleu_path, encoding='utf8') as f:
        lines  = f.readlines()

    if len(lines) > 0:
        var = re.search(r'BLEU\s+=\s+(.+?),', lines[0])
        bleu = var.group(1)
    else:
        bleu = 0

    os.remove(bleu_path)

    return float(bleu)


# get list of word ids for each timestep in the batch, do padding and masking. If batch size is 1 return None as masks
def get_batch_word_ids(batch_seqs, x2int):
    net_len = 0
    masks = []
    batch_word_ids = []

    # need to maintain longest seq len since *output* seqs are not sorted by length
    max_seq_len = len(batch_seqs[0])
    for seq in batch_seqs:
        if len(seq) > max_seq_len:
            max_seq_len = len(seq)

    for i in range(max_seq_len):
        if len(batch_seqs) > 1:
            # masking
            mask = [(1 if len(seq) > i else 0) for seq in batch_seqs]
            masks.append(mask)
            net_len += sum(mask)
        else:
            # no masking
            masks = None
            net_len = len(batch_seqs[0])
        batch_word_ids.append([])

        # get word ids
        for seq in batch_seqs:
            # pad short seqs
            if i > len(seq) - 1:
                batch_word_ids[i].append(x2int[PAD])
            else:
                if seq[i] in x2int:
                    batch_word_ids[i].append(x2int[seq[i]])
                else:
                    batch_word_ids[i].append(x2int[UNK])

    return batch_word_ids, masks, net_len


def plot_to_file(y_vals, x_name, x_vals, file_path):

    plots = []
    with plt.style.context('fivethirtyeight'):
        for (name, vals) in y_vals:
            p, = plt.plot(x_vals, vals, label=name)
            plots.append(p)
        plt.legend(loc='upper left', handles=plots)
    plt.savefig(file_path)
