"""

Sequence to sequence learning with an attention mechanism implemented using dynet's python bindings.

Usage:
  dynmt.py [--dynet-mem MEM] [--dynet-gpus GPU] [--dynet-devices DEV] [--dynet-autobatch AUTO] [--input-dim=INPUT]
  [--hidden-dim=HIDDEN] [--epochs=EPOCHS] [--lstm-layers=LAYERS] [--optimization=OPTIMIZATION] [--reg=REGULARIZATION]
  [--batch-size=BATCH] [--beam-size=BEAM] [--learning=LEARNING] [--plot] [--override] [--eval] [--ensemble=ENSEMBLE]
  [--vocab-size=VOCAB] [--eval-after=EVALAFTER] [--max-len=MAXLEN] [--last-state] [--max-pred=MAXPRED] [--compact]
  [--grad-clip=GRADCLIP] [--max-patience=MAXPATIENCE] [--models-to-save=SAVE] [--max] [--diverse] TRAIN_INPUTS_PATH
  TRAIN_OUTPUTS_PATH DEV_INPUTS_PATH DEV_OUTPUTS_PATH TEST_INPUTS_PATH TEST_OUTPUTS_PATH RESULTS_PATH...

Arguments:
  TRAIN_INPUTS_PATH    train inputs path
  TRAIN_OUTPUTS_PATH   train outputs path
  DEV_INPUTS_PATH      development inputs path
  DEV_OUTPUTS_PATH     development outputs path
  TEST_INPUTS_PATH     test inputs path
  TEST_OUTPUTS_PATH    test outputs path
  RESULTS_PATH  results file path

Options:
  -h --help                     show this help message and exit
  --dynet-mem MEM               allocates MEM bytes for dynet
  --dynet-devices DEV           CPU/GPU ids to use
  --dynet-gpus GPU              how many gpus to use
  --dynet-autobatch AUTO        switch auto-batching on
  --input-dim=INPUT             input embeddings dimension [default: 300]
  --hidden-dim=HIDDEN           LSTM hidden layer dimension [default: 100]
  --epochs=EPOCHS               amount of training epochs [default: 1]
  --lstm-layers=LAYERS          amount of layers in LSTM [default: 1]
  --optimization=OPTIMIZATION   chosen optimization method (ADAM/SGD/ADAGRAD/MOMENTUM/ADADELTA) [default: ADADELTA]
  --reg=REGULARIZATION          regularization parameter for optimization [default: 0]
  --learning=LEARNING           learning rate parameter for optimization [default: 0.0001]
  --batch-size=BATCH            batch size [default: 1]
  --beam-size=BEAM              beam size in beam search [default: 5]
  --vocab-size=VOCAB            max vocabulary size [default: 99999]
  --eval-after=EVALAFTER        amount of train batches to wait before evaluation [default: 1000]
  --max-len=MAXLEN              max train sequence length [default: 50]
  --max-pred=MAXPRED            max predicted sequence length [default: 50]
  --grad-clip=GRADCLIP          gradient clipping threshold [default: 5.0]
  --max-patience=MAXPATIENCE    amount of checkpoints without improvement on dev before early stopping [default: 100]
  --plot                        plot a learning curve while training each model
  --override                    override existing model with the same name, if exists
  --ensemble=ENSEMBLE           ensemble model paths separated by a comma
  --last-state                  only use last encoder state
  --eval                        skip training, do only evaluation
  --compact                     use compact lstm builder
  --models-to-save=SAVE         amount of models to save during training [default: 10]
  --max                         use MaxPooling encoder
  --diverse                     symmetric diverse loss
"""

import numpy as np
import random
import glob
import prepare_data
import progressbar
import time
import os
import common
import dynet as dn
from docopt import docopt
from collections import defaultdict
import matplotlib
import BiLSTMEncoder
import AttentionBasedDecoder
import MaxPoolEncoder
import LastBiLSTMStateEncoder

# to run on headless server
matplotlib.use('Agg')
# noinspection PyPep8
from matplotlib import pyplot as plt

# add masking for the input (zero-out attention weights) - done
# save k models every checkpoint and not only if best model - done
# OOP refactoring for encoder/decoder - done
# continue logging from last saved checkpoint values - done
# write saved checkpoint metadata to file: epoch, update, best score, best perplexity - taking from log - done
# TODO: measure sentences per second while *decoding*
# TODO: add ensembling support by interpolating probabilities
# TODO: debug with non-english output (i.e. reverse translation from en to he)
# TODO: print n-best lists to file
# TODO: carefully rename model parameters the same way they are named in a specific paper


def main(train_inputs_path, train_outputs_path, dev_inputs_path, dev_outputs_path, test_inputs_path, test_outputs_path,
         results_file_path, input_dim, hidden_dim, epochs, layers, optimization, plot, override, eval_only, ensemble,
         batch_size, vocab_size, eval_after, max_len):

    # write model config file (.modelinfo)
    common.write_model_config_file(arguments, train_inputs_path, train_outputs_path, dev_inputs_path,
                                   dev_outputs_path, test_inputs_path, test_outputs_path, results_file_path)

    # print arguments for current run
    for param in arguments:
        print param + '=' + str(arguments[param])

    # load train, dev and test data
    train_inputs, input_vocabulary, train_outputs, output_vocabulary = \
        prepare_data.load_parallel_data(train_inputs_path, train_outputs_path, vocab_size, max_len)

    dev_inputs, dev_in_vocab, dev_outputs, dev_out_vocab = \
        prepare_data.load_parallel_data(dev_inputs_path, dev_outputs_path, vocab_size, 999)

    test_inputs, test_in_vocab, test_outputs, test_out_vocab = \
        prepare_data.load_parallel_data(test_inputs_path, test_outputs_path, vocab_size, 999)

    # add unk symbols to vocabularies
    input_vocabulary.append(common.UNK)
    output_vocabulary.append(common.UNK)

    # add pad symbols to vocabularies
    input_vocabulary.append(common.PAD)
    output_vocabulary.append(common.PAD)

    # add begin/end sequence symbols to vocabularies
    input_vocabulary.append(common.BEGIN_SEQ)
    input_vocabulary.append(common.END_SEQ)
    output_vocabulary.append(common.BEGIN_SEQ)
    output_vocabulary.append(common.END_SEQ)

    # symbol 2 int and int 2 symbol
    x2int = dict(zip(input_vocabulary, range(0, len(input_vocabulary))))
    y2int = dict(zip(output_vocabulary, range(0, len(output_vocabulary))))
    int2y = {index: x for x, index in y2int.items()}

    print 'input vocab size: {}'.format(len(x2int))
    print 'output vocab size: {}'.format(len(y2int))

    # try to load existing model
    model_file_name = '{}_bestmodel.txt'.format(results_file_path)
    if os.path.isfile(model_file_name) and not override:
        print 'loading existing model from {}'.format(model_file_name)
        model, params = load_best_model(input_vocabulary, output_vocabulary, results_file_path, input_dim, hidden_dim,
                                        layers)
        print 'loaded existing model successfully'
    else:
        print 'could not find existing model or explicit override was requested. started training from scratch...'
        model, params = build_model(input_vocabulary, output_vocabulary, input_dim, hidden_dim, layers)

    # initialize the encoder object
    encoder = None
    if arguments['--max']:
        encoder = MaxPoolEncoder.MaxPoolEncoder(x2int, params)
        print 'using MaxPoolEncoder...'
    if arguments['--last-state']:
        encoder = LastBiLSTMStateEncoder.LastBiLSTMStateEncoder(x2int, params)
        print 'using LastStateEncoder...'
    if not encoder:
        encoder = BiLSTMEncoder.BiLSTMEncoder(x2int, params)
        print 'using BiLSTMEncoder...'

    if arguments['--diverse']:
        diverse = True
    else:
        diverse = False

    decoder = AttentionBasedDecoder.AttentionBasedDecoder(y2int, int2y, params, max_prediction_len, plot_param,
                                                          beam_param, diverse)

    # train the model
    if not eval_only:
        model, params, last_epoch, best_epoch = train_model(model, encoder, decoder, params, train_inputs,
                                                            train_outputs, dev_inputs, dev_outputs, y2int, int2y,
                                                            epochs, optimization, results_file_path, plot, batch_size,
                                                            eval_after)
        print 'last epoch is {}'.format(last_epoch)
        print 'best epoch is {}'.format(best_epoch)
        print 'finished training'
    else:
        print 'skipped training, evaluating on test set...'

    # evaluate using an ensemble
    if ensemble:
        # predict test set using ensemble majority
        predicted_sequences = predict_with_ensemble_majority(input_vocabulary, output_vocabulary, x2int, y2int,
                                                             int2y, ensemble, hidden_dim, input_dim, layers,
                                                             test_inputs, test_outputs)
    else:
        # TODO: load best model from disk before test eval in case training was performed
        # predict test set using a single model
        predicted_sequences = predict_multiple_sequences(params, encoder, decoder, y2int, int2y, test_inputs)
    if len(predicted_sequences) > 0:

        # evaluate the test predictions
        amount, accuracy = evaluate(predicted_sequences, test_inputs, test_outputs, print_results=False,
                                    predictions_file_path=results_file_path + '.test.predictions')
        print 'test bleu: {}% '.format(accuracy)

        final_results = []
        for i in xrange(len(test_outputs)):
            index = ' '.join(test_inputs[i])
            final_output = ' '.join(predicted_sequences[index])
            final_results.append(final_output)

        # write output files
        common.write_results_files(results_file_path, final_results)

    return


def predict_with_ensemble_majority(input_vocabulary, output_vocabulary, x2int, y2int, int2y, ensemble,
                                   hidden_dim, input_dim, layers, test_inputs, test_outputs):
    ensemble_model_names = ensemble.split(',')
    print 'ensemble paths:\n {}'.format('\n'.join(ensemble_model_names))
    ensemble_models = []

    # load ensemble models
    for ens in ensemble_model_names:
        model, params = load_best_model(input_vocabulary, output_vocabulary, ens, input_dim, hidden_dim, layers)
        ensemble_models.append((model, params))

    # predict the entire test set with each model in the ensemble
    ensemble_predictions = []
    for em in ensemble_models:
        model, params = em
        encoder = BiLSTMEncoder.BiLSTMEncoder(x2int, params)
        decoder = AttentionBasedDecoder.AttentionBasedDecoder(y2int, int2y, params, max_prediction_len, plot_param,
                                                              beam_param)

        predicted_sequences = predict_multiple_sequences(params, encoder, decoder, y2int, int2y, test_inputs)
        ensemble_predictions.append(predicted_sequences)

    # perform voting for each test input
    majority_predicted_sequences = {}
    string_to_template = {}
    test_data = zip(test_inputs, test_outputs)
    for i, (input_seq, output_seq) in enumerate(test_data):
        joint_index = input_seq
        prediction_counter = defaultdict(int)
        for ens in ensemble_predictions:
            prediction_str = ''.join(ens[joint_index])
            prediction_counter[prediction_str] += 1
            string_to_template[prediction_str] = ens[joint_index]
            print 'template: {} prediction: {}'.format(''.join([e.encode('utf-8') for e in ens[joint_index]]),
                                                       prediction_str.encode('utf-8'))

        # return the most predicted output
        majority_prediction_string = max(prediction_counter, key=prediction_counter.get)
        print 'chosen:{} with {} votes\n'.format(majority_prediction_string.encode('utf-8'),
                                                 prediction_counter[majority_prediction_string])
        majority_predicted_sequences[joint_index] = string_to_template[majority_prediction_string]

    return majority_predicted_sequences


def save_best_model(model, model_file_path):
    tmp_model_path = model_file_path + '_bestmodel.txt'
    print 'saving to ' + tmp_model_path
    model.save(tmp_model_path)
    print 'saved to {0}'.format(tmp_model_path)


def save_model(model, model_file_path, updates, models_to_save=None):
    tmp_model_path = model_file_path + '_{}.txt'.format(updates)
    print 'saving to ' + tmp_model_path
    model.save(tmp_model_path)
    print 'saved to {0}'.format(tmp_model_path)

    if models_to_save:
        files = filter(os.path.isfile, glob.glob(model_file_path + '*[0-9].*txt'))
        files.sort(key=lambda x: os.path.getmtime(x))
        if len(files) > models_to_save:
            print 'removing {}'.format(files[0])
            os.remove(files[-1])


def load_best_model(input_vocabulary, output_vocabulary, results_file_path, input_dim, hidden_dim, layers):
    tmp_model_path = results_file_path + '_bestmodel.txt'
    model, params = build_model(input_vocabulary, output_vocabulary, input_dim, hidden_dim, layers)

    print 'trying to load model from: {}'.format(tmp_model_path)
    model.populate(tmp_model_path)
    return model, params


def build_model(input_vocabulary, output_vocabulary, input_dim, hidden_dim, layers):
    # define all model parameters
    # TODO: add logic for "smart" parameter allocation according to the user's chosen architecture
    print 'creating model...'

    model = dn.ParameterCollection()

    params = {}

    # input embeddings
    params['input_lookup'] = model.add_lookup_parameters((len(input_vocabulary), input_dim))

    # init vector for input feeding
    params['init_lookup'] = model.add_lookup_parameters((1, 3 * hidden_dim))

    # output embeddings
    params['output_lookup'] = model.add_lookup_parameters((len(output_vocabulary), input_dim))

    # used in softmax output
    params['readout'] = model.add_parameters((len(output_vocabulary), 3 * hidden_dim))
    params['bias'] = model.add_parameters(len(output_vocabulary))

    # rnn's
    if bool(arguments['--compact']):
        params['encoder_frnn'] = dn.CompactVanillaLSTMBuilder(layers, input_dim, hidden_dim, model)
        params['encoder_rrnn'] = dn.CompactVanillaLSTMBuilder(layers, input_dim, hidden_dim, model)
    else:
        params['encoder_frnn'] = dn.LSTMBuilder(layers, input_dim, hidden_dim, model)
        params['encoder_rrnn'] = dn.LSTMBuilder(layers, input_dim, hidden_dim, model)

    # attention MLPs - Luong-style with extra v_a from Bahdanau

    # concatenation layer for h (hidden dim), c (2 * hidden_dim)
    params['w_c'] = model.add_parameters((3 * hidden_dim, 3 * hidden_dim))

    # concatenation layer for h_input (hidden_dim), h_output (hidden_dim)
    params['w_a'] = model.add_parameters((hidden_dim, hidden_dim))

    # concatenation layer for h (hidden dim), c (2 * hidden_dim)
    params['u_a'] = model.add_parameters((hidden_dim, 2 * hidden_dim))

    # concatenation layer for h_input (2 * hidden_dim), h_output (hidden_dim)
    params['v_a'] = model.add_parameters((1, hidden_dim))

    # 3 * HIDDEN_DIM + input_dim - gets the feedback output embedding, "input feeding" approach for attn
    params['decoder_rnn'] = dn.LSTMBuilder(layers, 3 * hidden_dim + input_dim, hidden_dim, model)

    print 'finished creating model'

    return model, params


def train_model(model, encoder, decoder, params, train_inputs, train_outputs, dev_inputs, dev_outputs, y2int, int2y,
                epochs, optimization, results_file_path, plot, batch_size, eval_after):
    print 'training...'

    np.random.seed(17)
    random.seed(17)

    # sort training sentences by length in descending order
    train_data = zip(train_inputs, train_outputs)
    train_data.sort(key=lambda t: - len(t[0]))
    train_order = [x * batch_size for x in range(len(train_data) / batch_size + 1)]

    # sort dev sentences by length in descending order
    dev_batch_size = 1
    dev_data = zip(dev_inputs, dev_outputs)
    dev_data.sort(key=lambda t: - len(t[0]))
    dev_order = [x * dev_batch_size for x in range(len(dev_data) / dev_batch_size + 1)]

    if optimization == 'ADAM':
        trainer = dn.AdamTrainer(model)  # lam=REGULARIZATION, alpha=LEARNING_RATE, beta_1=0.9, beta_2=0.999, eps=1e-8)
    elif optimization == 'MOMENTUM':
        trainer = dn.MomentumSGDTrainer(model)
    elif optimization == 'SGD':
        trainer = dn.SimpleSGDTrainer(model)
    elif optimization == 'ADAGRAD':
        trainer = dn.AdagradTrainer(model)
    elif optimization == 'ADADELTA':
        trainer = dn.AdadeltaTrainer(model)
    else:
        trainer = dn.SimpleSGDTrainer(model)

    trainer.set_clip_threshold(float(arguments['--grad-clip']))
    seen_examples_count = 0
    total_loss = 0
    best_dev_epoch = 0
    best_train_epoch = 0
    patience = 0
    train_len = len(train_outputs)
    dev_len = len(dev_inputs)
    avg_train_loss = -1
    train_loss_patience = 0
    train_loss_patience_threshold = 99999999
    max_patience = int(arguments['--max-patience'])
    log_path = results_file_path + '_log.txt'
    start_epoch, checkpoints_x, train_loss_y, dev_loss_y, dev_accuracy_y = read_from_log(log_path)

    if len(train_loss_y) > 0:
        total_batches = checkpoints_x[-1]
        best_avg_train_loss = max(train_loss_y)
        best_dev_accuracy = max(dev_accuracy_y)
        best_dev_loss = max(dev_loss_y)
    else:
        total_batches = 0
        best_avg_train_loss = 999999
        best_dev_loss = 999999
        best_dev_accuracy = 0

    # progress bar init
    # noinspection PyArgumentList
    widgets = [progressbar.Bar('>'), ' ', progressbar.ETA()]
    train_progress_bar = progressbar.ProgressBar(widgets=widgets, maxval=epochs).start()

    for e in xrange(start_epoch, epochs):

        # shuffle the batch start indices in each epoch
        random.shuffle(train_order)
        batches_per_epoch = len(train_order)
        start = time.time()

        # go through batches
        for i, batch_start_index in enumerate(train_order, start=1):
            total_batches += 1

            # get batch examples
            batch_inputs = [x[0] for x in train_data[batch_start_index:batch_start_index + batch_size]]
            batch_outputs = [x[1] for x in train_data[batch_start_index:batch_start_index + batch_size]]
            actual_batch_size = len(batch_inputs)

            # skip empty batches
            if actual_batch_size == 0 or len(batch_inputs[0]) == 0:
                continue

            # compute batch loss

            # debug prints for batch seq lengths
            # print 'batch {} seq lens'.format(i)
            # print [len(s) for s in batch_inputs]
            loss = compute_batch_loss(encoder, decoder, batch_inputs, batch_outputs, y2int)

            # forward pass
            total_loss += loss.scalar_value()
            loss.backward()

            # update parameters
            trainer.update()

            seen_examples_count += actual_batch_size

            # avg loss per sample
            avg_train_loss = total_loss / float(i * batch_size + e * train_len)

            # start patience counts only after 20 batches
            if avg_train_loss < best_avg_train_loss and total_batches > 20:
                best_avg_train_loss = avg_train_loss
                train_loss_patience = 0
            else:
                train_loss_patience += 1
                if train_loss_patience > train_loss_patience_threshold:
                    print 'train loss patience exceeded: {}'.format(train_loss_patience)
                    return model, params, e, best_train_epoch

            if total_batches % 100 == 0 and total_batches > 0:
                print 'epoch {}: {} batches out of {} ({} examples out of {}) total: {} batches, {} examples. avg \
loss per example: {}'.format(e,
                             i,
                             batches_per_epoch,
                             i * batch_size,
                             train_len,
                             total_batches,
                             total_batches*batch_size,
                             avg_train_loss)

                # print sentences per second
                end = time.time()
                elapsed_seconds = end - start
                print '{} sentences per second'.format(seen_examples_count / elapsed_seconds)
                seen_examples_count = 0
                start = time.time()

            # checkpoint
            if total_batches % eval_after == 0:

                print 'starting checkpoint evaluation'
                dev_bleu, dev_loss = checkpoint_eval(encoder, decoder, params, dev_batch_size, dev_data, dev_inputs,
                                                     dev_len, dev_order, dev_outputs, int2y, y2int,
                                                     results_file_path=results_file_path)

                log_to_file(log_path, e, total_batches, avg_train_loss, dev_loss, dev_bleu)
                save_model(model, results_file_path, total_batches, models_to_save=int(arguments['--models-to-save']))
                if dev_bleu >= best_dev_accuracy:
                    best_dev_accuracy = dev_bleu
                    best_dev_epoch = e

                    # save best model to disk
                    save_best_model(model, results_file_path)
                    print 'saved new best model'
                    patience = 0
                else:
                    patience += 1

                if dev_loss < best_dev_loss:
                    best_dev_loss = dev_loss

                print 'epoch: {0} train loss: {1:.4f} dev loss: {2:.4f} dev bleu: {3:.4f} \
best dev bleu {4:.4f} (epoch {5}) patience = {6}'.format(
                    e,
                    avg_train_loss,
                    dev_loss,
                    dev_bleu,
                    best_dev_accuracy,
                    best_dev_epoch,
                    patience)

                if patience == max_patience:
                    print 'out of patience after {0} checkpoints'.format(str(e))
                    train_progress_bar.finish()
                    if plot:
                        plt.cla()
                    print 'checkpoint patience exceeded'
                    return model, params, e, best_train_epoch

                # plotting results from checkpoint evaluation
                if plot:
                    train_loss_y.append(avg_train_loss)
                    checkpoints_x.append(total_batches)
                    dev_accuracy_y.append(dev_bleu)
                    dev_loss_y.append(dev_loss)

                    y_vals = [('train_loss', train_loss_y), ('dev loss', dev_loss_y), ('dev_bleu', dev_accuracy_y)]
                    common.plot_to_file(y_vals, x_name='total batches', x_vals=checkpoints_x,
                                        file_path=results_file_path + '_learning_curve.png')

        # update progress bar after completing epoch
        train_progress_bar.update(e)

    # update progress bar after completing training
    train_progress_bar.finish()
    if plot:
        # clear plot when done
        plt.cla()
    print 'finished training. average loss: {} best epoch on dev: {} best epoch on train: {}'.format(
        str(avg_train_loss),
        best_dev_epoch,
        best_train_epoch)

    return model, params, e, best_train_epoch


def checkpoint_eval(encoder, decoder, params, batch_size, dev_data, dev_inputs, dev_len, dev_order, dev_outputs, int2y,
                    y2int, results_file_path=None):

    # TODO: could be more efficient - now "encoding" (lookup) the dev set twice (for predictions and loss)
    print 'predicting on dev...'
    # get dev predictions
    dev_predictions = predict_multiple_sequences(params, encoder, decoder, y2int, int2y, dev_inputs)
    print 'calculating dev bleu...'
    # get dev accuracy
    dev_bleu = evaluate(dev_predictions, dev_inputs, dev_outputs, print_results=True,
                        predictions_file_path=results_file_path+'.dev.predictions')[1]

    # get dev loss
    print 'computing dev loss...'
    total_dev_loss = 0
    for i, batch_start_index in enumerate(dev_order, start=1):

        # get dev batches
        batch_inputs = [x[0] for x in dev_data[batch_start_index:batch_start_index + batch_size]]
        batch_outputs = [x[1] for x in dev_data[batch_start_index:batch_start_index + batch_size]]

        # skip empty batches
        if len(batch_inputs) == 0 or len(batch_inputs[0]) == 0:
            continue

        # TODO: remove
        # print 'dev batch {}'.format(i)
        # print 'batch sent len {}'.format(len(batch_inputs[0]))

        loss = compute_batch_loss(encoder, decoder, batch_inputs, batch_outputs, y2int)
        total_dev_loss += loss.value()

        if i % 10 == 0 and i > 0:
            print 'went through {} dev batches out of {} ({} examples out of {})'.format(i, len(dev_order),
                                                                                         i * batch_size,
                                                                                         dev_len)

    avg_dev_loss = total_dev_loss / float(len(dev_inputs))

    return dev_bleu, avg_dev_loss


def log_to_file(file_name, epoch, total_updates, train_loss, dev_loss, dev_accuracy):

    # if first log, add headers
    if not os.path.isfile(file_name):
        with open(file_name, "w") as logfile:
            logfile.write("{}\t{}\t{}\t{}\t{}\n".format(
                'epoch', 'update', 'avg_train_loss', 'avg_dev_loss', 'dev_accuracy'))

    with open(file_name, "a") as logfile:
        logfile.write("{}\t{}\t{}\t{}\t{}\n".format(epoch, total_updates, train_loss, dev_loss,
                                                        dev_accuracy))


def read_from_log(log_path):
    last_epoch = 0
    checkpoints_x = []
    train_loss_y = []
    dev_loss_y = []
    dev_accuracy_y = []
    if os.path.isfile(log_path) and not arguments['--override']:
        with open(log_path, "r") as logfile:
            line = logfile.readline()
            while line:
                splitted = line.split('\t')
                if not splitted[0].isdigit():
                    line = logfile.readline()
                    continue
                last_epoch = int(splitted[0])
                update = int(splitted[1])
                avg_train_loss = float(splitted[2])
                avg_dev_loss = float(splitted[3])
                if len(splitted) == 6:
                    # backwards compatibillity
                    dev_accuracy = float(splitted[5].strip())
                else:
                    dev_accuracy = float(splitted[4].strip())

                checkpoints_x.append(update)
                train_loss_y.append(avg_train_loss)
                dev_loss_y.append(avg_dev_loss)
                dev_accuracy_y.append(dev_accuracy)

                # read next line
                line = logfile.readline()

    return last_epoch, checkpoints_x, train_loss_y, dev_loss_y, dev_accuracy_y


def compute_batch_loss(encoder, decoder, batch_input_seqs, batch_output_seqs, y2int):
    # renew computation graph per batch
    dn.renew_cg()

    batch_size = len(batch_input_seqs)

    # encode batch with bilstm encoder: each element represents one step in time, and is a matrix of 2*h x batch size
    # for example, for sentence length of 12, blstm_outputs wil be: 12 x 2 x 100 x 16
    # note: also adding begin_seq, end_seq symbols here!
    encoded_inputs, input_masks = encoder.encode_batch(batch_input_seqs)

    # concatenate the end seq symbols to the output sequence
    padded_batch_output_seqs = [seq + [common.END_SEQ] for seq in batch_output_seqs]

    # get output word ids for each step of the decoder
    output_word_ids, output_masks, output_tot = common.get_batch_word_ids(padded_batch_output_seqs, y2int)

    total_batch_loss = decoder.compute_decoder_batch_loss(encoded_inputs, input_masks, output_word_ids, output_masks,
                                                          batch_size)

    return total_batch_loss


def predict_multiple_sequences(params, encoder, decoder, y2int, int2y, inputs):
    print 'predicting...'
    predictions = {}
    data_len = len(inputs)
    for i, input_seq in enumerate(inputs):
        if i == 0 and plot_param:
            plot_attn_weights(encoder, decoder, input_seq, filename='{}_{}.png'.format(
                              results_file_path_param, int(time.time())))
        if beam_param > 1:
            # take 1-best result
            nbest, alphas_mtx = decoder.predict_beamsearch(encoder, input_seq)

            # best hypothesis, sequence without probability
            predicted_seq = nbest[0][0]

            # TODO: remove
            print '{}/{}\n'.format(i, data_len)
            print 'input: {}\n'.format(' '.join(input_seq).encode('utf8'))
            for k, seq in enumerate(nbest):
                print '{}-best: {}'.format(k, ' '.join(seq[0]).encode('utf8') + '\n')
        else:
            predicted_seq, alphas_mtx = decoder.predict_greedy(encoder, input_seq)
        if i % 100 == 0 and i > 0:
            print 'predicted {} examples out of {}'.format(i, data_len)

        index = ' '.join(input_seq)
        predictions[index] = predicted_seq

    return predictions


def evaluate(predicted_sequences, inputs, outputs, print_results=False, predictions_file_path=None):
    if print_results:
        print 'evaluating model...'

    test_data = zip(inputs, outputs)
    eval_predictions = []
    eval_golds = []

    # go through the parallel sequence pairs
    for i, (input_seq, output_seq) in enumerate(test_data):
        index = ' '.join(input_seq)
        predicted_output = ' '.join(predicted_sequences[index])

        # create strings from sequences for debug prints and evaluation
        enc_in = ' '.join(input_seq).encode('utf8')
        enc_gold = ' '.join(output_seq).encode('utf8')
        enc_out = predicted_output.encode('utf8')

        if print_results:
            print 'input: {}'.format(enc_in)
            print 'gold output: {}'.format(enc_gold)
            print 'prediction: {}\n'.format(enc_out)

        eval_predictions.append(enc_out.decode('utf8'))
        eval_golds.append(enc_gold.decode('utf8'))

    bleu = common.evaluate_bleu(eval_golds, eval_predictions, predictions_file_path=predictions_file_path)

    if print_results:
        print 'finished evaluating model. bleu: {}\n\n'.format(bleu)

    return len(predicted_sequences), bleu


def plot_attn_weights(encoder, decoder, input_seq, filename=None):
    # predict
    output_seq, alphas_mtx = decoder.predict_greedy(encoder, input_seq)
    fig, ax = plt.subplots()

    image = np.array(alphas_mtx)
    # noinspection PyUnresolvedReferences
    ax.imshow(image, cmap=plt.cm.Blues, interpolation='nearest')

    # fix x axis ticks density - input len (+2)
    ax.xaxis.set_ticks(np.arange(0, len(alphas_mtx[0]), 1))

    # fix y axis ticks density - output len (+1)
    ax.yaxis.set_ticks(np.arange(0, len(alphas_mtx), 1))

    # set tick labels to meaningful symbols
    ax.set_xticklabels([u'begin'] + list(input_seq) + [u'end'])
    ax.set_yticklabels(list(output_seq) + [u'end'])

    # set title
    input_word = u' '.join(input_seq)
    output_word = u' '.join(output_seq)
    ax.set_title(u'attention-based alignment:\n{}->\n{}'.format(input_word, output_word))
    plt.savefig(filename)
    plt.close()


if __name__ == '__main__':
    arguments = docopt(__doc__)
    max_prediction_len = int(arguments['--max-pred'])
    plot_param = arguments['--plot']
    beam_param = int(arguments['--beam-size'])
    results_file_path_param = arguments['RESULTS_PATH'][0]

    main(arguments['TRAIN_INPUTS_PATH'], arguments['TRAIN_OUTPUTS_PATH'], arguments['DEV_INPUTS_PATH'],
         arguments['DEV_OUTPUTS_PATH'], arguments['TEST_INPUTS_PATH'], arguments['TEST_OUTPUTS_PATH'],
         arguments['RESULTS_PATH'][0], int(arguments['--input-dim']), int(arguments['--hidden-dim']),
         int(arguments['--epochs']), int(arguments['--lstm-layers']), arguments['--optimization'],
         bool(arguments['--plot']), bool(arguments['--override']), bool(arguments['--eval']), arguments['--ensemble'],
         int(arguments['--batch-size']), int(arguments['--vocab-size']), int(arguments['--eval-after']),
         int(arguments['--max-len']))
