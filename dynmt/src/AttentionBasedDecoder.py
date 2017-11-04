import dynet as dn
import numpy as np
import common


class AttentionBasedDecoder:
    def __init__(self, y2int, int2y, params, max_prediction_len, plot, beam_size, diverse = False):
        self.y2int = y2int
        self.int2y = int2y
        self.decoder_rnn = params['decoder_rnn']
        self.init_lookup = params['init_lookup']
        self.output_lookup = params['output_lookup']
        self.max_prediction_len = max_prediction_len
        self.plot = plot
        self.beam_size = beam_size
        self.params = params
        self.diverse = diverse

    def compute_decoder_batch_loss(self, encoded_inputs, input_masks, output_word_ids, output_masks, batch_size):
        self.readout = dn.parameter(self.params['readout'])
        self.bias = dn.parameter(self.params['bias'])
        self.w_c = dn.parameter(self.params['w_c'])
        self.u_a = dn.parameter(self.params['u_a'])
        self.v_a = dn.parameter(self.params['v_a'])
        self.w_a = dn.parameter(self.params['w_a'])

        # initialize the decoder rnn
        s_0 = self.decoder_rnn.initial_state()

        # initial "input feeding" vectors to feed decoder - 3*h
        init_input_feeding = dn.lookup_batch(self.init_lookup, [0] * batch_size)

        # initial feedback embeddings for the decoder, use begin seq symbol embedding
        init_feedback = dn.lookup_batch(self.output_lookup, [self.y2int[common.BEGIN_SEQ]] * batch_size)

        # init decoder rnn
        decoder_init = dn.concatenate([init_feedback, init_input_feeding])
        s = s_0.add_input(decoder_init)

        # loss per timestep
        losses = []

        # run the decoder through the output sequences and aggregate loss
        for i, step_word_ids in enumerate(output_word_ids):

            # returns h x batch size matrix
            decoder_rnn_output = s.output()

            # compute attention context vector for each sequence in the batch (returns 2h x batch size matrix)
            attention_output_vector, alphas = self.attend(encoded_inputs, decoder_rnn_output, input_masks)

            # compute output scores (returns vocab_size x batch size matrix)
            # h = readout * attention_output_vector + bias
            h = dn.affine_transform([self.bias, self.readout, attention_output_vector])

            # encourage diversity by punishing highly confident predictions
            # TODO: support batching - esp. w.r.t. scalar inputs
            if self.diverse:
                soft = dn.softmax(dn.tanh(h))
                batch_loss = dn.pick_batch(-dn.log(soft), step_word_ids) \
                    - dn.log(dn.scalarInput(1) - dn.pick_batch(soft, step_word_ids)) - dn.log(dn.scalarInput(4))
            else:
                # get batch loss for this timestep
                batch_loss = dn.pickneglogsoftmax_batch(h, step_word_ids)

            # mask the loss if at least one sentence is shorter
            if output_masks and output_masks[i][-1] != 1:
                mask_expr = dn.inputVector(output_masks[i])
                # noinspection PyArgumentList
                mask_expr = dn.reshape(mask_expr, (1,), batch_size)
                batch_loss = batch_loss * mask_expr

            # input feeding approach - input h (attention_output_vector) to the decoder
            # prepare for the next iteration - "feedback"
            feedback_embeddings = dn.lookup_batch(self.output_lookup, step_word_ids)
            decoder_input = dn.concatenate([feedback_embeddings, attention_output_vector])
            s = s.add_input(decoder_input)

            losses.append(batch_loss)

        # sum the loss over the time steps and batch
        total_batch_loss = dn.sum_batches(dn.esum(losses))

        return total_batch_loss

    # Luong et. al 2015 attention mechanism:
    def attend(self, encoded_inputs, h_t, input_masks=None):
        # encoded_inputs dimension is: seq len x 2*h x batch size, h_t dimension is h x batch size (for bilstm encoder)
        if len(encoded_inputs) == 1:
            # no need to attend if only one input state, compute output directly
            h_output = dn.tanh(self.w_c * dn.concatenate([h_t, encoded_inputs[0]]))
            # return trivial alphas (all 1's since one input gets all attention)
            if input_masks:
                # if batching
                alphas = dn.inputTensor([1]*len(input_masks[0]), batched=True)
            else:
                alphas = dn.inputTensor([1], batched=True)
            return h_output, alphas

        # iterate through input states to compute attention scores
        # scores = [v_a * dn.tanh(w_a * h_t + u_a * h_input) for h_input in blstm_outputs]
        w_a_h_t = self.w_a * h_t
        scores = [self.v_a * dn.tanh(dn.affine_transform([w_a_h_t, self.u_a, h_input])) for h_input in encoded_inputs]

        concatenated = dn.concatenate(scores)
        if input_masks:
            # if batching, multiply attention scores with input masks to zero-out scores for padded inputs
            dn_masks = dn.inputTensor(input_masks, batched=True)
            concatenated = dn.cmult(concatenated, dn_masks)

        # normalize scores
        alphas = dn.softmax(concatenated)

        # compute context vector with weighted sum for each seq in batch
        bo = dn.concatenate_cols(encoded_inputs)
        c = bo * alphas
        # c = dn.esum([h_input * dn.pick(alphas, j) for j, h_input in enumerate(blstm_outputs)])

        # compute output vector using current decoder state and context vector
        h_output = dn.tanh(self.w_c * dn.concatenate([h_t, c]))

        return h_output, alphas

    # decode output seq with greedy search given input seq
    def predict_greedy(self, encoder, input_seq):
        dn.renew_cg()

        self.readout = dn.parameter(self.params['readout'])
        self.bias = dn.parameter(self.params['bias'])
        self.w_c = dn.parameter(self.params['w_c'])
        self.u_a = dn.parameter(self.params['u_a'])
        self.v_a = dn.parameter(self.params['v_a'])
        self.w_a = dn.parameter(self.params['w_a'])

        alphas_mtx = []

        if len(input_seq) == 0:
            return []

        # encode input sequence
        blstm_outputs, input_masks = encoder.encode_batch([input_seq])

        # initialize the decoder rnn
        s = self.decoder_rnn.initial_state()

        # set prev_output_vec for first lstm step as BEGIN_WORD concatenated with special padding vector
        prev_output_vec = dn.concatenate([self.output_lookup[self.y2int[common.BEGIN_SEQ]], self.init_lookup[0]])
        predicted_sequence = []
        i = 0

        # run the decoder through the sequence and predict output symbols
        while i < self.max_prediction_len:

            # get current h of the decoder
            s = s.add_input(prev_output_vec)
            decoder_rnn_output = s.output()

            # perform attention step
            attention_output_vector, alphas = self.attend(blstm_outputs, decoder_rnn_output)

            if self.plot:
                val = alphas.vec_value()
                alphas_mtx.append(val)

            # compute output probabilities
            # h = readout * attention_output_vector + bias
            h = dn.affine_transform([self.bias, self.readout, attention_output_vector])

            # TODO: understand why diverse needs tanh before softmax
            if self.diverse:
                h = dn.tanh(h)
            probs = dn.softmax(h)

            # find best candidate output - greedy
            next_element_index = np.argmax(probs.npvalue())
            predicted_sequence.append(self.int2y[next_element_index])

            # check if reached end of word
            if predicted_sequence[-1] == common.END_SEQ:
                break

            # prepare for the next iteration - "feedback"
            prev_output_vec = dn.concatenate([self.output_lookup[next_element_index], attention_output_vector])
            i += 1

        # remove the end seq symbol
        return predicted_sequence[0:-1], alphas_mtx

    def predict_beamsearch(self, encoder, input_seq):
        if len(input_seq) == 0:
            return []

        dn.renew_cg()

        self.readout = dn.parameter(self.params['readout'])
        self.bias = dn.parameter(self.params['bias'])
        self.w_c = dn.parameter(self.params['w_c'])
        self.u_a = dn.parameter(self.params['u_a'])
        self.v_a = dn.parameter(self.params['v_a'])
        self.w_a = dn.parameter(self.params['w_a'])

        alphas_mtx = []

        # encode input sequence
        blstm_outputs, input_masks = encoder.encode_batch([input_seq])

        # complete sequences and their probabilities
        final_states = []

        # initialize the decoder rnn
        s_0 = self.decoder_rnn.initial_state()

        # holds beam step index mapped to (sequence, probability, decoder state, attn_vector) tuples
        beam = {-1: [([common.BEGIN_SEQ], 1.0, s_0, self.init_lookup[0])]}
        i = 0

        # expand another step if didn't reach max length and there's still beams to expand
        while i < self.max_prediction_len and len(beam[i - 1]) > 0:

            # create all expansions from the previous beam:
            new_hypos = []
            for hypothesis in beam[i - 1]:
                prefix_seq, prefix_prob, prefix_decoder, prefix_attn = hypothesis
                last_hypo_symbol = prefix_seq[-1]

                # cant expand finished sequences
                if last_hypo_symbol == common.END_SEQ:
                    continue

                # expand from the last symbol of the hypothesis
                try:
                    prev_output_vec = self.output_lookup[self.y2int[last_hypo_symbol]]
                except KeyError:
                    # not a known symbol
                    print 'impossible to expand, key error: ' + str(last_hypo_symbol)
                    continue

                decoder_input = dn.concatenate([prev_output_vec, prefix_attn])
                s = prefix_decoder.add_input(decoder_input)
                decoder_rnn_output = s.output()

                # perform attention step
                attention_output_vector, alphas = self.attend(blstm_outputs, decoder_rnn_output)

                # save attention weights for plotting
                # TODO: add attention weights properly to allow building the attention matrix for the best path
                if self.plot:
                    val = alphas.vec_value()
                    alphas_mtx.append(val)

                # compute output probabilities
                # h = readout * attention_output_vector + bias
                h = dn.affine_transform([self.bias, self.readout, attention_output_vector])

                # TODO: understand why diverse needs tanh before softmax
                if self.diverse:
                    h = dn.tanh(h)
                probs = dn.softmax(h)
                probs_val = probs.npvalue()

                # TODO: maybe should choose nbest from all expansions and not only from nbest of each hypothesis?
                # find best candidate outputs
                n_best_indices = common.argmax(probs_val, self.beam_size)
                for index in n_best_indices:
                    p = probs_val[index]
                    new_seq = prefix_seq + [self.int2y[index]]
                    new_prob = prefix_prob * p
                    if new_seq[-1] == common.END_SEQ or i == self.max_prediction_len - 1:
                        # TODO: add to final states only if fits in k best?
                        # if found a complete sequence or max length - add to final states
                        final_states.append((new_seq[1:-1], new_prob))
                    else:
                        new_hypos.append((new_seq, new_prob, s, attention_output_vector))

            # add the most probable expansions from all hypotheses to the beam
            new_probs = np.array([p for (s, p, r, a) in new_hypos])
            argmax_indices = common.argmax(new_probs, self.beam_size)
            beam[i] = [new_hypos[l] for l in argmax_indices]
            i += 1

        # get nbest results from final states found in search
        final_probs = np.array([p for (s, p) in final_states])
        argmax_indices = common.argmax(final_probs, self.beam_size)
        nbest_seqs = [final_states[l] for l in argmax_indices]

        return nbest_seqs, alphas_mtx
