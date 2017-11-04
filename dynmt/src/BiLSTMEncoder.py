import dynet as dn
import common

class BiLSTMEncoder:
    def __init__(self, x2int, params):
        self.x2int = x2int
        self.input_lookup = params['input_lookup']
        self.encoder_frnn = params['encoder_frnn']
        self.encoder_rrnn = params['encoder_rrnn']

    # bilstm encode batch, each element in the result is a matrix of 2*h x batch size elements
    def encode_batch(self, input_seq_batch):
        f_outputs = []
        r_outputs = []
        final_outputs = []

        to_encode = [[common.BEGIN_SEQ] + s + [common.END_SEQ] for s in input_seq_batch]

        # get the word ids for each step, after padding
        word_ids, masks, tot_chars = common.get_batch_word_ids(to_encode, self.x2int)

        # init rnns
        f_state = self.encoder_frnn.initial_state()
        r_state = self.encoder_rrnn.initial_state()

        # max seq len after padding (assuming first sentence is longest since sorting by length in train_model())
        max_seq_len = len(to_encode[0])

        # iterate in both directions
        for i in xrange(max_seq_len):
            f_state = f_state.add_input(dn.lookup_batch(self.input_lookup, word_ids[i]))
            f_outputs.append(f_state.output())

            r_state = r_state.add_input(dn.lookup_batch(self.input_lookup, word_ids[max_seq_len - i - 1]))
            r_outputs.append(r_state.output())

        # concatenate forward and backward representations for each step
        for i in xrange(max_seq_len):
            concatenated = dn.concatenate([f_outputs[i], r_outputs[max_seq_len - i - 1]])
            final_outputs.append(concatenated)

        return final_outputs, masks