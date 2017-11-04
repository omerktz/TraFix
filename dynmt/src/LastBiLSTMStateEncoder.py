import dynet as dn
import BiLSTMEncoder

class LastBiLSTMStateEncoder:
    def __init__(self, x2int, params):
        self.bilstm = BiLSTMEncoder.BiLSTMEncoder(x2int, params)

    # bilstm encode batch, then for each seq return max pooled vector of encoded inputs
    def encode_batch(self, input_seq_batch):
        # TODO: test with batching
        encoded_inputs, masks = self.bilstm.encode_batch(input_seq_batch)
        last_output = encoded_inputs[-1]

        # one mask per step, all are [1]'s since only one state from max pool encoder
        max_masks = [[1] * len(input_seq_batch)]
        return [last_output], max_masks