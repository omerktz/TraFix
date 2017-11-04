import dynet as dn
import BiLSTMEncoder
from collections import defaultdict
import math

class MaxPoolEncoder:
    def __init__(self, x2int, params):
        self.bilstm = BiLSTMEncoder.BiLSTMEncoder(x2int, params)

    # bilstm encode batch, then for each seq return max pooled vector of encoded inputs
    def encode_batch(self, input_seq_batch):
        # TODO: test with batching
        encoded_inputs, masks = self.bilstm.encode_batch(input_seq_batch)
        max_output = dn.emax(encoded_inputs)

        # one mask per step, all are [1]'s since only one state from max pool encoder
        max_masks = [[1] * len(input_seq_batch)]

        # vizualize how many entries are selected from each input
        self.values_per_input(encoded_inputs, input_seq_batch, max_output)

        return [max_output], max_masks

    def values_per_input(self, encoded_inputs, input_seq_batch, max_output):
        # get the value of the max-pooled vector
        max = max_output.value()

        # get the value for each bilstm output
        vals = []
        for i, input in enumerate(encoded_inputs):
            v = input.value()
            vals.append(v)

        hist = defaultdict(int)
        for i, max_val in enumerate(max):
            for j, vec in enumerate(vals):
                if math.fabs(max_val - vec[i]) < 0.000000000000001:
                    hist[j] += 1

        print '\n'
        print 'seq:' + str(input_seq_batch[0])
        print 'selected in position: '
        for key in hist:
            char = ''
            if key == 0:
                char = '<s>'
            if key == len(input_seq_batch[0]) + 1:
                char = '</s>'
            if char == '':
                char = input_seq_batch[0][key - 1]
            print str(key) + '    ' + str(hist[key]) + '   ' + char
        print sum(hist.values())
        print 'seq len: ' + str(len(input_seq_batch[0]) + 2)
        print '\n'