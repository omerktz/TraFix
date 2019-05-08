import codecs
import spacy
from collections import Counter
import re

def split_numbers_to_digits(tokens):
    new_tokens = []
    for i in range(len(tokens)):
        token = tokens[i]
        if re.match('^\-?[0-9]+$', token):
            digits = list(token)
            if digits[0] == '-':
                digits = ['-N'] + digits[1:]
            if i+1 < len(tokens):
                if re.match('^\-?[0-9]+$', tokens[i+1]):
                    digits += ['|']
            new_tokens += digits
        else:
            new_tokens += [token]
    return new_tokens

# preprocess the parallel data, return tokenized sequences and vocabularies
def load_parallel_data(input_seqs_path, output_seqs_path, split_numbers_in, split_numbers_out, max_seq_len=None):

    # print 'loading preprocessing model...'
    # nlp = spacy.load('en')

    # doc = nlp(u'Hello, world. Here are two sentences.')
    # texts = [u'One document.', u'...', u'Lots of documents']
    # iter_texts = (texts[i % 3] for i in xrange(100000000))
    #
    # for i, doc in enumerate(nlp.pipe(iter_texts, batch_size=50, n_threads=4)):
    #     assert doc.is_parsed
    #     if i == 100:
    #         break

    # token = doc[0]
    # sentence = next(doc.sents)
    # assert token is sentence[0]
    # assert sentence.text == 'Hello, world.'

    tokenized_input_seqs = []
    tokenized_output_seqs = []
    # input_vocab = []
    # output_vocab = []
    total_input_len = 0
    total_output_len = 0
    max_input_len = 0
    max_output_len = 0
    amount = 0
    print 'loading data from files:\n{} (splitting numbers: {})\n{} (splitting numbers: {})'.format(input_seqs_path, split_numbers_in, output_seqs_path, split_numbers_out)
    with codecs.open(output_seqs_path, encoding='utf8') as output_file:
        with codecs.open(input_seqs_path, encoding='utf8') as input_file:

            input_file_lines = input_file.readlines()
            output_file_lines = output_file.readlines()

            # split sequences by spaces
            for i in xrange(len(output_file_lines)):
                input_seq = input_file_lines[i]
                output_seq = output_file_lines[i]

                input_tokens = filter(lambda c: c not in [';', ','], input_seq.split())
                output_tokens = output_seq.split()

                if split_numbers_in:
                    input_tokens = split_numbers_to_digits(input_tokens)
                if split_numbers_out:
                    output_tokens = split_numbers_to_digits(output_tokens)

                amount += 1
                input_seq_len = len(input_tokens)
                output_seq_len = len(output_tokens)

                total_input_len += input_seq_len
                total_output_len += output_seq_len

                if input_seq_len > max_input_len:
                    max_input_len = input_seq_len

                if output_seq_len > max_output_len:
                    max_output_len = output_seq_len

                # throw away too long sequences
                # trimmed = tokens[:max_seq_len]\
                if (max_seq_len is None) or (input_seq_len < max_seq_len and output_seq_len < max_seq_len):
                        tokenized_input_seqs.append(input_tokens)
                        tokenized_output_seqs.append(output_tokens)

                # input_vocab += input_tokens
                # output_vocab += output_tokens

            print 'max input len is {}, avg input len is {}'.format(max_input_len, total_input_len/float(amount))
            print 'max output len is {}, avg output len is {}'.format(max_output_len, total_output_len / float(amount))

    # build a vocabulary from the most common symbols
    # print 'building vocabulary...'
    # most_common_input = [ite for ite, it in Counter(input_vocab).most_common(vocab_size)]
    # most_common_output = [ite for ite, it in Counter(output_vocab).most_common(vocab_size)]
    # print 'done building vocabulary'
    # return tokenized_input_seqs, list(set(most_common_input)), tokenized_output_seqs, list(set(most_common_output))
    return tokenized_input_seqs, tokenized_output_seqs

def load_vocabularies(input_seqs_path, output_seqs_path):
    input_vocab = []
    output_vocab = []
    with codecs.open(output_seqs_path, encoding='utf8') as output_file:
        with codecs.open(input_seqs_path, encoding='utf8') as input_file:
            input_file_lines = input_file.readlines()
            output_file_lines = output_file.readlines()
            # split sequences by spaces
            for i in xrange(len(input_file_lines)):
                input_vocab += filter(lambda c: c not in [';', ','], input_file_lines[i].strip().split())
            for i in xrange(len(output_file_lines)):
                output_vocab += output_file_lines[i].strip().split()
    return list(set(input_vocab)), list(set(output_vocab))
