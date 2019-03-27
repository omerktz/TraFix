import random
import codecs

# generate toy parallel sequences: characters to numbers
def main():
    ordered = True
    lines = 500
    input_file_path = '../data/toy/input_ordered_test.txt'
    output_file_path = '../data/toy/output_ordered_test.txt'
    with codecs.open(input_file_path, 'w', encoding='utf8') as input:
        with codecs.open(output_file_path, 'w', encoding='utf8') as output:
            for i in xrange(lines):
                input_line = ''
                output_line = ''
                length = random.randrange(1, 30)
                prev_index = 0
                for j in xrange(length):
                    char_index = random.randrange(97, 122)
                    if ordered:
                        while char_index < prev_index:
                            char_index = random.randrange(97, 122)
                        prev_index = char_index
                    char = chr(char_index)
                    input_line += char + ' '
                    output_line += str(char_index) + ' '
                output.write(output_line + '\n')
                input.write(input_line + '\n')


if __name__ == '__main__':
    main()