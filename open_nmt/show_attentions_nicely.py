import re
import pandas as pd
import numpy as np
from PIL import Image
import matplotlib.pyplot as plt
import heapq
from visualize_attn import showAttention
import os

def prepare_and_write_line(w,line):
    line = line.replace('*0.', '0.')
    line = re.sub(r" +", "&", line)
    w.write(line[1:-2] + '\n')

def create_file_of_one_word_by_num(lines, sentence_num, output_path):
    sentence_passed = 0
    first_line_of_word = 0
    word_file_path = output_path + 'sentence_num_' + str(sentence_num) + '_attention.txt'
    w = open(word_file_path, 'w+')
    for line in lines:
        if sentence_num < sentence_passed:
            break
        if sentence_num == sentence_passed:
            if(first_line_of_word == 0):
                first_line_of_word = 1
                line = '&' + line
            prepare_and_write_line(w,line)

        if(line.__contains__('</s>')):
            sentence_passed +=1
    w.close()
    if(sentence_num > sentence_passed):
        return None
    return word_file_path

def make_smaller_file_with_only_important_words(attn_file, output_path, sentence_num):
    over_lap = 5
    

    with open(attn_file) as all_attn:
        lines = all_attn.readlines()
        word_file_path = create_file_of_one_word_by_num(lines,sentence_num,output_path)

    if(word_file_path == None):
        return False
    df = pd.read_csv(word_file_path, sep='&')
    origin_values = df.values
    origin_columns = df.columns[1:]
    todrop = []
    for column in origin_columns:
        if(not any(i > 0.1 for i in df[column])):
            todrop.append(column)

    df = df.drop(columns=todrop)
    df.to_csv(word_file_path.replace('.txt', '.csv'),index=False)
    attns = np.asarray(map(lambda x: x[1:], df.values))
    attns = np.multiply(attns, 256)
    attns = attns.astype(int)

    output_sentence = df.ix[:,0]
    input_sentence = ' '.join(re.sub(r"\.\d+", "", str(e)) for e in df.columns[1:])
    image_output_path = word_file_path.replace('.txt', '.png')
    # print image_output_path
    showAttention(input_sentence, output_sentence, attns, image_output_path)
    os.system('rm ' + word_file_path)
    return True

def make_smaller_file_with_only_important_data(attn_file, output_path, num_of_sentences_to_print, only_failed_words, failed_path):
    if(only_failed_words == 1):
        df = pd.read_csv(failed_path)
        words_to_attend = df.index
        if words_to_attend.size == 0:
            return
        for i in words_to_attend:
            make_smaller_file_with_only_important_words(attn_file, output_path, i)
    else:
        i = 0
        while (finished == True and (num_of_sentences_to_print == 0 or i <= num_of_sentences_to_print)):
            finished = make_smaller_file_with_only_important_words(attn_file, output_path, i)
            i += 1

    # df = pd.read_csv(output_path + 'attn_only_ordered_nicely.txt', sep=' ')
    # df.to_csv(output_path + 'attn_only_ordered_nicely_%d.csv' %iter_num ,index=False)

def print_image_of_one_sentence(attn_file, word, sentence_num, output_path, enlarge_pixels):
    with open(attn_file) as all_attn:
        lines = all_attn.readlines()
        if(word != None):
            a = 5
        elif ( sentence_num != None ):
            create_file_of_one_word_by_num(lines, sentence_num, output_path)
            df = pd.read_csv(output_path + 'sentence_num_' + str(sentence_num) + '_attention.txt',sep='&')
            columns = df.columns
            array = df.as_matrix()
            newArr = []
            lines_for_new_readable_file = []
            for a in array:
                a = [val for val in a[1:] for _ in range(enlarge_pixels)]
                for x in range(enlarge_pixels):
                    newArr.append(a)
            newArr = np.asarray(newArr)
            newArr = newArr.astype(float) * 256
            newArr = newArr.astype(int)
            im = Image.fromarray(newArr,'L')
            im.save('b.jpg')
            plt.imshow(newArr, cmap='gray')
            plt.show()
        else:
            print 'wrong usage'
            exit(1)



if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Evaluate NMT as active learner")
    parser.add_argument('attn_file', type=str, help="The attn file to read from")
    parser.add_argument('output_path', type=str, help="The place to create out new file")
    parser.add_argument('-word', type=str, help ="The word that we want to print", default=None)
    parser.add_argument('-sentence_num', type=int, help="The number of word that we want to print", default=2)
    parser.add_argument('-enlarge_pixels', type=int, help="if we want to make the pixels larger", default=1)
    parser.add_argument('-num_highest_attentions', type=int, help="how many attentions would we like to see for each word", default=10)
    parser.add_argument('-num_of_sentences_to_print', type=int, help="number of words to print", default=0)
    parser.add_argument('-only_failed_words', type=int, help='will we order attn of only failed results', default=0)
    parser.add_argument('-failed_path', type=str, help='path of failed results', default='')
    parser.add_argument('-iter_num', type=int, help='the number of the itteration', default=0)
    args = parser.parse_args()
    make_smaller_file_with_only_important_data(args.attn_file, args.num_highest_attentions, args.output_path, args.num_of_sentences_to_print, args.only_failed_words, args.failed_path, args.iter_num)
    # print_image_of_one_word(args.attn_file, args.word, args.sentence_num, args.output_path, args.enlarge_pixels)
