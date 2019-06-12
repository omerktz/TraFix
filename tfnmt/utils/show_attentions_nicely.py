import re
import pandas as pd
import os

def prepare_and_write_line(w,line):
    line = line.replace('*0.', '0.')
    line = re.sub(r" +", "&", line)
    w.write(line[1:-2] + '\n')

def create_file_of_one_sentence_by_num(lines, sentence_num, output_path):
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

def drop_non_used_columns_from_df(df):
    todrop = []
    columns_visited = []
    for column in df.columns:
        if (not any(i > 0.1 for i in df[column])):
            todrop.append(column)
    return df.drop(columns=todrop)


def from_df_to_image_and_csv(df, word_file_path, whole_df):
    if not whole_df:
        df = drop_non_used_columns_from_df(df)
    df.columns = map(lambda col: re.sub(r"\.\d+", "", str(col)), df.columns)
    df.to_csv(word_file_path.replace('.txt', '.csv'))
    # if want to print picture (takes a lot of time)
    # attns = np.asarray(map(lambda x: x, df.values))
    # attns = np.multiply(attns, 256)
    # attns = attns.astype(int)
    #
    # output_sentence = df.index.insert(0,'')
    # input_sentence = ' '.join(df.columns)
    # image_output_path = word_file_path.replace('.txt', '.png')
    # # print image_output_path
    # showAttention(input_sentence, output_sentence, attns, image_output_path)


def from_df_total(df, word_file_path, over_lap, num_of_words_each_part):
    print str(df.columns.size)
    df = drop_non_used_columns_from_df(df)
    print str(df.columns.size)
    from_df_to_image_and_csv(df, word_file_path, True)
    print str(df.index.size)
    print str(num_of_words_each_part + over_lap)
    if df.index.size > (num_of_words_each_part + over_lap):
        i = 0
        while i < df.index.size:
            indexes_to_print = range(min(i - over_lap, 0), min(i + num_of_words_each_part, df.index.size))
            temp_df = df.loc[df.index.isin(df.index[indexes_to_print])]
            from_df_to_image_and_csv(temp_df, word_file_path.replace('.txt', '_%d.txt' %i), False)
            i += num_of_words_each_part
    os.system('rm ' + word_file_path)

def make_smaller_file_with_only_important_words(attn_file, output_path, sentence_num):
    over_lap = 5
    num_of_words_each_part = 20

    with open(attn_file) as all_attn:
        lines = all_attn.readlines()
        word_file_path = create_file_of_one_sentence_by_num(lines, sentence_num, output_path)

    if(word_file_path == None):
        return False

    df = pd.read_csv(word_file_path, sep='&')
    from_df_total(df, word_file_path, over_lap, num_of_words_each_part)
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

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Evaluate NMT as active learner")
    parser.add_argument('attn_file', type=str, help="The attn file to read from")
    parser.add_argument('output_path', type=str, help="The place to create out new file")
    parser.add_argument('-sentence_num', type=int, help="The number of word that we want to print", default=2)
    parser.add_argument('-num_of_sentences_to_print', type=int, help="number of words to print", default=0)
    parser.add_argument('-only_failed_words', type=int, help='will we order attn of only failed results', default=0)
    parser.add_argument('-failed_path', type=str, help='path of failed results', default='')
    parser.add_argument('-iter_num', type=int, help='the number of the itteration', default=0)
    args = parser.parse_args()
    make_smaller_file_with_only_important_data(args.attn_file, args.output_path, args.num_of_sentences_to_print, args.only_failed_words, args.failed_path)
