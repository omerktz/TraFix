import codecs
def main():
    base_path = '/Users/roeeaharoni'
    in_path =  '{}/git/research/nmt/data/news-de-en/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.de'.format(base_path)
    out_path = '{}/git/research/nmt/data/news-de-en/dev/newstest2015-deen.tok.penntrg.clean.true.bpe.en'.format(base_path)

    proc_in_path = '{}/git/dynet-seq2seq-attn/data/toy_de.txt'.format(base_path)
    proc_out_path = '{}/git/dynet-seq2seq-attn/data/toy_en.txt'.format(base_path)

    line_count = 0
    with codecs.open(in_path, 'r', 'utf8') as in_file:
        with codecs.open(proc_in_path, 'w', 'utf8') as proc_in_file:
            with codecs.open(out_path, 'r', 'utf8') as out_file:
                with codecs.open(proc_out_path, 'w', 'utf8') as proc_out_file:
                    line = in_file.readline()
                    outline = out_file.readline()
                    while line:
                        in_tokens = line.split()
                        out_tokens = outline.split()
                        if len(in_tokens) < 20 or len(out_tokens) < 20:
                            print line_count
                            line = in_file.readline()
                            outline = out_file.readline()
                            continue
                        else:
                            line_count += 1
                            proc_in_file.write(' '.join(in_tokens[0:20]) + '\n')
                            proc_out_file.write(' '.join(out_tokens[0:20]) + '\n')
                            line = in_file.readline()
                            outline = out_file.readline()
                            if line_count > 19:
                                break



if __name__ == '__main__':
    main()