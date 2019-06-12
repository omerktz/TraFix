import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
import matplotlib

import numpy as np

def showAttention(input_sentence, output_words, attentions, output_image_path):
    # matplotlib.use('Agg')
    # Set up figure with colorbar
    fig = plt.figure(figsize=(70,25))
    ax = fig.add_subplot(111)
    cax = ax.matshow(attentions, cmap='gray')
    fig.colorbar(cax)

    # Set up axes
    ax.set_xticklabels([''] + input_sentence.split(' ') +
                       ['<EOS>'], rotation=90)
    ax.set_yticklabels([''] + output_words)

    # Show label at every tick
    ax.xaxis.set_major_locator(ticker.MultipleLocator(1))
    ax.yaxis.set_major_locator(ticker.MultipleLocator(1))
    plt.savefig(output_image_path)
    plt.close(fig)
    # plt.show()

if __name__ == "__main__":
    b = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
    input = 'a b c'
    output = ['n','m','l']
    showAttention(input,output,b)


