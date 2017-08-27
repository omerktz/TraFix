import sys
import os
import numpy
import csv

sys.path.insert(0, '..')
from utils.mapWrodToType import getType

from scipy.spatial import distance
def embedding_distance(x,y):
  return distance.euclidean(x,y)

if (len(sys.argv) < 3) or (len(sys.argv) > 4):
  print 'Usage: python '+sys.argv[0]+' <model npz file> <output file> [<vocabulary file>]'
  sys.exit(1)
embedding = numpy.load(sys.argv[1])['Wemb']
numpy.savetxt(sys.argv[2],embedding)
if len(sys.argv) == 4:
  with open(sys.argv[2],'r') as f:
    embeddings = [l.strip() for l in f.readlines()]
  with open(sys.argv[3],'r') as f:
    vocab = [l.strip() for l in f.readlines()][1:-1]
  vocab = map(lambda x: x[:x.rfind(':')][1:-1], vocab)
  with open(sys.argv[2]+'.csv','w') as f:
    csvf = csv.writer(f)
    csvf.writerow(['Word','Raw','','Parsed'])
    for i in range(len(vocab)):
      csvf.writerow([vocab[i],embeddings[i],'']+embeddings[i].split(' '))
  os.remove(sys.argv[2])
  with open(sys.argv[2]+'.dist.csv', 'w') as f:
    csvf = csv.writer(f)
    csvf.writerow(['']+vocab)
    for i in range(len(embeddings)):
      embeddings[i] = map(lambda y: float(y), filter(lambda x: len(x)>0, embeddings[i].split(' ')))
    for i in range(len(vocab)):
      csvf.writerow([vocab[i]]+map(lambda j:str(embedding_distance(embeddings[j], embeddings[i])), range(len(vocab))))
  with open('embeddings.html', 'w') as fhtml:
    sortedvocab = sorted(sorted(vocab), key=lambda v: getType(v).value)
    sortedtypes = map(lambda x: getType(x).name, sortedvocab)
    fhtml.write('<!DOCTYPE html>\n<html>\n<head>\n<style>\n#raw td {\n	text-align: center;\n}\n#freeze {\n	background: rgba(128,128,128,0.25);\n    position: absolute;\n	top: 0;\n	left: 0;\n	width: 100%;\n	height: 100%;\n}\n#loader {\n	border: 16px solid #f3f3f3; /* Light grey */\n	border-top: 16px solid #3498db; /* Blue */\n	border-radius: 50%;\n    position: absolute;\n    top: 50%;\n    left: 50%;\n    margin-top: -50px;\n    margin-left: -50px;\n	width: 100px;\n	height: 100px;\n	animation: spin 2s linear infinite;\n}\n@keyframes spin {\n	0% { transform: rotate(0deg); }\n	100% { transform: rotate(360deg); }\n}\n</style>\n<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.2.1/jquery.min.js"></script>\n<script>\n')
    fhtml.write('var vocab = [' + ','.join(map(lambda x: '"' + x + '"', sortedvocab)) + '];\n')
    fhtml.write('var types = [' + ','.join(map(lambda x: '"' + x + '"', sortedtypes)) + '];\n')
    fhtml.write('var changes = [' + ','.join(map(lambda x: str(x), filter(lambda i: sortedtypes[i] != sortedtypes[i+1], range(len(sortedtypes)-1)))) + '];\n')
    fhtml.write('var title = "' + sys.argv[1] + ' embeddings";\n')
    fhtml.write('var matrix = [')
    for i in range(len(sortedvocab)):
      if i > 0:
        fhtml.write(',')
      fhtml.write('[' + ','.join(map(lambda j: str(embedding_distance(embeddings[i], embeddings[j])), range(len(sortedvocab)))) + ']')
    fhtml.write('];\n')
    fhtml.write('function populateHeatmapInner() {\n    if ($(\'input[name=display]:checked\').val() == "words") {\n        words = vocab;\n    } else {\n        words = types;\n	}\n    if ($(\'input[name=colors]:checked\').val() == "linear") {\n        normalizeVal = function(x) { return x };\n    } else {\n        normalizeVal = Math.sqrt;\n	}\n	row = \'<tr><td style="border-right: 1px solid black; border-bottom: 1px solid black;"></td>\';\n	i = 0;\n	words.forEach(function(y) {\n		row += \'<td style="border-bottom: 1px solid black;\'+(changes.indexOf(i) != -1 ? \'border-right: 1px solid black;\' : \'\')+\'"><div style="width: 50px">\'+y+\'</div></td>\';\n		i++;\n	});\n	row += \'</tr>\'\n    $("#raw").append(row);\n    i = 0;\n    words.forEach(function(x) {\n    	borderrow = changes.indexOf(i) != -1\n    	row = \'<tr id="tr_\'+i+\'"><td style="border-right: 1px solid black;\'+(borderrow ? \'border-bottom: 1px solid black;\' : \'\')+\'"><div style="width: 50px">\'+x+\'</div></td>\';\n    	j = 0;\n		matrix[i].forEach(function(y) {\n			row += \'<td class="td" id="td_\'+i+\'_\'+j+\'" style="\'+(borderrow ? \'border-bottom: 1px solid black;\' : \'\')+(changes.indexOf(j) != -1 ? \'border-right: 1px solid black;\' : \'\')+\'">\'+parseFloat(Math.round(y * 100) / 100).toFixed(2);+\'</td>\';\n			j++;\n		});\n		row += \'</tr>\'\n    	$("#raw").append(row);\n    	i++;\n    });\n    // build heatmap\n    r = $(\'#raw tr\').length - 1;\n    if (r > 0) {\n    	c = $(\'#tr_0 td\').length - 1;\n    	if (c > 1) {\n	    	minVal = maxVal = parseFloat($(\'#td_0_1\').text());\n	    	for (i = 0; i < r; i++) {\n	    		for (j = 0; j < c; j++) {\n	    		    if (i != j) {\n                        val = parseFloat($(\'#td_\' + i + \'_\' + j).text());\n                        minVal = Math.min(minVal, val);\n                        maxVal = Math.max(maxVal, val);\n                    }\n	    		}\n	    	}\n	    	rangeVal = maxVal - minVal;\n	    	for (i = 0; i < r; i++) {\n	    		for (j = 0; j < c; j++) {\n	    		    if (i != j) {\n                        val = parseFloat($(\'#td_\' + i + \'_\' + j).text());\n                        ratio = normalizeVal((val - minVal) / rangeVal);\n                       $(\'#td_\' + i + \'_\' + j).css(\'background\', \'rgba(\'+Math.round(255*ratio)+\',\'+Math.round(255*(1-ratio))+\',0,50)\');\n                    } else {\n	    		        $(\'#td_\' + i + \'_\' + j).css(\'background\', \'rgba(255,255,0,50)\');\n					}\n					$(\'#td_\' + i + \'_\' + j).attr(\'title\' , vocab[i]+\' (\'+types[i]+\') -> \'+vocab[j]+\' (\'+types[j]+\') : \'+matrix[i][j])\n	    		}\n	    	}\n	    }\n    }\n	$(\'#loader\').hide();\n    $(\'#freeze\').hide();\n};\nfunction populateHeatmap() {\n	$("#raw").empty();\n	$(\'#freeze\').show();\n	$(\'#loader\').show();\n	setTimeout(populateHeatmapInner, 0);\n}\n$(document).ready(function() {\n	document.title = title;\n	populateHeatmap();\n	$(\'input[name=display]\').click(function() {\n		populateHeatmap();\n	});\n	$(\'input[name=colors]\').click(function() {\n		populateHeatmap();\n	});\n});\n</script>\n</head>\n<body>\n<div id="freeze"><div id="loader"></div></div>\n<div>\n	<table>\n		<tr>\n			<td width="100px">\n				Display:\n			</td>\n			<td width="100px">\n				<input type="radio" name="display" value="words" checked>words\n			</td>\n			<td>\n				<input type="radio" name="display" value="types" >types\n			</td>\n		</tr>\n		<tr>\n			<td width="100px">\n				Colors:\n			</td>\n			<td width="100px">\n				<input type="radio" name="colors" value="linear" >linear\n			</td>\n			<td>\n				<input type="radio" name="colors" value="exponential" checked>exponential\n			</td>\n		</tr>\n	</table>\n</div>\n<br/><br/>\n<div>\n	<table id="raw" style="border-spacing: 0;">\n	</table>\n</div>\n</body>\n</html>\n')
