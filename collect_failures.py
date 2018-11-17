import itertools
import csv
import postOrderUtil
import json
def apply_number_replacements(line, replacements):
	parts = line.strip().split(" ")
	for i in range(len(parts)):
		if parts[i] in replacements.keys():
			parts[i] = replacements[parts[i]]
	return " ".join(parts)

datasets = ["test4", "test9", "test5", "test6", "test7"]
with open('unoptimized_failures.csv', 'w') as f:
	csvf = csv.writer(f)
	csvf.writerow(['input', 'expected'] + ['translation'+str(i) for i in range(5)])
	for dataset in datasets:
		with open(dataset+'.corpus.ll', 'r') as f:
			inputs = [l.strip() for l in f.readlines()]
		with open(dataset+'.corpus.hl', 'r') as f:
			expected = [l.strip() for l in f.readlines()]
		with open(dataset+'.corpus.replacements', 'r') as f:
			replacements = [json.loads(l.strip()) for l in f.readlines()]
		expected = [apply_number_replacements(expected[i], replacements[i]) for i in range(len(expected))]
		with open(dataset+'.corpus.5.out','r') as f:
			translations = [map(lambda x: x.strip(), l.split('|||')[0:2]) for l in f.readlines()]
			translations = map(lambda (x, y): (int(x), y), translations)
			translations = map(lambda (x,y): (x, apply_number_replacements(y, replacements[x])), translations)
		print len(inputs)
		grouped_translations = {}
		for k, g in itertools.groupby(translations, key=lambda x: x[0]):
			grouped_translations[k] = map(lambda x: x[1], list(g))
		for i in range(len(inputs)):
			postorder = [postOrderUtil.parse(x) for x in grouped_translations[i]]
			csvf.writerow([inputs[i], postOrderUtil.parse(expected[i])[1].c()] + map(lambda x: x[1].c() if x[0] else '', postorder))
