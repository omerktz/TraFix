from datetime import datetime
with open('log0','r') as f:
	lines = map(lambda x: x.strip(), f.readlines())
start = None
remaining = []
train = []
translate = []
evaluate = []
finish = None
for i in xrange(len(lines)):
	l = lines[i]
	if 'Initializing ActiveLearner' in l:
		start = datetime.strptime(l[7:26].strip(), '%Y-%m-%d %H:%M:%S')
	elif 'entries left to translate' in l:
		remaining.append(int(l[70:73]))
	elif 'Training model' in l:
		train.append(datetime.strptime(l[7:26].strip(), '%Y-%m-%d %H:%M:%S'))
	elif 'Translating dataset' in l:
		translate.append(datetime.strptime(l[7:26].strip(), '%Y-%m-%d %H:%M:%S'))
	elif 'Evaluating latest results' in l:
		evaluate.append(datetime.strptime(l[7:26].strip(), '%Y-%m-%d %H:%M:%S'))
	elif 'ActiveLearner finished' in l:
		finish = datetime.strptime(l[7:26].strip(), '%Y-%m-%d %H:%M:%S')
for i in xrange(len(remaining)):
	print str(remaining[i])
print ''
for i in xrange(len(remaining)):
	print str(translate[i]-train[i])
print ''
for i in xrange(len(remaining)):
	print str(evaluate[i]-translate[i])
print ''
print 'Duration: '+ str(finish-start)