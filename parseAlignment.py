import sys
if len(sys.argv) != 4:
	print 'Usage: python '+sys.argv[0]+' <alignment file> <sentence #> <translation #>'
	sys.exit(1)

f = sys.argv[1]
s = int(sys.argv[2])
t = int(sys.argv[3])

with open(f,'r') as f:
	l = f.readline().strip()
	count = 0
	while len(l) > 0:
		p = map(lambda x: x.strip(), l.split('|||'))
		x = int(p[0])
		if (x < s) or ((x == s) and (count < t)):
			if x == s:
				count += 1
			l = f.readline().strip()
			while len(l) > 0:
				l = f.readline().strip()
			l = f.readline().strip()
			continue
		if (x > s) or (count > t):
			print 'Not found!'
			sys.exit(0)
		src = (p[3]+' $').replace('  ',' ').split(' ')
		target = (p[1]+' $').replace('  ',' ').split(' ')
		alignment = {}
		i = 0
		l = f.readline().strip()
		while len(l) > 0:
			v = map(float, l.split(' '))
			alignment[target[i]] = dict(map(lambda i: (src[i],v[i]), range(len(src))))
			l = f.readline().strip()
			i += 1
		for w in target:
			j = max(range(len(alignment[w].keys())), key=lambda k:alignment[w][src[k]])
			print w+'\t'+src[j]+'\t('+str(j)+')'
		sys.exit(0)
	print 'Not found!'
		