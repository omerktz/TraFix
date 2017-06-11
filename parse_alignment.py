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
		with open('data.js','w') as fjs:
			fjs.write('var src = ['+','.join(map(lambda x: '"'+x+'"', src))+'];\n')
			fjs.write('var trg = ['+','.join(map(lambda x: '"'+x+'"', target))+'];\n')
			fjs.write('var title = "'+sys.argv[1]+'-'+sys.argv[2]+'-'+sys.argv[3]+'";\n')
			fjs.write('var matrix = [')
			for s in set(src):
				if src.count(s) > 1:
					i = 0
					for j in range(len(src)):
						if src[j] == s:
							src[j] += '~'+str(i)
							i += 1
			alignment = {}
			i = 0
			l = f.readline().strip()
			while len(l) > 0:
				v = map(float, l.split(' '))
				alignment[target[i]] = dict(map(lambda i: (src[i],v[i]), range(len(src))))
				l = f.readline().strip()
				if i > 0:
					fjs.write(',')
				fjs.write('['+','.join(map(str, v))+']')
				i += 1
			fjs.write('];\n')
		print ' '.join(src)
		print ' '.join(target)
		for w in target:
			indexes = sorted(range(len(alignment[w].keys())), key=lambda k:alignment[w][src[k]], reverse=True)
			src_str = ''
			j_str = ''
			sumAlignment = 0
			i = 0
			while (sumAlignment < 0.9):
				j_str += str(indexes[i])+','
				src_str += "'"+src[indexes[i]]+"',"
				sumAlignment += alignment[w][src[indexes[i]]]
				i += 1
			print w+'\t['+src_str[:-1]+']\t['+j_str[:-1]+']'
		sys.exit(0)
	print 'Not found!'
		