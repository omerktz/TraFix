def filter(c,ll,out):
	return not c.count(';') in map(lambda x:x.count(';'), out)