import sys
import os
from subprocess import call

def compareProgs(c,out):
	if c == out:
		return 0
	with open('cbmc.c','w') as fcbmc:
		firstC = None
		varsC = set()
		c = c.strip().split(' ')
		firstC = None
		for i in range(len(c)):
			if c[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
				if not firstC:
					firstC = c[i]
				varsC.add(c[i])
				c[i] = c[i]+'_0'
		c = ' '.join(c)
		varsC.remove(firstC)
		firstOut = None
		varsOut = set()
		out = out.strip().split(' ')
		firstOut = None
		for i in range(len(out)):
			if out[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
				if not firstOut:
					firstOut = out[i]
				varsOut.add(out[i])
				out[i] = out[i]+'_1'
		out = ' '.join(out)
		varsOut.remove(firstOut)
		if len(varsC) != len(varsOut):
			return 1
		if not (varsC.issubset(varsOut) and varsOut.issubset(varsC)):
			return 1
		fcbmc.write('void main() {\n')
		fcbmc.write('\tint '+firstC+'_0,'+firstOut+'_1'+','.join(['']+map(lambda x:x+'_0',varsC)+map(lambda x:x+'_1',varsOut))+';\n')
		for v in varsC:
			fcbmc.write('\t__CPROVER_assume('+v+'_0=='+v+'_1);\n')
		fcbmc.write('\t'+c+'\n')
		fcbmc.write('\t'+out+'\n')
		fcbmc.write('\t__CPROVER_assert('+firstC+'_0=='+firstOut+'_1,"computations not equivalent");\n')
		fcbmc.write('}')
	ret = call(['cbmc','cbmc.c'])
	os.remove('cbmc.c')
	return ret

def main(f):
	nsuccess = 0
	nfail = 0
	nparse = 0
	with open(f+'.success.out','w') as fsuccess:
		with open(f+'.fail.out', 'w') as ffail:
			with open(f+'.parse.out', 'w') as fparse:
				fsuccess.write('c\tll\tout\n')
				ffail.write('c\tll\tout\n')
				fparse.write('c\tll\tout\n')
				with open(f+'.corpus.c','r') as fc:
					with open(f+'.corpus.ll', 'r') as fll:
						with open(f+'.corpus.out', 'r') as fout:
							for c in fc.readlines():
								c = c.strip()
								ll = fll.readline().strip()
								out = fout.readline().strip()
								res = compareProgs(c,out)
								if res == 0:
									fsuccess.write(c+'\t'+ll+'\t'+out+'\n')
									nsuccess += 1
								else:
									if res == 6:
										fparse.write(c + '\t' + ll + '\t' + out + '\n')
										nparse += 1
									else:
										ffail.write(c + '\t' + ll + '\t' + out + '\n')
										nfail += 1
	print str(nsuccess)+' statements translated correctly'
	print str(nparse)+' translated statements failed to parse'
	print str(nfail)+' translated statements are not equivalent'

if __name__ == "__main__":
	main(sys.argv[1])