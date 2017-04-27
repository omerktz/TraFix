import sys
import os
from subprocess import call

def compareProgs(p):
	with open(p+'.cbmc.c','w') as fcbmc:
		firstC = None
		varsC = set()
		with open(p+'.c','r') as fc:
			c = [l.strip().split(' ') for l in fc.readlines()]
			for l in c:
				firstC = None
				for i in range(len(l)):
					if l[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
						if not firstC:
							firstC = l[i]
						varsC.add(l[i])
						l[i] = l[i]+'_0'
			c = map(lambda l:' '.join(l),c)
			c = '\n'.join(c)
		varsC.remove(firstC)
		firstOut = None
		varsOut = set()
		with open(p+'.out','r') as fout:
			out = [l.strip().split(' ') for l in fout.readlines()]
			for l in out:
				firstOut = None
				for i in range(len(l)):
					if l[i][0] not in ['0','1','2','3','4','5','6','7','8','9','+','-','*','/','%','(',')','=',';']:
						if not firstOut:
							firstOut = l[i]
						varsOut.add(l[i])
						l[i] = l[i]+'_1'
			out = map(lambda l:' '.join(l),out)
			out = '\n'.join(out)
		varsOut.remove(firstOut)
		if len(varsC) != len(varsOut):
			return False
		if not (varsC.issubset(varsOut) and varsOut.issubset(varsC)):
			return False
		fcbmc.write('void main() {\n')
		fcbmc.write('int '+firstC+'_0,'+firstOut+'_1'+','.join(['']+map(lambda x:x+'_0',varsC)+map(lambda x:x+'_1',varsOut))+';\n')
		for v in varsC:
			fcbmc.write('assume('+v+'_0=='+v+'_1);\n')
		fcbmc.write(c+'\n')
		fcbmc.write(out+'\n')
		fcbmc.write('assert('+firstC+'_0=='+firstOut+'_1);\n')
		fcbmc.write('}')
	ret = call(['cbmc',p+'.cbmc.c'])
	return ret == 0

def main(dir):
	with open(os.path.join(dir,'success.out'),'w') as fsuccess:
		with open(os.path.join(dir,'fail.out'),'w') as ffail:
			for d in os.listdir(os.path.join(dir,'line')):
				x = os.path.join(dir,'line',d)
				fs = set([f[:f.find('.')] for f in os.listdir(x)])
				results = map(lambda f:(f,compareProgs(os.path.join(x,f))),fs)
				for r in results:
					if r[1]:
						fsuccess.write(r[0]+'\n')
					else:
						ffail.write(r[0]+'\n')

if __name__ == "__main__":
	main(sys.argv[1])