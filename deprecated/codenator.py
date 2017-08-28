# class Program:
#     _threshold = config.getfloat('Program', 'StatementThreshold')
#
#     def __init__(self):
#         Var.clear()
#         self.statements = [Init()]
#         while (random.uniform(0, 1) <= Program._threshold) or (len(self.statements) == 1):
#             self.statements.append(Assignment())
#         self.statements.append(Return.getReturn())
#
#     def getStatements(self):
#         return self.statements[1:-1]
#
#     def __str__(self):
#         res = self.statements[-1].getType() + ' f() {\n\t'
#         res += '\t'.join(map(lambda x: str(x), self.statements)).strip()
#         res += '\n}\n'
#         return res
#
# def generatePrograms():
#     import sys
#     limited = False
#     limit = 0
#     outDir = 'out'
#     if len(sys.argv) > 1:
#         try:
#             limit = int(sys.argv[1])
#             limited = True
#         except:
#             pass
#         if len(sys.argv) > 2:
#             outDir = sys.argv[2]
#     # from cleanup import cleanup
#     # cleanup(outDir)
#     if os.path.exists(outDir):
#         import shutil
#         shutil.rmtree(outDir)
#     os.mkdir(outDir)
#     os.mkdir(os.path.join(outDir, 'block'))
#     os.mkdir(os.path.join(outDir, 'line'))
#     if limited:
#         print 'Generating ' + str(limit) + ' programs'
#     else:
#         print 'Generating programs until manually stopped (ctrl+C)'
#     print 'Saving to folder: ' + outDir
#     print ''
#     j = 1
#     vocabc = set()
#     vocabll = set()
#     first = True
#     minC = None
#     maxC = None
#     minLL = None
#     maxLL = None
#     with open(os.path.join(outDir, 'corpus.c'), 'w') as corpusc:
#         with open(os.path.join(outDir, 'corpus.ll'), 'w') as corpusll:
#             while (not limited) or (j <= limit):
#                 filename = ''.join(random.choice(string.ascii_letters + string.digits) for _ in range(10))
#                 while os.path.exists(os.path.join(outDir, filename + '.c')):
#                     filename = ''.join(random.choice(string.ascii_letters + string.digits) for _ in range(10))
#                 if limited:
#                     print '\r\t' + filename + '\t\t' + str(j) + '/' + str(limit),
#                 else:
#                     print '\r\t' + filename + '\t\t' + str(j),
#                 sys.stdout.flush()
#                 done = False
#                 while not done:
#                     try:
#                         p = Program()
#                         done = True
#                     except RuntimeError:
#                         pass
#                 with open(os.path.join(outDir, 'block', filename + '.c'), 'w') as f:
#                     f.write(str(p))
#                 os.system(
#                     'clang -S -emit-llvm -o ' + os.path.join(outDir, 'block', filename + '.ll') + ' ' + os.path.join(
#                         outDir, 'block', filename + '.c') + ' > /dev/null 2>&1')
#                 with open(os.path.join(outDir, 'block', filename + '.ll'), 'r') as f:
#                     lines = [l.strip() for l in f.readlines()]
#                 start = min(filter(lambda i: lines[i].startswith('define') and 'f()' in lines[i], range(len(lines))))
#                 end = min(filter(lambda i: lines[i] == '}' and i > start, range(len(lines))))
#                 with open(os.path.join(outDir, 'block', filename + '.ll'), 'w') as f:
#                     for i in range(start, end + 1):
#                         f.write(lines[i] + '\n')
#                 os.mkdir(os.path.join(outDir, 'line', filename))
#                 statements = p.getStatements()
#                 for i in range(len(statements)):
#                     s = statements[i]
#                     s._target._name = 'Y'
#                     k = 0
#                     for v in s.collectVars():
#                         v._name = 'X' + str(k)
#                         k += 1
#                     v = s.collectVarNames()
#                     with open(os.path.join(outDir, 'line', filename, filename + '_' + str(i) + '.c'), 'w') as f:
#                         f.write('void f() {\n')
#                         f.write('int ' + ','.join(v) + ';\n')
#                         f.write(str(s))
#                         f.write('}\n')
#                     os.system('clang -S -emit-llvm -o ' + os.path.join(outDir, 'line', filename, filename + '_' + str(
#                         i) + '.ll') + ' ' + os.path.join(outDir, 'line', filename,
#                                                          filename + '_' + str(i) + '.c') + ' > /dev/null 2>&1')
#                     with open(os.path.join(outDir, 'line', filename, filename + '_' + str(i) + '.ll'), 'r') as f:
#                         lines = [l.strip() for l in f.readlines()]
#                     start = min(
#                         filter(lambda i: lines[i].startswith('define') and 'f()' in lines[i], range(len(lines))))
#                     end = min(filter(lambda i: lines[i] == '}' and i > start, range(len(lines))))
#                     lenC = 0
#                     with open(os.path.join(outDir, 'line', filename, filename + '_' + str(i) + '.c'), 'w') as f:
#                         line = str(s)
#                         f.write(line)
#                         corpusc.write(line)
#                         vocabc.update(map(lambda x: x.strip(), line.split(' ')))
#                         lenC = line.strip().count(' ') + 1
#                         lenLL = 0
#                     with open(os.path.join(outDir, 'line', filename, filename + '_' + str(i) + '.ll'), 'w') as f:
#                         for i in range(start + 1 + len(v), end - 1):
#                             line = lines[i].strip().replace(',', ' ,')
#                             if line.endswith(', align 4'):
#                                 line = line[:-len(', align 4')].strip()
#                             f.write(line + ' ;\n')
#                             vocabll.update(map(lambda x: x.strip(), line.split(' ')))
#                             corpusll.write(line + ' ; ')
#                             lenLL += line.strip().count(' ') + 2
#                         corpusll.write('\n')
#                     if first:
#                         minC = lenC
#                         maxC = lenC
#                         minLL = lenLL
#                         maxLL = lenLL
#                         first = False
#                     else:
#                         minC = min(minC, lenC)
#                         maxC = max(maxC, lenC)
#                         minLL = min(minLL, lenLL)
#                         maxLL = max(maxLL, lenLL)
#                 j += 1
#     with open(os.path.join(outDir, 'vocab.c.json'), 'w') as f:
#         f.write('{\n')
#         i = 0
#         n = len(vocabc)
#         for w in vocabc:
#             f.write('  "' + w + '": ' + str(i))
#             i += 1
#             if i != n:
#                 f.write(', ')
#             f.write('\n')
#         f.write('}')
#     with open(os.path.join(outDir, 'vocab.ll.json'), 'w') as f:
#         f.write('{\n')
#         i = 0
#         n = len(vocabll)
#         for w in vocabll:
#             f.write('  "' + w + '": ' + str(i))
#             i += 1
#             if i != n:
#                 f.write(', ')
#             f.write('\n')
#         f.write('}')
#     print '\nDone!\n'
#     print 'input lengths (ll): ' + str(minLL) + '-' + str(maxLL)
#     print 'output lengths (ll): ' + str(minC) + '-' + str(maxC)
#
# class Return:
#     _threshold = config.getfloat('Return','Threshold')
#     @staticmethod
#     def getReturn():
#         if random.uniform(0,1) <= Return._threshold:
#             return ReturnVoid()
#         return ReturnInt()
#     def getType(self):
#         return ''
#
# class ReturnInt(Return):
#     def __str__(self):
#         return 'return ' + str(getExpr([2, 2, 1,1])) + ' ;\n'
#     def getType(self):
#         return 'int'
#
# class ReturnVoid(Return):
#     def __str__(self):
#         return ''
#     def getType(self):
#         return 'void'
#
