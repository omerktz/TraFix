import re

class Num:
    type = 'NUM'
    @staticmethod
    def check(token,stack):
        try:
            return re.match('^\-?[0-9]+$',token) or re.match('^N[0-9]+$',token)
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(Num(token))
        return True
    def __init__(self, token):
        self.num = token
    def c(self):
        return self.num

class Var:
    type = 'VAR'
    @staticmethod
    def check(token,stack):
        try:
            return re.match('^[YX][0-9]*$',token)
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(Var(token))
        return True
    def __init__(self, token):
        self.var = token
    def c(self):
        return self.var

class BinOp:
    type = 'EXPR'
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['+','-','*','/','%']) and (stack[-1].type in ['NUM','VAR','EXPR']) and (stack[-2].type in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(BinOp(token,stack.pop(),stack.pop()))
        return True
    def __init__(self, token, op2, op1):
        self.op = token
        self.operand1 = op1
        self.operand2 = op2
    def c(self):
        res = ''
        if isinstance(self.operand1, BinOp):
            res += '( '+self.operand1.c()+' )'
        else:
            res += self.operand1.c()
        res += ' '+self.op+' '
        if isinstance(self.operand2, BinOp):
            res += '( '+self.operand2.c()+' )'
        else:
            res += self.operand2.c()
        return res

class UniOp:
    type = 'EXPR'
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['++X','--X','X++','X--']) and (stack[-1].type in ['VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(UniOp(token,stack.pop()))
        return True
    def __init__(self, token, op):
        self.op = token
        self.operand = op
    def c(self):
        return (self.op[:-1]+' ' if self.op in ['++X','--X'] else '')+self.operand.c()+(' '+self.op[1:] if self.op in ['X++','X--'] else '')

class Assignment:
    type = 'ASSIGN'
    @staticmethod
    def check(token,stack):
        try:
            return (token == '=') and (stack[-1].type == 'VAR') and (stack[-2].type in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(Assignment(stack.pop(), stack.pop()))
        return True
    def __init__(self, op1, op2):
        self.tgt = op1
        self.src = op2
    def c(self):
        return self.tgt.c()+' = '+self.src.c()

class Cond:
    type = 'COND'
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['>','>=','<','<=','==','!=']) and (stack[-1].type in ['NUM','VAR','EXPR']) and (stack[-2].type in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(Cond(token, stack.pop(), stack.pop()))
        return True
    def __init__(self, token, op2, op1):
        self.op = token
        self.operand1 = op1
        self.operand2 = op2
    def c(self):
        res = ''
        if isinstance(self.operand1, BinOp):
            res += '( '+self.operand1.c()+' )'
        else:
            res += self.operand1.c()
        res += ' '+self.op+' '
        if isinstance(self.operand2, BinOp):
            res += '( '+self.operand2.c()+' )'
        else:
            res += self.operand2.c()
        return res

class CondB:
    type = 'CONDB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'COND') and (stack[-1].type == 'COND')
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(CondB(stack.pop()))
        return True
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()

class TrueB:
    type = 'TRUEB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'TRUE') and (stack[-1].type in ['STATEMENT'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(TrueB(stack.pop()))
        return True
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()

class FalseB:
    type = 'FALSEB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'FALSE') and (stack[-1].type in ['STATEMENT'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(FalseB(stack.pop()))
        return True
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()

class Branch:
    type = 'BRANCH'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'IF') and (((stack[-1].type == 'TRUEB') and (stack[-2].type == 'CONDB')) or
                                        ((len(stack) > 2) and (stack[-1].type == 'FALSEB') and (stack[-2].type == 'TRUEB') and (stack[-3].type == 'CONDB')))
        except:
            return False
    @staticmethod
    def handle(token,stack):
        false = None
        if stack[-1].type == 'FALSEB':
            false = stack.pop()
        stack.append(Branch(stack.pop(), stack.pop(), false))
        return True
    def __init__(self, true, cond, false):
        self.true = true
        self.cond = cond
        self.false = false
    def c(self):
        return 'if ( '+self.cond.c()+' ) { '+self.true.c()+('} else { '+self.false.c() if self.false else '')+'}'

class Loop:
    type = 'LOOP'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'WHILE') and (stack[-1].type in ['STATEMENT']) and (stack[-2].type == 'CONDB')
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(Loop(stack.pop(), stack.pop()))
        return True
    def __init__(self, body, cond):
        self.body = body
        self.cond = cond
    def c(self):
        return 'while ( '+self.cond.c()+' ) { '+self.body.c()+'}'

class Statement:
    type = 'STATEMENT'
    @staticmethod
    def check(token,stack):
        try:
            return stack[-1].type in ['ASSIGN', 'BRANCH', 'LOOP']
        except:
            return False
    @staticmethod
    def handle(token,stack):
        current = stack.pop()
        other = None
        if len(stack) > 0:
            if stack[-1].type in ['STATEMENT']:
                other = stack.pop()
        stack.append(Statement(current, other))
        return False
    def __init__(self,inner,other):
        self.inner = inner
        self.other = other
    def c(self):
        return (self.other.c() if self.other else '')+self.inner.c()+' ; '

postOrderTypes = [Statement,Num,Var,BinOp,UniOp,Assignment,Cond,CondB,TrueB,FalseB,Branch,Loop]
def parse(code):
    tokens = filter(lambda x: len(x) > 0, code.strip().split(' '))
    stack = []
    while len(tokens) > 0:
        matches = filter(lambda t: t.check(tokens[0],stack), postOrderTypes)
        if len(matches) == 0:
            return (False, None)
        if matches[0].handle(tokens[0],stack):
            tokens = tokens[1:]
    while Statement.check(None, stack):
        Statement.handle(None,stack)
    return ((len(stack) == 1) and (stack[0].type in ['STATEMENT']), stack[0])

if __name__ == "__main__":
    print parse('N2 X0 * N15 < COND X5 X11 N14 X5 X10 * - - N3 / = TRUE IF X10 X7 = X9 X10 X7 + N0 N19 X2  - + + X1 N18 X2 % / * N4 / =')[1].c()
