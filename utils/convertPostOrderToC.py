import re

class Num:
    type = 'NUM'
    @staticmethod
    def check(token,stack):
        try:
            return re.match('^\-?[0-9]+$',token)
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(Num(token))
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
    def __init__(self, token, op2, op1):
        self.op = token
        self.operand1 = op1
        self.operand2 = op2
    def c(self):
        operand1 = self.operand1.c()
        if self.operand1.type == 'EXPR':
            operand1 = '( '+operand1+' )'
        operand2 = self.operand2.c()
        if self.operand2.type == 'EXPR':
            operand2 = '( '+operand2+' )'
        return operand1+' '+self.op+' '+operand2

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
            return (token == '=') and (stack[-2].type == 'VAR') and (stack[-1].type in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(Assignment(stack.pop(), stack.pop()))
    def __init__(self, op2, op1):
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
    def __init__(self, token, op2, op1):
        self.op = token
        self.operand1 = op1
        self.operand2 = op2
    def c(self):
        return self.operand1.c() + ' ' + self.op + ' ' + self.operand2.c()

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
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()

class TrueB:
    type = 'TRUEB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'TRUE') and (stack[-1].type in ['STATEMENT','STATEMENTS'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(TrueB(stack.pop()))
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()

class FalseB:
    type = 'FALSEB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'FALSE') and (stack[-1].type in ['STATEMENT','STATEMENTS'])
        except:
            return False
    @staticmethod
    def handle(token,stack):
        stack.append(FalseB(stack.pop()))
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
    def __init__(self, true, cond, false):
        self.true = true
        self.cond = cond
        self.false = false
    def c(self):
        return 'if ( '+self.cond.c()+' ) { '+self.true.c()+('} else { '+self.false.c() if self.false else '')+'}'

class Statement:
    type = 'STATEMENT'
    @staticmethod
    def check(token,stack):
        try:
            return (token == ';') and (stack[-1].type in ['ASSIGN','BRANCH'])
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
    def __init__(self,inner,other):
        self.inner = inner
        self.other = other
    def c(self):
        return (self.other.c() if self.other else '')+self.inner.c()+' ; '

postOrderTypes = [Num,Var,BinOp,UniOp,Assignment,Cond,CondB,TrueB,FalseB,Branch,Statement]
def parse(code):
    tokens = code.strip().split(' ')
    stack = []
    while len(tokens) > 0:
        matches = filter(lambda t: t.check(tokens[0],stack), postOrderTypes)
        if len(matches) != 1:
            return (False, None)
        matches[0].handle(tokens[0],stack)
        tokens = tokens[1:]
    return ((len(stack) == 1) and (stack[0].type in ['STATEMENT']), stack[0])

if __name__ == "__main__":
    print parse('23 X7 X++ == COND X7 Y = ; 4 Y = ; TRUE 10 Y = ; X1 24 * Y = ; X7 28 64 X3 / - - Y = ; FALSE IF ; ')[1].c()
