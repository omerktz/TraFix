import re

class Num:
    @staticmethod
    def check(token,stack):
        try:
            return re.match('^\-?[0-9]+$',token)
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.append('NUM')

class Var:
    @staticmethod
    def check(token,stack):
        try:
            return re.match('^[YX][0-9]*$',token)
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.append('VAR')

class BinOp:
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['+','-','*','/','%']) and (stack[-1] in ['NUM','VAR','EXPR']) and (stack[-2] in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.pop()
        stack.pop()
        stack.append('EXPR')

class UniOp:
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['++X','--X','X++','X--']) and (stack[-1] in ['VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.pop()
        stack.append('EXPR')

class Assignment:
    @staticmethod
    def check(token,stack):
        try:
            return (token == '=') and (stack[-1] == 'VAR') and (stack[-2] in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.pop()
        stack.pop()
        stack.append('ASSIGN')

class Cond:
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['>','>=','<','<=','==','!=']) and (stack[-1] in ['NUM','VAR','EXPR']) and (stack[-2] in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.pop()
        stack.pop()
        stack.append('COND')

class CondB:
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'COND') and (stack[-1] == 'COND')
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.pop()
        stack.append('CONDB')

class TrueB:
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'TRUE') and (stack[-1] in ['STATEMENT','STATEMENTS'])
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.pop()
        stack.append('TRUEB')

class FalseB:
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'FALSE') and (stack[-1] in ['STATEMENT','STATEMENTS'])
        except:
            return False
    @staticmethod
    def handle(stack):
        stack.pop()
        stack.append('FALSEB')

class Branch:
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'IF') and (((stack[-1] == 'TRUEB') and (stack[-2] == 'CONDB')) or ((len(stack) > 2) and (stack[-1] == 'FALSEB') and (stack[-2] == 'TRUEB') and (stack[-3] == 'CONDB')))
        except:
            return False
    @staticmethod
    def handle(stack):
        if stack[-1] == 'FALSEB':
            stack.pop()
        stack.pop()
        stack.pop()
        stack.append('BRANCH')

class Statement:
    @staticmethod
    def check(token,stack):
        try:
            return (token == ';') and (stack[-1] in ['ASSIGN','BRANCH'])
        except:
            return False
    @staticmethod
    def handle(stack):
        if len(stack) > 1:
            if stack[-2] in ['STATEMENT','STATEMENTS']:
                stack.pop()
        stack.pop()
        stack.append('STATEMENT')

postOrderTypes = [Num,Var,BinOp,UniOp,Assignment,Cond,CondB,TrueB,FalseB,Branch,Statement]
def parse(code):
    tokens = code.strip().split(' ')
    stack = []
    while len(tokens) > 0:
        matches = filter(lambda t: t.check(tokens[0],stack), postOrderTypes)
        if len(matches) != 1:
            return False
        matches[0].handle(stack)
        tokens = tokens[1:]
    return ((len(stack) == 1) and (stack[0] in ['STATEMENT','STATEMENTS']))

if __name__ == "__main__":
    print parse('23 X7 X++ == COND X7 Y = ; 4 Y = ; TRUE 10 Y = ; X1 24 * Y = ; X7 28 64 X3 / - - Y = ; FALSE IF ; ')
