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
    def handle(token,stack,simplify):
        stack.append(Num(token))
        return True
    def __init__(self, token):
        self.num = token
        self.val = int(token)
    def c(self):
        return self.num
    def __str__(self):
        return self.c()

class Var:
    type = 'VAR'
    @staticmethod
    def check(token,stack):
        try:
            return re.match('^[YX][0-9]*$',token)
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        stack.append(Var(token))
        return True
    def __init__(self, token):
        self.var = token
    def c(self):
        return self.var
    def __str__(self):
        return self.c()

class BinOp:
    type = 'EXPR'
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['+','-','*','/','%']) and (stack[-1].type in ['NUM','VAR','EXPR']) and (stack[-2].type in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        def get_rev_op(op):
            if op == '+':
                return '-'
            if op == '-':
                return '+'
            if op == '*':
                return '/'
            if op == '/':
                return '*'
            return None
        def apply_op(op, lhs, rhs):
            if op == '+':
                return lhs+rhs
            if op == '-':
                return lhs-rhs
            if op == '*':
                return lhs*rhs
            if op == '/':
                return lhs/rhs
            if op == '%':
                return lhs%rhs
            print 'Error: Invalid op!'
            import sys
            sys.exit(1)
        arg2 = stack.pop()
        arg1 = stack.pop()
        if token in ['+', '*']:
            (op, rev_op) = (token, get_rev_op(token))
        else:
            (op, rev_op) = (get_rev_op(token), token)
        if not simplify:
            if token == op:
                stack.append(BinOp(op, rev_op, ['( '+arg1.c()+' )' if arg1.type == 'EXPR' else arg1.c(), '( '+arg2.c()+' )' if arg2.type == 'EXPR' else arg2.c()], []))
            else:
                stack.append(BinOp(op, rev_op, ['( ' + arg1.c() + ' )' if arg1.type == 'EXPR' else arg1.c()], ['( ' + arg2.c() + ' )' if arg2.type == 'EXPR' else arg2.c()]))
            return True
        if isinstance(arg1, BinOp):
            if (arg1.rev_op == rev_op) and (rev_op != '%'):
                lhs = arg1.lhs[:]
                rhs = arg1.rhs[:]
            else:
                lhs = ['( '+arg1.c()+' )']
                rhs = []
        elif isinstance(arg1, Num):
            if token == '+' and arg1.val < 0:
                rhs = [Num(str(-arg1.val))]
                lhs = []
            else:
                lhs = [arg1]
                rhs = []
        elif isinstance(arg1, Var):
            lhs = [arg1.c()]
            rhs = []
        elif isinstance(arg1, UniOp):
            lhs = ['( ' + arg1.c() + ' )']
            rhs = []
        else:
            print 'Error: Unknown operand type to binary operation'
            import sys
            sys.exit(1)
        if token in ['+', '*']:
            if isinstance(arg2, BinOp):
                if arg2.rev_op == rev_op:
                    lhs += arg2.lhs[:]
                    rhs += arg2.rhs[:]
                else:
                    lhs += ['( '+arg2.c()+' )']
            elif isinstance(arg2, Num):
                lhs += [arg2]
            elif isinstance(arg2, Var):
                lhs += [arg2.c()]
            elif isinstance(arg2, UniOp):
                lhs += ['( ' + arg2.c() + ' )']
            else:
                print 'Error: Unknown operand type to binary operation'
                import sys
                sys.exit(1)
        else:
            if isinstance(arg2, BinOp):
                if (arg2.rev_op == rev_op) and (rev_op != '%'):
                    rhs += arg2.lhs[:]
                    lhs += arg2.rhs[:]
                else:
                    rhs += ['( ' + arg2.c() + ' )']
            elif isinstance(arg2, Num):
                rhs += [arg2]
            elif isinstance(arg2, Var):
                rhs += [arg2.c()]
            elif isinstance(arg2, UniOp):
                rhs += ['( ' + arg2.c() + ' )']
            else:
                print 'Error: Unknown operand type to binary operation'
                import sys
                sys.exit(1)
        lhs_nums = map(lambda y: y.val, filter(lambda x: isinstance(x, Num), lhs))
        rhs_nums = map(lambda y: y.val, filter(lambda x: isinstance(x, Num), rhs))
        lhs_rest = filter(lambda x: not isinstance(x, Num), lhs)
        rhs_rest = filter(lambda x: not isinstance(x, Num), rhs)
        if len(lhs_nums) > 1:
            lhs_nums = [reduce(lambda x, y: apply_op(op, x, y), lhs_nums[1:], lhs_nums[0])]
        if len(rhs_nums) > 1:
            rhs_nums = [reduce(lambda x, y: apply_op(op, x, y), rhs_nums[1:], rhs_nums[0])]
        if len(lhs_nums) == 1 and len(rhs_nums) == 1:
            if rev_op in ['-', '%']:
                num = apply_op(rev_op, lhs_nums[0], rhs_nums[0])
                if num < 0:
                    lhs_nums = []
                    rhs_nums = [num]
                else:
                    lhs_nums = [num]
                    rhs_nums = []
            else:
                if rhs_nums[0] != 0 and (lhs_nums[0] % rhs_nums[0]) == 0:
                    lhs_nums = [lhs_nums[0] / rhs_nums[0]]
                    rhs_nums = []
        if len(lhs_rest) > 0 or len(rhs_rest) > 0:
            stack.append(BinOp(op,rev_op,map(lambda x: Num(str(x)), lhs_nums)+lhs_rest,map(lambda x: Num(str(x)), rhs_nums)+rhs_rest))
        else:
            if len(lhs_nums) == 0:
                stack.append(Num(str(rhs_nums[0])))
            elif len(rhs_nums) == 0:
                stack.append(Num(str(lhs_nums[0])))
            else:
                num = apply_op(rev_op, lhs_nums[0], rhs_nums[0])
                stack.append(Num(str(num)))
        return True
    def __init__(self, op, rev_op, lhs, rhs):
        self.op = op
        self.rev_op = rev_op
        self.lhs = lhs
        self.rhs = rhs
    def c(self):
        res = ''
        if len(self.lhs) > 0:
            if self.op is not None:
                res += (' '+self.op+' ').join(map(str, self.lhs))
            else:
                if len(self.lhs) > 1:
                    print 'Warning: lhs of mod is larger than 1'
                res += str(self.lhs[0])
        if len(self.rhs) > 0:
            res += (' '+self.rev_op+' ') + (' '+self.rev_op+' ').join(map(str, self.rhs))
        return res
    def __str__(self):
        return self.c()

class UniOp:
    type = 'EXPR'
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['++X','--X','X++','X--']) and (stack[-1].type in ['VAR'])
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        stack.append(UniOp(token,stack.pop()))
        return True
    def __init__(self, token, op):
        self.op = token
        self.operand = op
    def c(self):
        return (self.op[:-1]+' ' if self.op in ['++X','--X'] else '')+self.operand.c()+(' '+self.op[1:] if self.op in ['X++','X--'] else '')
    def __str__(self):
        return self.c()

class Assignment:
    type = 'ASSIGN'
    @staticmethod
    def check(token,stack):
        try:
            return (token == '=') and (stack[-1].type == 'VAR') and (stack[-2].type in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        stack.append(Assignment(stack.pop(), stack.pop()))
        return True
    def __init__(self, op1, op2):
        self.tgt = op1
        self.src = op2
    def c(self):
        return self.tgt.c()+' = '+self.src.c()
    def __str__(self):
        return self.c()

class Cond:
    type = 'COND'
    @staticmethod
    def check(token,stack):
        try:
            return (token in ['>','>=','<','<=','==','!=']) and (stack[-1].type in ['NUM','VAR','EXPR']) and (stack[-2].type in ['NUM','VAR','EXPR'])
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
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
    def __str__(self):
        return self.c()

class CondB:
    type = 'CONDB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'COND') and (stack[-1].type == 'COND')
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        stack.append(CondB(stack.pop()))
        return True
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()
    def __str__(self):
        return self.c()

class TrueB:
    type = 'TRUEB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'TRUE') and (stack[-1].type in ['STATEMENT'])
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        stack.append(TrueB(stack.pop()))
        return True
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()
    def __str__(self):
        return self.c()

class FalseB:
    type = 'FALSEB'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'FALSE') and (stack[-1].type in ['STATEMENT'])
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        stack.append(FalseB(stack.pop()))
        return True
    def __init__(self, inner):
        self.inner = inner
    def c(self):
        return self.inner.c()
    def __str__(self):
        return self.c()

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
    def handle(token,stack,simplify):
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
    def __str__(self):
        return self.c()

class Loop:
    type = 'LOOP'
    @staticmethod
    def check(token,stack):
        try:
            return (token == 'WHILE') and (stack[-1].type in ['STATEMENT']) and (stack[-2].type == 'CONDB')
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        stack.append(Loop(stack.pop(), stack.pop()))
        return True
    def __init__(self, body, cond):
        self.body = body
        self.cond = cond
    def c(self):
        return 'while ( '+self.cond.c()+' ) { '+self.body.c()+'}'
    def __str__(self):
        return self.c()

class Statement:
    type = 'STATEMENT'
    @staticmethod
    def check(token,stack):
        try:
            return stack[-1].type in ['ASSIGN', 'BRANCH', 'LOOP']
        except:
            return False
    @staticmethod
    def handle(token,stack,simplify):
        current = stack.pop()
        other = None
        if len(stack) > 0:
            if stack[-1].type in ['STATEMENT'] or isinstance(stack[-1], UniOp):
                other = stack.pop()
        stack.append(Statement(current, other))
        return False
    def __init__(self,inner,other):
        self.inner = inner
        self.other = other
    def c(self):
        other_c = self.other.c() if self.other else ''
        if isinstance(self.other, UniOp):
            other_c += ' ; '
        return other_c+self.inner.c()+' ; '
    def __str__(self):
        return self.c()

postOrderTypes = [Statement,Num,Var,BinOp,UniOp,Assignment,Cond,CondB,TrueB,FalseB,Branch,Loop]
def parse(code, simplify=False):
    tokens = filter(lambda x: len(x) > 0, code.strip().split(' '))
    stack = []
    while len(tokens) > 0:
        matches = filter(lambda t: t.check(tokens[0],stack), postOrderTypes)
        if len(matches) == 0:
            if (len(stack) == 0) or (not isinstance(stack[-1], UniOp)):
                return (False, None)
            Statement.handle(None, stack, simplify)
        elif matches[0].handle(tokens[0],stack,simplify):
            tokens = tokens[1:]
    if len(stack) > 0:
        if isinstance(stack[-1], UniOp):
            Statement.handle(None, stack, simplify)
    while Statement.check(None, stack):
        Statement.handle(None,stack,simplify)
    return ((len(stack) == 1) and (stack[0].type in ['STATEMENT']), stack[0] if len(stack) > 0 else None)

if __name__ == "__main__":
    print parse('2 X0 * 15 < COND X11 14 X5 X10 * - - 3 / X5 = TRUE IF X7 X10 = X10 X7 + 1 19 X2  - + + X1 18 X2 % / * 4 / X9 =')[1].c()
