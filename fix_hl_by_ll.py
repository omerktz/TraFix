import os
import re
import postOrderUtil as po_util
import compare_hl
import pandas as pd

numbers_pattern = '^(-)?\d+'
vars_pattern = '^X\d+'
jumps = ['jmp', 'je', 'jz', 'jne', 'jnz', 'jg', 'jnle', 'jge', 'jnl', 'jl', 'jnge', 'jle', 'jng', 'ja', 'jnbe', 'jae', 'jnb', 'jb', 'jnae', 'jbe', 'jna', 'jcxz', 'jc', 'jnc', 'jo', 'jno', 'jp', 'jpe', 'jnp', 'jpo', 'js', 'jns']
larger = ['>', '>=']
smaller = ['<', '<=']
conditions = larger + smaller
max_num = 10000000
divs = ['/', '%']

hl2ll = None
def load_compiler(f):
	global hl2ll
	if f.endswith('.py'):
		f = f[:-3]
	if f.endswith('.pyc'):
		f = f[:-4]
	hl2ll =  __import__(f)


class MockHL:
	def __init__(self, s):
		self._s = s
		self._vars = set()
		self._nums = set()
		for x in s.split(' '):
			if re.match('^N[0-9]+$',x):
				self._nums.add(x)
			elif re.match('^X[0-9]+$',x):
				self._vars.add(x)
	def __str__(self):
		return self._s
	def collect_vars(self):
		return self._vars
	def collect_nums(self):
		return self._nums

def compiler(hl):
	if not hl:
		return hl
	s = ''.join([y + ' ; ' for y in filter(lambda x: len(x) > 0, hl.split(';'))])
	return hl2ll.compiler(MockHL(s), check_success=True)


def is_var(ll_word):
    temp = re.match(vars_pattern, ll_word)
    return temp is not None and temp.group() == ll_word

def is_number(ll_word):
    temp = re.match(numbers_pattern, ll_word)
    return temp is not None and temp.group() == ll_word


def find_first_mis_match(ll_origin, ll_model):
    for i in range(ll_origin.__len__()):
        if ll_model.__len__() == i:
            return i
        if not (ll_origin[i] == ll_model[i]):
            return i
    return -1


def create_and_check_hl(list_hl, i, ll_origin, index, new_value, div=False):
    try_hl = list_hl[:]
    try_hl[i] = new_value
    try_hl = ' '.join(try_hl)
    try_ll = compiler(try_hl)
    if try_ll is None:
        return None
    first_mis_match = find_first_mis_match(ll_origin, try_ll.split(' '))
    if (first_mis_match == -1 or first_mis_match > index):
        if (div):
            if (ll_origin[first_mis_match - 1] == 'sarl'):
                return None
        return try_hl
    else:
        return None


def fix_number_in_hl(hl, ll_origin, old_num, index):
    new_num = ll_origin[index]
    is_minus_old_num = old_num[0] == '-'
    is_minus_new_num = new_num[0] == '-'
    list_hl = hl.split(' ')
    for i in range(list_hl.__len__()):
        if(list_hl[i] == old_num or (is_minus_old_num and list_hl[i] == old_num[1:])):
            try_hl = create_and_check_hl(list_hl, i, ll_origin, index, new_num)
            if try_hl is None:
                if is_minus_new_num:
                    try_hl = create_and_check_hl(list_hl, i, ll_origin, index, new_num[1:])
                    if try_hl is None and list_hl[i - 1] == '+':
                        temp = list_hl[:]
                        temp[i - 1] = '-'
                        try_hl = create_and_check_hl(temp, i, ll_origin, index, new_num[1:])
                elif is_minus_old_num:
                    try_hl = create_and_check_hl(list_hl, i, ll_origin, index, '-' + new_num)

            if try_hl is not None:
                return try_hl

    return None


def fix_var_in_hl(hl, ll_origin, old_var, index):
    new_var = ll_origin[index]
    list_hl = hl.split(' ')
    for i in range(list_hl.__len__()):
        if (list_hl[i] == old_var):
            try_hl = create_and_check_hl(list_hl, i, ll_origin, index, new_var)
            if try_hl is not None:
                return try_hl

    return None


def fix_cond_in_hl(hl, ll_origin, index):
    list_hl = hl.split(' ')
    for i in range(list_hl.__len__()):
        if (list_hl[i] in  conditions):
            for cond in conditions:
                if not (cond == list_hl[i]):
                    try_hl = create_and_check_hl(list_hl, i, ll_origin, index, cond)
                    if try_hl is not None:
                        return try_hl

    return None


def fix_div_in_hl(hl, ll_origin, index):
    list_hl = hl.split(' ')
    for i in range(list_hl.__len__()):
        if list_hl[i] in divs:
            if is_number(list_hl[i+1]):
                num = int(list_hl[i+1])
                for j in range(num - 10, num + 10):
                    try_hl = create_and_check_hl(list_hl, i + 1, ll_origin, index, str(j), div=True)
                    if try_hl is not None:
                        return try_hl

    return None

def is_close_numbers(num1, num2):
    return abs(num1 - num2) == 1

def is_devide_num_prob(num1, num2):
    return abs(num1) > max_num and abs(num2) > max_num

def fix_hl(hl, ll_origin, ll_model, combine=False):
    # print hl
    # print ll_origin
    # print ll_model

    load_compiler('x86Util.py')
    if (combine):
        origin_hl = hl
        hl_tree = compare_hl.from_list_to_tree(hl.split(' '))
        hl = from_tree_to_code(hl_tree)
        if hl == origin_hl or hl == origin_hl[:-2]:
            return None
    ll_origin_list = ll_origin.split(' ')
    ll_model_list = ll_model.split(' ')
    close_numbers = False
    # if not (ll_origin.__len__() == ll_model.__len__()):
    #     return None
    for i in range(ll_origin_list.__len__()):
        if ll_model_list.__len__() == i:
            return None
        if (ll_origin_list[i] == ll_model_list[i]):
            continue
        # print 'll_origin[i]: ' + ll_origin_list[i]
        # print 'll_model[i]: ' + ll_model_list[i]
        if(is_number(ll_origin_list[i]) and is_number(ll_model_list[i])):
            close_numbers = is_close_numbers(int(ll_origin_list[i]), int(ll_model_list[i]))
            if(is_devide_num_prob(int(ll_origin_list[i]), int(ll_model_list[i]))):
                fixed_hl = fix_div_in_hl(hl, ll_origin_list, i)
            else:
                fixed_hl = fix_number_in_hl(hl, ll_origin_list, ll_model_list[i], i)
        elif (is_var(ll_origin_list[i]) and is_var(ll_model_list[i])):
            fixed_hl = fix_var_in_hl(hl, ll_origin_list, ll_model_list[i], i)
        elif (ll_origin_list[i] in jumps and ll_model_list[i] in jumps):
            fixed_hl = fix_cond_in_hl(hl, ll_origin_list, i)
        else:
            return None

        if fixed_hl is None:
            if(close_numbers):
                close_numbers = False
            else:
                return None
        else:
            hl = fixed_hl
            # print hl
            ll_model_list = compiler(hl).split(' ')

    # print hl
    if (compiler(hl) == ll_origin):
        return hl
    return None


def from_tree_to_code(hl_tree):
    return ' ; '.join(map(lambda x: x.__str__(), hl_tree)).replace('  ', ' ').replace('} }', '} ; }')

def check_successes(exp_name):
    problem = 0
    df =pd.read_csv(os.path.join(exp_name, 'successes.csv'))
    for index, row in df.iterrows():
        is_right = row['hl'] == compiler(row['out'])
        if not is_right:
            problem += 1
            print 'success does not compile to result: '
            print
            print po_util.parse(index)[1].c()
            print
            print row['out']
            print
            print compiler(po_util.parse(index)[1].c())
            print
            print compiler(row['out'])
            print
            print index

    if problem == 0:
        print 'successes are legit'


if __name__ == "__main__":
    load_compiler('x86Util.py')
    # exp_name = os.path.join('/mnt/c/python_technion/Codenator', 'tf_44_to_100')
    # check_successes(exp_name)
    hl = 'X8 X14 2 8 / * X2 = X5 7 5 X12 * % 0 6 | 3 9 X6 X9 / - - - X11 8 0 X7 / X1 - + == COND X10 1 4 % 0 4 - 9 4 + X2 3 7 X2 * + - X0 = X4 X1 X7 1 2 - 0 2 % / 5 6 + * X0 = X10 X14 = WHILE X6 ++X X2 - X5 --X + X4 --X < COND 4 | 5 6 X13 --X * * 7 9 / X4 ++X % X8 = WHILE X14 6 8 + X10 8 5 X3 5 1 | 9 1 X0 * / % - + >= COND X5 X9 != COND X13 X6 X4 + 9 3 / == COND 2 1 X3 = WHILE 3 1 X3 % X13 / 8 4 X6 + != COND X13 X7 / X5 = TRUE 9 2 X1 X7 --X X12 6 1 X13 % - % - * X13 = FALSE IF 0 9 X4 X14 / % X6 = WHILE TRUE IF'
    print compiler(po_util.parse(hl)[1].c())
    print (po_util.parse(hl)[1].c())
    exit(0)
    # hl = 'while ( ( -- X0 - ( 66 % X6 ) ) == ( ( X5 -- * ( X0 / X5 ) ) * ( ( ( 30 + ( 35 / X12 ) ) + 28 ) + X12 ) ) ) { X3 = ( ( X14 / X8 ) % 33 ) + ( ( X10 / X1 ) / ( ( X10 - 27 ) + ( X3 % X10 ) ) ) ; X2 = X0 ; if ( ( ( X4 * X1 ) + 52 ) != ( ( X14 / ( 72 % -- X3 ) ) % ( ( 51 + X5 ) / X10 ++ ) ) ) { if ( ( ( 35 / X3 ) + 34 ) <= ( ( ( 64 * -- X14 ) - ( ( ( -- X10 + 27 ) - X12 ) - 60 ) ) / ( X1 / ( 60 - X13 ) ) ) ) { X7 = ( ( X9 % 12 ) % ( 39 % X6 ) ) / X1 ; } ; } ; } ; X6 = X10 / ( X1 % ( 12 * X7 ) ) ; X14 = 53 ; X5 = ( 21 / X14 ) * ( X8 / ( ( 91 * X14 ) - 40 ) ) ;'
    # ll = 'movl 8447 , X14 ; movl X12 , %eax ; movl 9686 , %edx ; movl %edx , %ecx ; subl %eax , %ecx ; movl 1981325155 , %edx ; movl %ecx , %eax ; imull %edx ; sarl 12 , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl %edx , %eax ; imull 8879 , %eax , %eax ; subl %eax , %ecx ; movl %ecx , %eax ; movl X11 , %edx ; subl 1 , %edx ; movl %edx , X11 ; movl X11 , %edx ; cmpl %edx , %eax ; jl .L0 ; movl X1 , %edx ; movl X9 , %eax ; cmpl %eax , %edx ; jl .L0 ; movl X13 , %eax ; leal 9263 ( %eax ) , %edx ; movl X5 , %eax ; subl %eax , %edx ; movl X2 , %eax ; addl %edx , %eax ; movl %eax , X13 ; .L0 : ; movl X6 , %eax ; movl %eax , X13 ; movl X7 , %eax ; addl 4535 , %eax ; movl X1 , %edx ; movl 3440 , %ecx ; subl %edx , %ecx ; movl %ecx , %esi ; idivl %esi ; movl %eax , %ebx ; movl X3 , %eax ; movl 9021 , %edx ; subl %eax , %edx ; movl X4 , %eax ; movl %edx , %ecx ; imull %eax , %ecx ; movl X12 , %eax ; imull 7582 , %eax , %eax ; movl X6 , %esi ; idivl %esi ; leal ( %ecx ,%eax ) , %edx ; movl X4 , %eax ; imull %edx , %eax ; cmpl %eax , %ebx ; jg .L1 ; movl X3 , %eax ; leal -1 ( %eax ) , %edx ; movl %edx , X3 ; movl %eax , X9 ; jmp .L2 ; .L1 : ; movl X14 , %eax ; movl %eax , X11 ; .L2 : ; movl X1 , %eax ; imull 5485 , %eax , %edx ; movl X4 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X10 ;'
    # comp = compiler(hl)
    # ll_list = ll.split(' ')
    # comp_list = comp.split(' ')
    # for i in range(ll_list.__len__()):
    #     if not comp_list[i] == ll_list[i]:
    #         print i
    #         print comp_list[i]
    #         print ll_list[i]
    # print comp
    # print comp == ll
    # exit(0)
    hl = 'X0 --X 6 6 X6 % - X5 X-- X0 X5 / * X12 5 5 | 3 5 X12 / + + * == COND X14 X8 / 3 3 % X10 X1 / X10 2 2 + X3 X10 % + / + X3 = X0 X2 = 2 5 X4 X1 * + X14 7 7 X3 --X % / 5 5 X5 + X10 X++ / % != COND 3 5 X3 / 3 4 + X14 --X 6 4 * 2 4 X10 --X + X12 - 6 - - X1 6 X13 - / / <= COND X9 1 2 % 3 3 X6 % % X1 / X7 = TRUE IF TRUE IF WHILE X10 X1 1 2 X7 * % / X6 = 5 5 X14 = 2 0 X14 / X8 1 5 | 9 1 X14 * - / * X5 ='
    hl = po_util.parse(hl)[1].c().strip()
    # print hl
    # hl_tree = compare_hl.from_list_to_tree(hl.split(' '))
    # hl = from_tree_to_code(hl_tree)
    # hl = 'while ( ( X9 / ( ( 88 * X3 ) - X1 ) ) <= ( ( ( X10 % 95 ) - X5 ) - X7 ) ) { while ( X3 ++ < ( ( ( ( 69 / X9 ) % X13 ) + 33 ) % X6 ) ) { if ( ( ( ( X0 + 44 ) / ( 78 % X9 ) ) % 80 ) <= ( ( ( X7 / X13 ) % 55 ) - ( ( 24 - X2 ) % X8 ) ) ) { while ( X3 ++ < ( ( ( ( 39 / X9 ) % X13 ) + 33 ) % X6 ) ) { X3 = 77 / X3 ; } ; } else { X1 = ( X11 / 55 ) + X7 ; } ; } ; } ;'
    ll_origin = 'jmp .L1 ; .L0 : ; movl X14 , %eax ; movl X8 , %edi ; idivl %edi ; movl %eax , %ebx ; movl 1041204193 , %edx ; movl %ebx , %eax ; imull %edx ; sarl 3 , %edx ; movl %ebx , %eax ; sarl 31 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl %ecx , %eax ; sall 5 , %eax ; addl %ecx , %eax ; subl %eax , %ebx ; movl %ebx , %ecx ; movl X10 , %eax ; movl X1 , %esi ; idivl %esi ; movl %eax , %edi ; movl X10 , %eax ; leal -27 ( %eax ) , %esi ; movl X3 , %eax ; movl X10 , %ebx ; idivl %ebx ; movl %edx , %eax ; addl %eax , %esi ; movl %edi , %eax ; idivl %esi ; addl %ecx , %eax ; movl %eax , X3 ; movl X0 , %eax ; movl %eax , X2 ; movl X4 , %edx ; movl X1 , %eax ; imull %edx , %eax ; leal 52 ( %eax ) , %esi ; movl X14 , %ecx ; movl X3 , %eax ; subl 1 , %eax ; movl %eax , X3 ; movl X3 , %ebx ; movl 72 , %eax ; idivl %ebx ; movl %edx , %edi ; movl %ecx , %eax ; idivl %edi ; movl %eax , %ebx ; movl X5 , %eax ; leal 51 ( %eax ) , %ecx ; movl X10 , %edi ; leal 1 ( %edi ) , %eax ; movl %eax , X10 ; movl %ecx , %eax ; idivl %edi ; movl %eax , %ecx ; movl %ebx , %eax ; idivl %ecx ; movl %edx , %eax ; cmpl %eax , %esi ; je .L1 ; movl X3 , %edi ; movl 35 , %eax ; idivl %edi ; leal 34 ( %eax ) , %ebx ; movl X14 , %eax ; subl 1 , %eax ; movl %eax , X14 ; movl X14 , %eax ; sall 6 , %eax ; movl %eax , %edx ; movl X10 , %eax ; subl 1 , %eax ; movl %eax , X10 ; movl X10 , %eax ; leal 27 ( %eax ) , %ecx ; movl X12 , %eax ; subl %eax , %ecx ; movl %ecx , %eax ; subl 60 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl X1 , %eax ; movl X13 , %edx ; movl 60 , %esi ; subl %edx , %esi ; idivl %esi ; movl %eax , %edi ; movl %ecx , %eax ; idivl %edi ; cmpl %eax , %ebx ; jg .L1 ; movl X9 , %ebx ; movl 715827883 , %edx ; movl %ebx , %eax ; imull %edx ; sarl 1 , %edx ; movl %ebx , %eax ; sarl 31 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl %ecx , %eax ; addl %eax , %eax ; addl %ecx , %eax ; sall 2 , %eax ; subl %eax , %ebx ; movl %ebx , %ecx ; movl X6 , %ebx ; movl 39 , %eax ; idivl %ebx ; movl %edx , %ebx ; movl %ecx , %eax ; idivl %ebx ; movl %edx , %eax ; movl X1 , %esi ; idivl %esi ; movl %eax , X7 ; .L1 : ; movl X0 , %eax ; subl 1 , %eax ; movl %eax , X0 ; movl X0 , %ecx ; movl X6 , %ebx ; movl 66 , %eax ; idivl %ebx ; movl %edx , %eax ; movl %ecx , %ebx ; subl %eax , %ebx ; movl X5 , %ecx ; leal -1 ( %ecx ) , %eax ; movl %eax , X5 ; movl X0 , %eax ; movl X5 , %edi ; idivl %edi ; imull %eax , %ecx ; movl X12 , %edi ; movl 35 , %eax ; idivl %edi ; leal 58 ( %eax ) , %edx ; movl X12 , %eax ; addl %edx , %eax ; imull %ecx , %eax ; cmpl %eax , %ebx ; je .L0 ; movl X10 , %ecx ; movl X1 , %ebx ; movl X7 , %edx ; movl %edx , %eax ; addl %eax , %eax ; addl %edx , %eax ; sall 2 , %eax ; movl %eax , %esi ; movl %ebx , %eax ; idivl %esi ; movl %edx , %edi ; movl %ecx , %eax ; idivl %edi ; movl %eax , X6 ; movl 53 , X14 ; movl X14 , %esi ; movl 21 , %eax ; idivl %esi ; movl %eax , %ecx ; movl X8 , %eax ; movl X14 , %edx ; imull 91 , %edx , %edx ; leal -40 ( %edx ) , %edi ; idivl %edi ; imull %ecx , %eax ; movl %eax , X5 ;'
    ll_model = 'jmp .L1 ; .L0 : ; movl X14 , %eax ; movl X8 , %edi ; idivl %edi ; movl %eax , %ebx ; movl 1041204193 , %edx ; movl %ebx , %eax ; imull %edx ; sarl 3 , %edx ; movl %ebx , %eax ; sarl 31 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl %ecx , %eax ; sall 5 , %eax ; addl %ecx , %eax ; subl %eax , %ebx ; movl %ebx , %ecx ; movl X10 , %eax ; movl X1 , %esi ; idivl %esi ; movl %eax , %edi ; movl X10 , %eax ; leal 22 ( %eax ) , %esi ; movl X3 , %eax ; movl X10 , %ebx ; idivl %ebx ; movl %edx , %eax ; addl %eax , %esi ; movl %edi , %eax ; idivl %esi ; addl %ecx , %eax ; movl %eax , X3 ; movl X0 , %eax ; movl %eax , X2 ; movl X4 , %edx ; movl X1 , %eax ; imull %edx , %eax ; leal 25 ( %eax ) , %esi ; movl X14 , %ecx ; movl X3 , %eax ; subl 1 , %eax ; movl %eax , X3 ; movl X3 , %ebx ; movl 77 , %eax ; idivl %ebx ; movl %edx , %edi ; movl %ecx , %eax ; idivl %edi ; movl %eax , %ebx ; movl X5 , %eax ; leal 55 ( %eax ) , %ecx ; movl X10 , %edi ; leal 1 ( %edi ) , %eax ; movl %eax , X10 ; movl %ecx , %eax ; idivl %edi ; movl %eax , %ecx ; movl %ebx , %eax ; idivl %ecx ; movl %edx , %eax ; cmpl %eax , %esi ; je .L1 ; movl X3 , %edi ; movl 35 , %eax ; idivl %edi ; leal 34 ( %eax ) , %ebx ; movl X14 , %eax ; subl 1 , %eax ; movl %eax , X14 ; movl X14 , %eax ; sall 6 , %eax ; movl %eax , %edx ; movl X10 , %eax ; subl 1 , %eax ; movl %eax , X10 ; movl X10 , %eax ; leal 24 ( %eax ) , %ecx ; movl X12 , %eax ; subl %eax , %ecx ; movl %ecx , %eax ; subl 6 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl X1 , %eax ; movl X13 , %edx ; movl 6 , %esi ; subl %edx , %esi ; idivl %esi ; movl %eax , %edi ; movl %ecx , %eax ; idivl %edi ; cmpl %eax , %ebx ; jg .L1 ; movl X9 , %ebx ; movl 715827883 , %edx ; movl %ebx , %eax ; imull %edx ; sarl 1 , %edx ; movl %ebx , %eax ; sarl 31 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl %ecx , %eax ; addl %eax , %eax ; addl %ecx , %eax ; sall 2 , %eax ; subl %eax , %ebx ; movl %ebx , %ecx ; movl X6 , %ebx ; movl 33 , %eax ; idivl %ebx ; movl %edx , %ebx ; movl %ecx , %eax ; idivl %ebx ; movl %edx , %eax ; movl X1 , %esi ; idivl %esi ; movl %eax , X7 ; .L1 : ; movl X0 , %eax ; subl 1 , %eax ; movl %eax , X0 ; movl X0 , %ecx ; movl X6 , %ebx ; movl 66 , %eax ; idivl %ebx ; movl %edx , %eax ; movl %ecx , %ebx ; subl %eax , %ebx ; movl X5 , %ecx ; leal -1 ( %ecx ) , %eax ; movl %eax , X5 ; movl X0 , %eax ; movl X5 , %edi ; idivl %edi ; imull %eax , %ecx ; movl X12 , %edi ; movl 35 , %eax ; idivl %edi ; leal 55 ( %eax ) , %edx ; movl X12 , %eax ; addl %edx , %eax ; imull %ecx , %eax ; cmpl %eax , %ebx ; je .L0 ; movl X10 , %ecx ; movl X1 , %ebx ; movl X7 , %edx ; movl %edx , %eax ; addl %eax , %eax ; addl %edx , %eax ; sall 2 , %eax ; movl %eax , %esi ; movl %ebx , %eax ; idivl %esi ; movl %edx , %edi ; movl %ecx , %eax ; idivl %edi ; movl %eax , X6 ; movl 55 , X14 ; movl X14 , %esi ; movl 20 , %eax ; idivl %esi ; movl %eax , %ecx ; movl X8 , %eax ; movl X14 , %edx ; imull -91 , %edx , %edx ; leal 15 ( %edx ) , %edi ; idivl %edi ; imull %ecx , %eax ; movl %eax , X5 ;'
    fixed_hl = fix_hl(hl, ll_origin, ll_model, True)
    # print hl
    print fixed_hl
    print compiler(fixed_hl) == ll_origin
