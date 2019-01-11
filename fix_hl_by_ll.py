import re
import postOrderUtil as po_util
import compare_hl

numbers_pattern = '^(-|N)?\d+'
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
            if try_hl is None and is_minus_new_num:
                try_hl = create_and_check_hl(list_hl, i, ll_origin, index, new_num[1:])
                if try_hl is None and list_hl[i - 1] == '+':
                    temp = list_hl[:]
                    temp[i - 1] = '-'
                    try_hl = create_and_check_hl(temp, i, ll_origin, index, new_num[1:])

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


def fix_div_in_hl(hl, ll_origin, param, index):
    list_hl = hl.split(' ')
    for i in range(list_hl.__len__()):
        if list_hl[i] in divs:
            if is_number(list_hl[i+1]) and (list_hl[i+1].isdigit() or list_hl[i+1][1:].isdigit()):
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

def fix_hl(hl, ll_origin, ll_model):
    # print hl
    # print ll_origin
    # print ll_model

    load_compiler('x86Util.py')
    # hl_tree = compare_hl.from_list_to_tree(hl.split(' '))
    # hl = from_tree_to_code(hl_tree)
    ll_origin = ll_origin.split(' ')
    ll_model = ll_model.split(' ')
    close_numbers = False
    # if not (ll_origin.__len__() == ll_model.__len__()):
    #     return None
    for i in range(ll_origin.__len__()):
        if (ll_origin[i] == ll_model[i]):
            continue
        # print 'll_origin[i]: ' + ll_origin[i]
        # print 'll_model[i]: ' + ll_model[i]
        if(is_number(ll_origin[i]) and is_number(ll_model[i])):
            close_numbers = is_close_numbers(int(ll_origin[i]), int(ll_model[i]))
            if(is_devide_num_prob(int(ll_origin[i]), int(ll_model[i]))):
                fixed_hl = fix_div_in_hl(hl, ll_origin, ll_model[i], i)
            else:
                fixed_hl = fix_number_in_hl(hl, ll_origin, ll_model[i], i)
        elif (is_var(ll_origin[i]) and is_var(ll_model[i])):
            fixed_hl = fix_var_in_hl(hl, ll_origin, ll_model[i], i)
        elif (ll_origin[i] in jumps and ll_model[i] in jumps):
            fixed_hl = fix_cond_in_hl(hl, ll_origin, i)
        else:
            return None

        if fixed_hl is None:
            if(close_numbers):
                close_numbers = False
            else:
                return None
        else:
            hl = fixed_hl
            ll_model = compiler(hl).split(' ')

        # print hl
    return hl


def from_tree_to_code(hl_tree):
    return ' ; '.join(map(lambda x: x.__str__(), hl_tree)).replace('  ', ' ').replace('} }', '} ; }')


if __name__ == "__main__":
    load_compiler('x86Util.py')
    # hl = 'X8 7 4 * 6 0 X8 * * X8 == COND X9 9 2 | 8 6 X10 X3 X4 + - - % X1 % % X14 = X0 X4 = TRUE IF 3 3 X6 / X12 1 1 X2 / % X7 + X6 * % X11 = 4 4 X0 / 5 8 X2 X9 + - 4 4 % - X2 = X7 X1 X++ - X11 * X6 = '
    # hl = po_util.parse(hl)[1].c().strip()
    # print hl
    # hl_tree = compare_hl.from_list_to_tree(hl.split(' '))
    # hl = from_tree_to_code(hl_tree)
    hl = 'while ( ( X9 / ( ( 88 * X3 ) - X1 ) ) <= ( ( ( X10 % 95 ) - X5 ) - X7 ) ) { while ( X3 ++ < ( ( ( ( 69 / X9 ) % X13 ) + 33 ) % X6 ) ) { if ( ( ( ( X0 + 44 ) / ( 78 % X9 ) ) % 80 ) <= ( ( ( X7 / X13 ) % 55 ) - ( ( 24 - X2 ) % X8 ) ) ) { while ( X3 ++ < ( ( ( ( 39 / X9 ) % X13 ) + 33 ) % X6 ) ) { X3 = 77 / X3 ; } ; } else { X1 = ( X11 / 55 ) + X7 ; } ; } ; } ;'
    ll_origin = 'jmp .L2 ; .L0 : ; movl X0 , %eax ; leal -34 ( %eax ) , %ecx ; movl X9 , %ebx ; movl 87 , %eax ; idivl %ebx ; movl %edx , %esi ; movl %ecx , %eax ; idivl %esi ; movl %eax , %ebx ; movl 1717986919 , %edx ; movl %ebx , %eax ; imull %edx ; sarl 5 , %edx ; movl %ebx , %eax ; sarl 31 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl %ecx , %eax ; sall 2 , %eax ; addl %ecx , %eax ; sall 4 , %eax ; subl %eax , %ebx ; movl %ebx , %ecx ; movl X7 , %eax ; movl X13 , %esi ; idivl %esi ; movl %eax , %esi ; movl 156180629 , %edx ; movl %esi , %eax ; imull %edx ; sarl 1 , %edx ; movl %esi , %eax ; sarl 31 , %eax ; movl %edx , %ebx ; subl %eax , %ebx ; imull 55 , %ebx , %eax ; subl %eax , %esi ; movl %esi , %ebx ; movl X2 , %eax ; movl 24 , %edx ; subl %eax , %edx ; movl %edx , %eax ; movl X8 , %esi ; idivl %esi ; movl %edx , %eax ; subl %eax , %ebx ; movl %ebx , %eax ; cmpl %eax , %ecx ; jg .L3 ; jmp .L2 ; .L1 : ; movl X3 , %esi ; movl 77 , %eax ; idivl %esi ; movl %eax , X3 ; .L2 : ; movl X3 , %ecx ; leal 1 ( %ecx ) , %eax ; movl %eax , X3 ; movl X9 , %esi ; movl 69 , %eax ; idivl %esi ; movl X13 , %ebx ; idivl %ebx ; movl %edx , %eax ; addl 31 , %eax ; movl X6 , %ebx ; idivl %ebx ; movl %edx , %eax ; cmpl %eax , %ecx ; jl .L1 ; jmp .L3 ; .L3 : ; movl X11 , %ecx ; movl 1374389535 , %edx ; movl %ecx , %eax ; imull %edx ; sarl 4 , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl X7 , %eax ; addl %edx , %eax ; movl %eax , X1 ; .L3 : ; movl X10 , %eax ; addl 1 , %eax ; movl %eax , X10 ; movl X10 , %eax ; movl 57 , %edx ; movl %edx , %esi ; subl %eax , %esi ; movl X11 , %ebx ; movl 45 , %eax ; idivl %ebx ; movl %eax , %edx ; movl X6 , %eax ; leal ( %edx ,%eax ) , %ecx ; movl X0 , %eax ; movl X4 , %ebx ; idivl %ebx ; movl %edx , %ebx ; movl %ecx , %eax ; idivl %ebx ; movl %edx , %eax ; cmpl %eax , %esi ; jle .L0 ; .L2 : ; movl X9 , %eax ; movl X3 , %edx ; imull 38 , %edx , %ecx ; movl X1 , %edx ; subl %edx , %ecx ; movl %ecx , %esi ; idivl %esi ; movl %eax , %ebx ; movl X10 , %ecx ; movl -1401515643 , %edx ; movl %ecx , %eax ; imull %edx ; leal ( %edx ,%ecx ) , %eax ; sarl 6 , %eax ; movl %eax , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl %edx , %eax ; imull 95 , %eax , %eax ; subl %eax , %ecx ; movl %ecx , %eax ; movl X5 , %edx ; subl %edx , %eax ; movl %eax , %edx ; movl X7 , %eax ; subl %eax , %edx ; movl %edx , %eax ; cmpl %eax , %ebx ; jle .L3 ;'
    ll_model = 'jmp .L2 ; .L0 : ; movl X0 , %eax ; leal 44 ( %eax ) , %ecx ; movl X9 , %ebx ; movl 78 , %eax ; idivl %ebx ; movl %edx , %esi ; movl %ecx , %eax ; idivl %esi ; movl %eax , %ebx ; movl 1717986919 , %edx ; movl %ebx , %eax ; imull %edx ; sarl 5 , %edx ; movl %ebx , %eax ; sarl 31 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl %ecx , %eax ; sall 2 , %eax ; addl %ecx , %eax ; sall 4 , %eax ; subl %eax , %ebx ; movl %ebx , %ecx ; movl X7 , %eax ; movl X13 , %esi ; idivl %esi ; movl %eax , %esi ; movl 156180629 , %edx ; movl %esi , %eax ; imull %edx ; sarl 1 , %edx ; movl %esi , %eax ; sarl 31 , %eax ; movl %edx , %ebx ; subl %eax , %ebx ; imull 55 , %ebx , %eax ; subl %eax , %esi ; movl %esi , %ebx ; movl X2 , %eax ; movl 24 , %edx ; subl %eax , %edx ; movl %edx , %eax ; movl X8 , %esi ; idivl %esi ; movl %edx , %eax ; subl %eax , %ebx ; movl %ebx , %eax ; cmpl %eax , %ecx ; jg .L3 ; jmp .L2 ; .L1 : ; movl X3 , %esi ; movl 77 , %eax ; idivl %esi ; movl %eax , X3 ; .L2 : ; movl X3 , %ecx ; leal 1 ( %ecx ) , %eax ; movl %eax , X3 ; movl X9 , %esi ; movl 39 , %eax ; idivl %esi ; movl X13 , %ebx ; idivl %ebx ; movl %edx , %eax ; addl 33 , %eax ; movl X6 , %ebx ; idivl %ebx ; movl %edx , %eax ; cmpl %eax , %ecx ; jl .L1 ; jmp .L3 ; .L3 : ; movl X11 , %ecx ; movl 156180629 , %edx ; movl %ecx , %eax ; imull %edx ; sarl 1 , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl X7 , %eax ; addl %edx , %eax ; movl %eax , X1 ; .L3 : ; movl X3 , %ecx ; leal 1 ( %ecx ) , %eax ; movl %eax , X3 ; movl X9 , %esi ; movl 69 , %eax ; idivl %esi ; movl X13 , %ebx ; idivl %ebx ; movl %edx , %eax ; addl 33 , %eax ; movl X6 , %ebx ; idivl %ebx ; movl %edx , %eax ; cmpl %eax , %ecx ; jl .L0 ; .L2 : ; movl X9 , %eax ; movl X3 , %edx ; imull 88 , %edx , %ecx ; movl X1 , %edx ; subl %edx , %ecx ; movl %ecx , %esi ; idivl %esi ; movl %eax , %ebx ; movl X10 , %ecx ; movl -1401515643 , %edx ; movl %ecx , %eax ; imull %edx ; leal ( %edx ,%ecx ) , %eax ; sarl 6 , %eax ; movl %eax , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl %edx , %eax ; imull 95 , %eax , %eax ; subl %eax , %ecx ; movl %ecx , %eax ; movl X5 , %edx ; subl %edx , %eax ; movl %eax , %edx ; movl X7 , %eax ; subl %eax , %edx ; movl %edx , %eax ; cmpl %eax , %ebx ; jle .L3 ;'
    fixed_hl = fix_hl(hl, ll_origin, ll_model)
    print fixed_hl
    print compiler(fixed_hl) == ll_origin
