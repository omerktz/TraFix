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
plus = '+'
minus = '-'

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


def create_and_check_hl(list_hl, i, ll_origin, index, new_value):
    try_hl = list_hl[:]
    try_hl[i] = new_value
    try_hl = ' '.join(try_hl)
    try_ll = compiler(try_hl)
    if try_ll is None:
        return None
    first_mis_match = find_first_mis_match(ll_origin, try_ll.split(' '))
    if (first_mis_match == -1 or first_mis_match > index):
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

# def divsdivs(hl_list, origin_model_ll, mistake_index, new_value):
#     divs = filter(lambda x: hl_list[x] == '/', range(len(hl_list)))
#     numbers = map(lambda i: i + 1, divs)
#     last_changed = 0
#     for i in numbers:
#         original_value = hl_list[i]
#         if not is_number(original_value):
#             continue
#         if(hl_list[i] == '87'):
#             hl_list[i] = '77'
#         else:
#             hl_list[i] = '87'
#         new_model_ll = compiler(' '.join(hl_list)).split(' ')
#
#         if new_model_ll[mistake_index] != origin_model_ll[mistake_index]:
#             # this is not the div that we are after
#             hl_list[i] = original_value
#             continue
#
#         original_int = int(original_value)
#         new_values = set()
#         replacement = replacements[relevant_replacements[0]][0]
#         # the first replacement. const 0 - origin. const 1 - models.
#         constant0 = int(replacement[0])
#         constant1 = int(replacement[1])
#         if len(relevant_replacements) == 1:
#             # we changed the exp
#             if (constant0 > 0) and (constant0 <= 32):
#                 if (constant1 > 0) and (constant1 <= 32):
#                     if constant0 - constant1 > 0:
#                         new_values.add(original_int >> (constant0 - constant1))
#                     else:
#                         new_values.add(original_int << (constant1 - constant0))
#             else:
#                 new_values.add(original_int * constant0 / float(constant1))
#                 new_values.add(original_int * (constant0 + (1 << 32)) / float(constant1 + (1 << 32)))
#         elif len(replacements) == 2:
#             power_replacement = map(lambda x: int(x), replacements[relevant_replacements[1]][0])
#             if (power_replacement[0] > 0) and (power_replacement[0] <= 32) and (power_replacement[1] > 0) and (
#                     power_replacement[1] <= 32):
#                 try:
#                     if original_int * constant0 >> (power_replacement[0] + 32) == 1:
#                         new_values.add((1 << (32 + power_replacement[1])) / float(constant1))
#                     elif original_int * (constant0 + (1 << 32)) >> (power_replacement[0] + 32) == 1:
#                         new_values.add((1 << (32 + power_replacement[1])) / float(constant1 + (1 << 32)))
#                     else:
#                         # print "Unknown div to mul pattern"
#                         # print map(lambda x: (x, replacements[x]), relevant_replacements)
#                         pass
#                 except OverflowError:
#                     pass
#         for new_value in new_values:
#             new_value_str = str(int(round(new_value)))
#             new_remaining_replacements = try_new_value(str(new_value_str), hl_list, i, ll, compiler, comparison)
#             if new_remaining_replacements is None:
#                 hl_list[i] = original_value
#                 continue
#             if len(new_remaining_replacements.keys()) == 0:
#                 hl_list[i] = str(new_value_str)
#                 return ' '.join(hl_list)
#             if found_right_replacement(new_remaining_replacements, replacements, relevant_replacements):
#                 remaining_replacements = new_remaining_replacements
#                 break
#             hl_list[i] = original_value
#         last_changed = changed
#     return None

def find_exp(ll, index):
    for i in range(index, ll.__len__()):
        if ll[i] == 'sarl':
            return int(ll[i+1])
    return None


def fix_div_in_hl(hl, ll_origin, ll_model, index, is_exp=False):
    list_hl = hl.split(' ')
    for i in range(list_hl.__len__()):
        if list_hl[i] in divs:
            if is_number(list_hl[i+1]):
                origin_value_hl = list_hl[i+1]
                if(list_hl[i+1] == '87' or (is_exp and ll_model[index] == '4')):
                    list_hl[i+1] = '97'
                else:
                    list_hl[i+1] = '87'
                temp_model_ll = compiler(' '.join(list_hl)).split(' ')
                if temp_model_ll.__len__() <= index or temp_model_ll[index] == ll_model[index]:
                    list_hl[i+1] = origin_value_hl
                else:
                    if abs(int(ll_model[index])) < 100:
                        exp_diff = int(ll_model[index]) - int(ll_origin[index])
                        if exp_diff > 0:
                            replacement = str(int(origin_value_hl) >> exp_diff)
                        else:
                            replacement = str(int(origin_value_hl) << abs(exp_diff))
                        try_hl = create_and_check_hl(list_hl, i + 1, ll_origin, index, replacement)
                        if try_hl is not None:
                            return try_hl
                    else:
                        origin_value_hl = int(origin_value_hl)
                        origin_exp = find_exp(ll_origin, index)
                        origin_const = int(ll_origin[index])
                        models_exp = find_exp(ll_model, index)
                        models_const = int(ll_model[index])
                        if (origin_exp == models_exp):
                            replacement = str(int(round(origin_value_hl * models_const / float(origin_const))))
                            try_hl = create_and_check_hl(list_hl, i + 1, ll_origin, index, replacement)
                            if try_hl is not None:
                                return try_hl
                            replacement = str(int(round(origin_value_hl * (models_const + (1 << 32)) / float(origin_const + (1 << 32)))))
                            try_hl = create_and_check_hl(list_hl, i + 1, ll_origin, index, replacement)
                            if try_hl is not None:
                                return try_hl
                        else:
                            replacement = str(int(round((1 << (32 + origin_exp)) / float(origin_const))))
                            try_hl = create_and_check_hl(list_hl, i + 1, ll_origin, index, replacement)
                            if try_hl is not None:
                                return try_hl
                            replacement = str(int(round((1 << (32 + origin_exp)) / float(origin_const + (1 << 32)))))
                            try_hl = create_and_check_hl(list_hl, i + 1, ll_origin, index, replacement)
                            if try_hl is not None:
                                return try_hl
                    return None
    return None

def try_to_change_oper(hl, ll_origin, index, old_oper, new_oper):
    list_hl = hl.split(' ')
    for i in range(list_hl.__len__()):
        if list_hl[i] in old_oper:
            try_hl = create_and_check_hl(list_hl, i, ll_origin, index, new_oper)
            if try_hl is not None:
                return try_hl

def is_close_numbers(num1, num2):
    return abs(num1 - num2) == 1

def is_devide_num_prob(num1, num2):
    return abs(num1) > max_num and abs(num2) > max_num


def div_exp_fix(ll_origin_list, ll_model_list, i):
    return ll_origin_list[i - 1] == 'sarl' and ll_model_list[i - 1] == 'sarl'


def fix_hl(hl, ll_origin, ll_model, combine=False):
    # print hl
    # print ll_origin
    # print ll_model
    # print combine

    load_compiler('x86Util.py')
    if (combine):
        origin_hl = hl
        hl_tree = compare_hl.from_list_to_tree(hl.split(' '))
        hl = from_tree_to_code(hl_tree)
        if hl == origin_hl or hl == origin_hl[:-2]:
            return None
        # print hl
        # print origin_hl
        # print compiler(hl)
    ll_origin_list = ll_origin.split(' ')
    ll_model_list = ll_model.split(' ')
    close_numbers = False
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
                fixed_hl = fix_div_in_hl(hl, ll_origin_list, ll_model_list, i)
            elif (div_exp_fix(ll_origin_list, ll_model_list, i)):
                fixed_hl = fix_div_in_hl(hl, ll_origin_list, ll_model_list, i, is_exp=True)
            else:
                fixed_hl = fix_number_in_hl(hl, ll_origin_list, ll_model_list[i], i)
        elif (is_var(ll_origin_list[i]) and is_var(ll_model_list[i])):
            fixed_hl = fix_var_in_hl(hl, ll_origin_list, ll_model_list[i], i)
        elif (ll_origin_list[i] in jumps and ll_model_list[i] in jumps):
            fixed_hl = fix_cond_in_hl(hl, ll_origin_list, i)

        # elif(ll_origin_list[i] == 'movl'):
        #     if (ll_model_list[i] == 'addl'):
        #         fixed_hl = try_to_change_oper(hl, ll_origin_list, i, plus, minus)
        #     elif (ll_model_list[i] == 'subl'):
        #         fixed_hl = try_to_change_oper(hl, ll_origin_list, i, minus, plus)
        #     else:
        #         return None
        #
        # elif (ll_origin_list[i] == 'subl') \
        #     and (ll_model_list[i] == 'movl'):
        #         fixed_hl = try_to_change_oper(hl, ll_origin_list, i, plus, minus)
        #
        # elif (ll_origin_list[i] == 'addl') \
        #     and (ll_model_list[i] == 'movl'):
        #         fixed_hl = try_to_change_oper(hl, ll_origin_list, i, minus, plus)

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
    return ' ; '.join(map(lambda x: x.__str__(), hl_tree)).replace('  ', ' ').replace('} }', '} ; }').replace('} ; else', '} else')

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
    # hl = 'X4 X2 = 7 7 | 2 8 X0 9 1 / * * X3 = X14 X11 = X11 7 6 X6 1 5 - + X6 % / 1 0 X0 X2 - 5 4 * X2 + % X4 X6 * X2 / 1 3 * % != COND 9 4 | 1 6 X14 / X6 6 9 % + == COND 1 6 X6 9 9 X5 + 4 1 | 2 5 X4 % * * + % X13 = WHILE WHILE'
    # print po_util.parse(hl)[1].c()
    # print compiler(po_util.parse(hl)[1].c())
    # hl = 'X1 = X1 / 87'
    # print compiler(hl)
    # exit(0)
    # exp_name = os.path.join('/mnt/c/python_technion/Codenator', 'tf_44_to_100')
    # check_successes(exp_name)
    # hl = '2 7 X8 + 6 9 + X4 == COND 7 8 X3 = TRUE IF 3 2 X10 = X2 8 0 | 6 5 X2 % * / X6 X3 + / X3 - X1 = 9 3 | 5 2 X5 5 1 % % % 9 3 X7 - 5 0 + / X6 = X11 --X X13 - X12 ='
    # print compiler(po_util.parse(hl)[1].c())
    # print (po_util.parse(hl)[1].c())
    # exit(0)
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
    hl = '@@ 6 9 | @@ 6 2 X11 * + @@ 9 3 >= COND X14 X-- @@ 7 0 + 2 3 / @@ 6 7 X4 / @@ 6 7 X6 * * / X9 = WHILE @@ 9 1 X0 X4 X1 + - * X8 ='
    hl = po_util.parse(hl)[1].c().strip()
    hl_origin = '@@ 2 9 | @@ 6 4 X11 * + @@ 9 4 > COND X14 X-- @@ 7 0 + 1 3 / @@ 6 7 X4 / @@ 6 7 X6 * * / X9 = WHILE @@ 9 1 X0 X4 X1 + - * X8 ='
    hl_origin = po_util.parse(hl_origin)[1].c().strip()
    # print hl
    # print compiler(hl)
    # print
    # exit(0)
    # hl = 'if ( ( ( ( 12 + X12 ) * ( 29 + X3 ) ) + X14 -- ) >= ( ( ( ( 25 - X13 ) % 28 ) % ( X7 / X6 ) ) / 28 ) ) { while ( ( ( 17 - X4 ) * X11 ) != ( 96 % X5 ) ) { X0 = ++ X8 % X8 ; } ; } else { while ( ( 48 * X8 -- ) == 48 ) { X6 = ( 51 * X12 ) - X14 ; } ; } ; X14 = ( 92 - ( ( X9 + X12 ) + X13 ) ) - ( 40 * ( 20 + X13 ) ) ; X11 = ( 30 * X14 ) % ( 31 % X10 ) ;'
    # hl_tree = compare_hl.from_list_to_tree(hl.split(' '))
    # hl = from_tree_to_code(hl_tree)
    # hl = 'while ( ( X9 / ( ( 88 * X3 ) - X1 ) ) <= ( ( ( X10 % 95 ) - X5 ) - X7 ) ) { while ( X3 ++ < ( ( ( ( 69 / X9 ) % X13 ) + 33 ) % X6 ) ) { if ( ( ( ( X0 + 44 ) / ( 78 % X9 ) ) % 80 ) <= ( ( ( X7 / X13 ) % 55 ) - ( ( 24 - X2 ) % X8 ) ) ) { while ( X3 ++ < ( ( ( ( 39 / X9 ) % X13 ) + 33 ) % X6 ) ) { X3 = 77 / X3 ; } ; } else { X1 = ( X11 / 55 ) + X7 ; } ; } ; } ;'
    ll_origin = compiler(hl_origin)#'movl X12 , %eax ; leal 12 ( %eax ) , %edx ; movl X3 , %eax ; addl 29 , %eax ; movl %edx , %ecx ; imull %eax , %ecx ; movl X14 , %eax ; leal -1 ( %eax ) , %edx ; movl %edx , X14 ; leal ( %ecx ,%eax ) , %esi ; movl X13 , %eax ; movl 25 , %edx ; movl %edx , %ecx ; subl %eax , %ecx ; movl -1840700269 , %edx ; movl %ecx , %eax ; imull %edx ; leal ( %edx ,%ecx ) , %eax ; sarl 4 , %eax ; movl %eax , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; movl %edx , %ebx ; subl %eax , %ebx ; movl %ebx , %edx ; leal 0 ( ,%edx ,4 ) , %eax ; movl %eax , %edx ; leal 0 ( ,%edx ,8 ) , %eax ; subl %edx , %eax ; movl %ecx , %ebx ; subl %eax , %ebx ; movl X7 , %eax ; movl X6 , %ecx ; idivl %ecx ; movl %eax , %ecx ; movl %ebx , %eax ; idivl %ecx ; movl %edx , %ecx ; movl 780903145 , %edx ; movl %ecx , %eax ; imull %edx ; sarl 4 , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl %edx , %eax ; cmpl %eax , %esi ; jl .L3 ; jmp .L1 ; .L0 : ; movl X8 , %eax ; addl 1 , %eax ; movl %eax , X8 ; movl X8 , %eax ; movl X8 , %ecx ; idivl %ecx ; movl %edx , %eax ; movl %eax , X0 ; .L1 : ; movl X4 , %eax ; movl 17 , %edx ; subl %eax , %edx ; movl X11 , %eax ; movl %edx , %ecx ; imull %eax , %ecx ; movl X5 , %ebx ; movl 96 , %eax ; idivl %ebx ; movl %edx , %eax ; cmpl %eax , %ecx ; jne .L0 ; jmp .L0 ; .L2 : ; movl X12 , %eax ; imull 51 , %eax , %edx ; movl X14 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X6 ; .L3 : ; movl X8 , %eax ; leal -1 ( %eax ) , %edx ; movl %edx , X8 ; imull 468 , %eax , %eax ; cmpl 48 , %eax ; je .L2 ; .L0 : ; movl X9 , %edx ; movl X12 , %eax ; addl %eax , %edx ; movl X13 , %eax ; addl %edx , %eax ; movl 92 , %edx ; subl %eax , %edx ; movl X13 , %eax ; addl 20 , %eax ; imull -40 , %eax , %eax ; addl %edx , %eax ; movl %eax , X14 ; movl X14 , %eax ; addl %eax , %eax ; movl %eax , %edx ; sall 4 , %edx ; movl %edx , %ecx ; subl %eax , %ecx ; movl X10 , %ebx ; movl 31 , %eax ; idivl %ebx ; movl %edx , %ebx ; movl %ecx , %eax ; idivl %ebx ; movl %edx , %eax ; movl %eax , X11 ;'
    ll_model = compiler(hl) #'jmp .L2 ; .L0 : ; movl X9 , %ecx ; movl 48 , %eax ; idivl %ecx ; movl %edx , %ecx ; movl X6 , %edi ; movl 71 , %eax ; idivl %edi ; movl %eax , %ebx ; movl %ecx , %eax ; idivl %ebx ; movl X0 , %eax ; movl %edx , %ecx ; subl %eax , %ecx ; movl X8 , %edi ; leal 1 ( %edi ) , %eax ; movl %eax , X8 ; movl %ecx , %eax ; idivl %edi ; movl %edx , %ecx ; movl %ecx , %ebx ; movl X14 , %ecx ; movl -2004318071 , %edx ; movl %ecx , %eax ; imull %edx ; leal ( %edx ,%ecx ) , %eax ; sarl 5 , %eax ; movl %eax , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , %edx ; leal 0 ( ,%edx ,4 ) , %eax ; movl %eax , %edx ; movl %edx , %eax ; sall 4 , %eax ; subl %edx , %eax ; subl %eax , %ecx ; movl %ecx , %eax ; movl 57 , %edx ; movl %edx , %ecx ; subl %eax , %ecx ; movl -2004318071 , %edx ; movl %ecx , %eax ; imull %edx ; leal ( %edx ,%ecx ) , %eax ; sarl 3 , %eax ; movl %eax , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , %edx ; sall 4 , %edx ; subl %eax , %edx ; movl %ecx , %eax ; subl %edx , %eax ; cmpl %eax , %ebx ; jne .L3 ; jmp .L2 ; .L1 : ; movl X9 , %eax ; leal 1 ( %eax ) , %edx ; movl %edx , X9 ; movl %eax , X0 ; .L2 : ; movl X13 , %esi ; movl X14 , %ebx ; movl X1 , %ecx ; movl 1616928865 , %edx ; movl %ecx , %eax ; imull %edx ; sarl 5 , %edx ; movl %ecx , %eax ; sarl 31 , %eax ; movl %edx , %edi ; subl %eax , %edi ; imull 85 , %edi , %eax ; subl %eax , %ecx ; movl %ecx , %edi ; movl %ebx , %eax ; idivl %edi ; movl %edx , %ecx ; movl %ecx , %eax ; subl %eax , %esi ; movl %esi , %eax ; cmpl 69 , %eax ; je .L1 ; jmp .L2 ; .L3 : ; movl X4 , %eax ; movl 72 , %edx ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X12 ; .L2 : ; movl X9 , %edx ; movl X7 , %eax ; movl %edx , %ecx ; imull %eax , %ecx ; movl X3 , %esi ; movl 42 , %eax ; idivl %esi ; movl %eax , %ebx ; movl X11 , %eax ; movl 85 , %edx ; subl %eax , %edx ; movl %edx , %eax ; imull 57 , %eax , %esi ; movl %ebx , %eax ; idivl %esi ; movl %eax , %edx ; movl X11 , %eax ; addl %edx , %eax ; leal ( %ecx ,%eax ) , %edx ; movl X10 , %eax ; cmpl %eax , %edx ; je .L0 ;'
    fixed_hl = fix_hl(hl, ll_origin, ll_model, False)

    print fixed_hl
    print compiler(fixed_hl) == ll_origin
    print hl
    print hl_origin
    print ll_model
    print ll_origin
