from tree import Node
import re
import postOrderUtil

line_seperator = ';'
start_bracket = '('
close_bracket = ')'
brakets = [start_bracket,close_bracket]
mult = '*'
div = '/'
strong_opers = [mult, div, '%']
plus = '+'
minus = '-'
whick_opers = [plus, minus]
opers = strong_opers + whick_opers
non_komotative_opers = ['%',div,'-']
equal = '='
short_opers = ['++','--']
conditions = ['>','>=','<','<=','==','!=']
numbers_pattern = '^-?\d+'
vars_pattern = '^X\d+'
loops = ['while']
ifs = ['else', 'if']
special_bracket_start = '{'
special_bracket_close = '}'
special_brackets = [special_bracket_start, special_bracket_close]

none_oper_index = -100


def find_oper_idex(h_list_line):
    open_brackets = 0
    first_whick_oper_index = none_oper_index
    index = -1
    for word in h_list_line:
        index += 1
        if (word == equal):
            return index
        if(word == start_bracket):
            open_brackets += 1
        elif (word == close_bracket):
            open_brackets -= 1
        elif (open_brackets == 0):
            if (strong_opers.__contains__(word) or conditions.__contains__(word)):
                return index
            if (first_whick_oper_index == none_oper_index and whick_opers.__contains__(word)):
                first_whick_oper_index = index
    return first_whick_oper_index


def is_left_digit(tree):
    return tree.get_left().value.isdigit()

def is_right_digit(tree):
    return tree.get_right().value.isdigit()


def concat_digits_plus_plus(tree, value):
    if (is_left_digit(tree)):
        tree.get_left().set_value(str(int(tree.get_left().get_value()) + int(value)))
        return tree
    if (is_right_digit(tree)):
        tree.get_right().set_value(str(int(tree.get_right().get_value()) + int(value)))
        return tree
    return None

def concat_digits_plus_minus(tree, value):
    if (is_left_digit(tree)):
        tree.get_left().set_value(str(int(tree.get_left().get_value()) + int(value)))
        return tree
    if (is_right_digit(tree)):
        tree.get_right().set_value(str(int(tree.get_right().get_value()) - int(value)))
        return tree
    return None

def concat_digits_minus_plus(tree, value):
    if (is_left_digit(tree)):
        tree.get_left().set_value(str(int(tree.get_left().get_value()) - int(value)))
        return tree
    if (is_right_digit(tree)):
        tree.get_right().set_value(str(int(tree.get_right().get_value()) - int(value)))
        return tree
    return None

def concat_digits_minus_minus(tree, value):
    if (is_left_digit(tree)):
        tree.get_left().set_value(str(int(tree.get_left().get_value()) - int(value)))
        return tree
    if (is_right_digit(tree)):
        tree.get_right().set_value(str(int(tree.get_right().get_value()) + int(value)))
        return tree
    return None


def concat_digits_mult(tree, value):
    if (is_left_digit(tree)):
        tree.get_left().set_value(str(int(tree.get_left().get_value()) * int(value)))
        return tree
    if (is_right_digit(tree)):
        tree.get_right().set_value(str(int(tree.get_right().get_value()) * int(value)))
        return tree
    return None


def handle_plus_concatination(left_tree, right_tree):
    if (right_tree.get_value().isdigit() and left_tree.get_value().isdigit()):
        return Node(str(int(right_tree.get_value()) + int(left_tree.get_value())))

    if (right_tree.get_value().isdigit()):
        if (left_tree.get_value() == plus):
            tree = concat_digits_plus_plus(left_tree, right_tree.get_value())
            if (tree is not None):
                return tree
        elif (left_tree.get_value() == minus):
            tree = concat_digits_plus_minus(left_tree, right_tree.get_value())
            if (tree is not None):
                return tree

    elif (left_tree.get_value().isdigit()):
        if (right_tree.get_value() == plus):
            tree = concat_digits_plus_plus(right_tree, left_tree.get_value())
            if (tree is not None):
                return tree
        elif (right_tree.get_value() == minus):
            tree = concat_digits_plus_minus(right_tree, left_tree.get_value())
            if (tree is not None):
                return tree

    return None


def handle_minus_concatination(left_tree, right_tree):
    if (right_tree.get_value().isdigit() and left_tree.get_value().isdigit()):
        return Node(str(int(left_tree.get_value()) - int(right_tree.get_value())))

    if (right_tree.get_value().isdigit()):
        if (left_tree.get_value() == plus):
            tree = concat_digits_minus_plus(left_tree, right_tree.get_value())
            if (tree is not None):
                return tree

        elif (left_tree.get_value() == minus):
            tree = concat_digits_minus_minus(left_tree, right_tree.get_value())
            if (tree is not None):
                return tree

    # TODO: num - (x +- num) - changes a lot

    return None

def handle_mult_concatination(left_tree, right_tree):
    if (right_tree.get_value().isdigit() and left_tree.get_value().isdigit()):
        return Node(str(int(left_tree.get_value()) * int(right_tree.get_value())))

    if (right_tree.get_value().isdigit()):
        if (left_tree.get_value() == mult):
            tree = concat_digits_mult(left_tree, right_tree.get_value())
            if (tree is not None):
                return tree

    elif (left_tree.get_value().isdigit()):
        if (right_tree.get_value() == mult):
            tree = concat_digits_mult(right_tree, left_tree.get_value())
            if (tree is not None):
                return tree

    return None


def concatinate_opers(root_val, left_tree, right_tree):
    tree = None
    if(root_val == plus):
        tree = handle_plus_concatination(left_tree, right_tree)

    if (root_val == minus):
        tree = handle_minus_concatination(left_tree, right_tree)

    if (root_val == mult):
        tree = handle_mult_concatination(left_tree, right_tree)

    if(tree is not None):
        return tree

    line_tree = Node(root_val)
    line_tree.set_left(left_tree)
    line_tree.set_right(right_tree)
    return line_tree


def from_line_to_tree(h_list_line):
    # print (h_list_line)
    # print (h_list_line.__len__())
    left_tree = None
    right_tree = None
    if (h_list_line.__len__() == 0):
        return None

    if (h_list_line.__len__() == 1):
        root_val = h_list_line[0]

    elif (h_list_line[0] == special_bracket_close):
        return from_line_to_tree(h_list_line[1:])

    elif (loops.__contains__(h_list_line[0]) or ifs.__contains__(h_list_line[0])):
        start_inside_loop_if = h_list_line.index(special_bracket_start)
        root_val = special_bracket_start
        left_tree = from_line_to_tree(h_list_line[1:start_inside_loop_if])
        if (left_tree is not None):
            left_tree.set_most_left(h_list_line[0])
        else:
            left_tree = Node(h_list_line[0])
        right_tree = from_line_to_tree(h_list_line[start_inside_loop_if + 1:])

    else:
        oper_index = find_oper_idex(h_list_line)
        if (oper_index != none_oper_index):
            root_val = h_list_line[oper_index]
            left_tree = from_line_to_tree(h_list_line[:oper_index])
            right_tree = from_line_to_tree(h_list_line[oper_index + 1:])
            return concatinate_opers(root_val, left_tree, right_tree)
        elif (h_list_line[0] == start_bracket):
            bracket_tree = from_line_to_tree(h_list_line[1:-1])
            bracket_tree.set_most_left(start_bracket)
            bracket_tree.set_most_right(close_bracket)
            return bracket_tree
        elif (short_opers.__contains__(h_list_line[1])):
            root_val = h_list_line[1]
            left_tree = from_line_to_tree(h_list_line[:-1])
        elif (short_opers.__contains__(h_list_line[0])):
            root_val = h_list_line[0]
            right_tree = from_line_to_tree(h_list_line[1:])

    line_tree = Node(root_val)
    line_tree.set_left(left_tree)
    line_tree.set_right(right_tree)
    return line_tree

def from_list_to_tree(h_list):
    lines = []
    while h_list.__len__() > 1:
        index = h_list.index(line_seperator)
        lines.append(from_line_to_tree(h_list[:index]))
        h_list = h_list[index + 1:]
    return lines

def is_var(hl_val):
    temp = re.match(vars_pattern, hl_val)
    return temp is not None and temp.group() == hl_val

def is_number(hl_val):
    temp = re.match(numbers_pattern, hl_val)
    return temp is not None and temp.group() == hl_val


def get_type(h_val):
    if (opers.__contains__(h_val)):
        return 'oper'
    if (is_number(h_val)):
        return 'number'
    if (is_var(h_val)):
        return 'var'
    if (short_opers.__contains__(h_val)):
        return 'short_oper'
    if (h_val == equal):
        return equal
    if (conditions.__contains__(h_val)):
        return 'cond'
    if (brakets.__contains__(h_val)):
        return 'brackets'
    if (loops.__contains__(h_val)):
        return 'loop'
    if (ifs.__contains__(h_val)):
        return 'if/else'
    if (special_brackets.__contains__(h_val)):
        return 'special_brackets'


def compare_node(h_val, hl_val):
    if (h_val == hl_val):
        return [True, '']
    h_type = get_type(h_val)
    hl_type = get_type(hl_val)
    if (h_type == hl_type):
        exp = 'model: ' + h_val + ' wanted: ' + hl_val
    else:
        exp = 'type_diff - model: ' + h_val + ' wanted: ' + hl_val
    return [False, [exp]]


def combine_two_returns_and(to_return_1, to_return_2):
    if (to_return_1[0] and to_return_2[0]):
        return [True, '', to_return_2[2] + to_return_1[2]]
    elif (to_return_1[0]):
        return to_return_2
    elif (to_return_2[0]):
        return to_return_1
    else:
        return [False, to_return_1[1] + to_return_2[1], [to_return_1[2], to_return_2[2]]]


def get_to_return_4_combinations(h_tree_line, hl_tree_line, depth):
    to_return_same_side = get_to_return_same_side(h_tree_line, hl_tree_line, depth)
    if (to_return_same_side[0]):
        return to_return_same_side

    to_return_right_left = compare_lines(h_tree_line.right, hl_tree_line.left, depth)
    to_return_left_right = compare_lines(h_tree_line.left, hl_tree_line.right, depth)

    to_return_not_same_side = combine_two_returns_and(to_return_right_left, to_return_left_right)
    if (to_return_not_same_side[0]):
        return to_return_not_same_side
    return combine_two_returns_or(to_return_same_side, to_return_not_same_side)

def combine_two_returns_or(to_return_1, to_return_2):
    # print 'to_return1: ' + str(to_return_1)
    # print 'to_return2: ' + str(to_return_2)
    depth_1 = max(to_return_1[2]) if isinstance(to_return_1[2],list) else to_return_1[2]
    depth_2 = max(to_return_2[2]) if isinstance(to_return_2[2], list) else to_return_2[2]
    if (depth_1 > depth_2):
        return to_return_1
    elif (depth_1 < depth_2):
        return to_return_2
    else:
        if any('type_diff' in s for s in to_return_1[1]):
            return to_return_2
        else:
            return to_return_1


def get_to_return_same_side(h_tree_line, hl_tree_line, depth):
    to_return_right = compare_lines(h_tree_line.right, hl_tree_line.right, depth)
    to_return_left = compare_lines(h_tree_line.left, hl_tree_line.left, depth)
    return combine_two_returns_and(to_return_right, to_return_left)

def compare_lines(h_tree_line, hl_tree_line, depth):
    to_return = []
    if(h_tree_line == None or hl_tree_line == None):
        to_return = [h_tree_line == hl_tree_line, '', depth]
    else:
        compared_nodes = compare_node(h_tree_line.value, hl_tree_line.value)
        if(compared_nodes[0]):
            if (is_var(h_tree_line.value)):
                to_return = [True, '', depth]
            elif (is_number(h_tree_line.value)):
                to_return = [True, '', depth]
            elif (loops.__contains__(h_tree_line.value) or ifs.__contains__(h_tree_line.value)):
                to_return = [True, '', depth]
            elif (h_tree_line == special_bracket_close):
                to_return = [True, '', depth]
            elif (opers.__contains__(hl_tree_line.value)):
                if (non_komotative_opers.__contains__(hl_tree_line.value)):
                    to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
                else:
                    to_return = get_to_return_4_combinations(h_tree_line, hl_tree_line, depth + 1)
            elif (h_tree_line.value == equal or conditions.__contains__(h_tree_line.value)):
                to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
            elif (short_opers.__contains__(h_tree_line.value)):
                if (h_tree_line.get_left() is not None) and is_var(h_tree_line.get_left().value):
                    to_return = compare_lines(h_tree_line.get_left(), hl_tree_line.get_left(), depth + 1)
                else:
                    to_return = compare_lines(h_tree_line.get_right(), hl_tree_line.get_right(), depth + 1)
            elif (h_tree_line.value == special_bracket_start):
                to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)

        else:
            to_return = [False, compared_nodes[1], depth]
    # print 'h_tree_line: ' + h_tree_line.__str__()
    # print 'hl_tree_line: ' + hl_tree_line.__str__()
    # print 'to_return: ' + str(to_return)
    return to_return


def compare_trees(h_tree, hl_tree):
    to_return = []
    first_line_mistake = -1
    for x in range(min(h_tree.__len__(),hl_tree.__len__())):
        h_tree_line = h_tree[x]
        hl_tree_line = hl_tree[x]
        # print h_tree_line
        # print hl_tree_line
        # print compare_lines(h_tree_line, hl_tree_line, 0)
        compared_line = compare_lines(h_tree_line, hl_tree_line, 0)
        print compared_line
        if (not compared_line.__len__() == 0 and not compared_line[0] and first_line_mistake == -1):
            first_line_mistake = x

        to_return.append(compared_line)

    if (not h_tree.__len__() == hl_tree.__len__()):
        to_return.append('num lines diff. model: ' + h_tree.__len__() + 'origin: ' + hl_tree.__len__())
    to_return.append('first line mistake: %d' %(first_line_mistake+1))
    return to_return

def writeMisMatches_hl(fhl, h, hl):
    fhl.write('origin: ' + hl + '\n')
    h_post_order_list = h.split(' ')
    hl_post_order_list = hl.split(' ')
    # fhl.write(str(find_first_difference(h_post_order_list, hl_post_order_list)) + '\n')

    normal_order_h = postOrderUtil.parse(h)[1].c()
    normal_order_hl = postOrderUtil.parse(hl)[1].c()
    fhl.write('model, normal: ' + normal_order_h + '\n')
    fhl.write('origin, normal: ' + normal_order_hl + '\n')

    h_tree = from_list_to_tree(normal_order_h.split(' '))
    hl_tree = from_list_to_tree(normal_order_hl.split(' '))
    fhl.write(str(compare_trees(h_tree, hl_tree)) + '\n')


def find_first_difference(h_post_order_list, hl_post_order_list):
    to_return = []
    for x in range(min(h_post_order_list.__len__(), hl_post_order_list.__len__())):
        compared = compare_node(h_post_order_list[x], hl_post_order_list[x])
        if(compared[0]):
            continue
        elif (not compared[1][0].__contains__('type_diff')):
            to_return.append(compared[1][0] + ' in %d' %x)
        else:
            to_return.append(compared[1][0] + ' in %d' %x)
            break
    if not h_post_order_list.__len__() == hl_post_order_list.__len__() :
        to_return.append('length diff. model: ' + str(h_post_order_list.__len__()) + ' wanted: ' + str(hl_post_order_list.__len__()))
    return to_return

if __name__ == "__main__":
    # h_sentence = '( X1 + 5 ) - 6 ;'
    # h_tree = from_list_to_tree(h_sentence.split(' '))
    # print h_tree[0]
    # exit (0)
    # h_post_order = 'X3 87 + 87 + 87 X3 - 75 + % X12 X++ X9 + - X1 X-- + X7 ='
    # hl_post_order = '11 92 X3 + + N18 X3 - % X12 X++ X9 + - X1 X-- + X7 ='
    h_post_order = '18 X7 ='
    hl_post_order = '18 X7 ='
    h_post_order_list = h_post_order.split(' ')
    hl_post_order_list = hl_post_order.split(' ')

    print find_first_difference(h_post_order_list, hl_post_order_list)

    h_sentence = postOrderUtil.parse(h_post_order)[1].c()
    hl_sentence = postOrderUtil.parse(hl_post_order)[1].c()

    h_sentence = 'while ( -- X14 >= 53 ) { X11 = ( X5 -- / X5 ) * ( ( X14 * X12 ) / ( X0 / ( X4 / 14 ) ) ) ; X2 = -- X8 % ( ++ X11 / X13 -- ) ; } ;'
    hl_sentence = 'while ( 31 >= -- X14 ) { X11 = ( X5 -- / X5 ) * ( ( X14 * X12 ) / ( ( X0 - X4 ) / ( X4 / 56 ) ) ) ; X2 = -- X8 % ( ++ X11 / X13 -- ) ; } ;'

    # h_sentence = postOrderUtil.parse('X5 X8 ++X 21 % N11 + + X5 + X0 X-- * X12 ++X != COND X6 ++X N7 * X7 51 - N2 X14 X10 % N4 * % / - X0 = WHILE')[1].c()
    # hl_sentence = postOrderUtil.parse('X5 X++ X8 ++X X10 --X / > COND X3 N5 + X7 X++ X1 * - X14 = TRUE IF X5 X-- 2 + N3 N8 X4 67 / X3 / % / - X13 = X5 X++ X12 = N2 X14 --X >= COND X5 X-- X5 / X14 X12 * X0 X4 - X4 56 / / / * X11 = X8 --X X11 ++X X13 X-- / % X2 = WHILE N18 X3 / X7 / N10 + N12 X11 --X + + X11 =')[1].c()

    h_tree = from_list_to_tree(h_sentence.split(' '))
    hl_tree = from_list_to_tree(hl_sentence.split(' '))
    print h_sentence
    h_string = ''
    for tree in h_tree:
        h_string += tree.__str__() + ' ; '
    print h_string
    print hl_sentence
    hl_string = ''
    for tree in hl_tree:
        hl_string += tree.__str__() + ' ; '
    print hl_string
    print compare_trees (h_tree, hl_tree)

    # lines = (from_list_to_tree('while ( ( ( X13 ++ % X13 ) % ( ( N8 % X13 ) / X2 -- ) ) >= ( N16 / ( ( X7 * ( N13 + X0 ) ) % X13 ) ) ) { X7 = N2 ; X10 = X2 + ( ( X13 / -- X4 ) + X1 ) ; } ; X7 = -- X9 ; if ( X14 <= ( -- X6 + X6 ++ ) ) { X2 = N14 * ( X4 ++ / ( ( X8 - X1 ) - X11 ) ) ; X11 = ( ( X0 - ( N0 - X8 ) ) * ( N12 * ( X1 + N3 ) ) ) % ( ( 28 * ( N15 + X11 ) ) / ( N11 % -- X6 ) ) ; } else { X6 = N18 - ( ( N7 % X5 ) % -- X13 ) ; } ; X13 = ( 21 * X14 ) * N16 ; if ( 7 > ( -- X1 - X7 -- ) ) { X0 = N6 ; } ;'.split(' ')))
    # for line in lines:
    #     print line
