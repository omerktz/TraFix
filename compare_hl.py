from tree import Node
import re

line_seperator = ';'
start_bracket = '('
close_bracket = ')'
brakets = [start_bracket,close_bracket]
strong_opers = ['*', '/', '%']
whick_opers = ['+','-']
opers = strong_opers + whick_opers
equal = '='
short_opers = ['++','--']
conditions = ['>','>=','<','<=','==','!=']
numbers_pattern = '^N?\d+'
vars_pattern = '^X\d+'
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
            if (strong_opers.__contains__(word)):
                return index
            if (first_whick_oper_index == none_oper_index and whick_opers.__contains__(word)):
                first_whick_oper_index = index
    return first_whick_oper_index

def from_line_to_tree(h_list_line):
    # print (h_list_line)
    # print (h_list_line.__len__())
    left_tree = None
    right_tree = None
    if (h_list_line.__len__() == 1):
        root_val = h_list_line[0]
    else:
        oper_index = find_oper_idex(h_list_line)
        if (oper_index != none_oper_index):
            root_val =  h_list_line[oper_index]
            left_tree = from_line_to_tree(h_list_line[:oper_index])
            right_tree = from_line_to_tree(h_list_line[oper_index + 1:])
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
        # print h_list
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


def compare_node(h_val, hl_val):
    if (h_val == hl_val):
        return [True, '']
    h_type = get_type(h_val)
    hl_type = get_type(hl_val)
    if (h_type == hl_type):
        exp = 'same type, both: ' + h_type + ' model value: ' + h_val + ' wanted value: ' + hl_val
    else:
        exp = 'not same type, model type: ' + h_type + ' wanted type: ' + hl_type
    return [False, exp]


def get_to_return_4_combinations(h_tree_line, hl_tree_line, depth):
    to_return_same_side = get_to_return_same_side(h_tree_line, hl_tree_line, depth)
    if (to_return_same_side[0]):
        return to_return_same_side

    to_return_right_left = compare_lines(h_tree_line.right, hl_tree_line.left, depth)
    to_return_left_right = compare_lines(h_tree_line.left, hl_tree_line.right, depth)

    to_return_not_same_side = combine_two_returns(to_return_right_left, to_return_left_right)
    if (to_return_not_same_side[0]):
        return to_return_not_same_side

    if (to_return_not_same_side[2] > to_return_same_side[2]):
        return to_return_not_same_side

    return to_return_same_side

def combine_two_returns(to_return_1, to_return_2):
    if (to_return_1[0] and to_return_2[0]):
        return [True, '', to_return_2[2] + to_return_1[2]]
    elif (to_return_1[0]):
        return to_return_2
    elif (to_return_2[0]):
        return to_return_1
    else:
        if (to_return_1[2] > to_return_2[2]):
            return to_return_1
        else:
            return to_return_2


def get_to_return_same_side(h_tree_line, hl_tree_line, depth):
    to_return_right = compare_lines(h_tree_line.right, hl_tree_line.right, depth)
    to_return_left = compare_lines(h_tree_line.left, hl_tree_line.left, depth)
    return combine_two_returns(to_return_right, to_return_left)

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
            elif (opers.__contains__(hl_tree_line.value)):
                to_return = get_to_return_4_combinations(h_tree_line, hl_tree_line, depth + 1)
            elif (short_opers.__contains__(h_tree_line.value) or h_tree_line.value == equal or conditions.__contains__(h_tree_line.value)):
                to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
        else:
            to_return = [False, compared_nodes[1], depth]
    # print 'h_tree_line: ' + h_tree_line.__str__()
    # print 'hl_tree_line: ' + hl_tree_line.__str__()
    # print 'to_return: ' + str(to_return)
    return to_return


def compare_trees(h_tree, hl_tree):
    for x in range(min(h_tree.__len__(),hl_tree.__len__())):
        h_tree_line = h_tree[x]
        hl_tree_line = hl_tree[x]
        print h_tree_line
        print hl_tree_line
        print compare_lines(h_tree_line, hl_tree_line, 0)

def writeMisMatches_hl(fhl, h, hl):
    h_tree = from_list_to_tree(h.split(' '))
    hl_tree = from_list_to_tree(hl.split(' '))
    compare_trees(h_tree, hl_tree)

if __name__ == "__main__":
    h_tree = from_list_to_tree('X1 = ( X1 % 62 ) + X6 -- ;'.split(' '))
    hl_tree = from_list_to_tree('X1 = ( X1 % 31 ) + X6 -- ;'.split(' '))
    compare_trees (h_tree, hl_tree)
    # lines = (from_list_to_tree('X13 = ( ( ( X5 / X9 ) / X8 ) * X5 ) % 7 ; X7 = ( ++ X12 / ( N8 % ( X14 % ( N14 - X3 ) ) ) ) / ( -- X8 - -- X0 ) ; X5 = N18 ; X11 = ( ( X11 -- * X12 ) % ( X7 / ( N13 / X13 ) ) ) % ( ( ( ( N3 - X7 ) / -- X5 ) + N7 ) * 40 ) ;'.split(' ')))
    # for line in lines:
    #     print line
