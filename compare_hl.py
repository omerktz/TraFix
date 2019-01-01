import os

import numpy

from tree import Node
import re
import postOrderUtil
import csv
import pandas as pd

line_separator = ';'
start_bracket = '('
close_bracket = ')'
brakets = [start_bracket,close_bracket]
mult = '*'
div = '/'
mod = '%'
strong_opers = [mult, div, mod]
plus = '+'
minus = '-'
whick_opers = [plus, minus]
opers = strong_opers + whick_opers
non_komotative_opers = [mod,div,'-']
equal = '='
short_opers = ['++','--']
conditions = ['>','>=','<','<=','==','!=']
numbers_pattern = '^(-|N)?\d+'
vars_pattern = '^X\d+'
loops = ['while']
ifs = ['else', 'if']
branch_types = loops + ifs
special_bracket_start = '{'
special_bracket_close = '}'
special_brackets = [special_bracket_start, special_bracket_close]
# by importance
types = ['while_num', 'else_num', 'if_num', 'lines', 'nodes_num' ,'type_diff', 'loop', 'if/else', equal, 'cond', 'wrong_sides_oper', 'oper', 'short_oper', 'div_mod' ,'num_var', 'var', 'number' ,'special_brackets', 'brackets']
types_with_victory = types + ['victory!!']
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


def without_double_minus(tree, value):
    diff = int(tree.get_right().get_value()) - int(value)
    if (diff < 0):
        tree.set_value(plus)
        diff *= -1
    tree.get_right().set_value(str(diff))
    return tree


def concat_digits_plus_minus(tree, value):
    if (is_left_digit(tree)):
        tree.get_left().set_value(str(int(tree.get_left().get_value()) + int(value)))
        return tree
    if (is_right_digit(tree)):
        return without_double_minus(tree, value)

    return None

def concat_digits_minus_plus(tree, value):
    if (is_left_digit(tree)):
        tree.get_left().set_value(str(int(tree.get_left().get_value()) - int(value)))
        return tree
    if (is_right_digit(tree)):
        return without_double_minus(tree, value)

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

    elif (is_number(right_tree.get_value()) and right_tree.get_value()[0] == minus):
        tree = Node(plus)
        tree.set_left(left_tree)
        tree.set_right(right_tree.get_value()[1:])
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


def handle_div_concatination(left_tree, right_tree):
    if (right_tree.get_value().isdigit() and left_tree.get_value() == div and left_tree.get_right().get_value().isdigit()):
        tree = left_tree
        tree.set_right(Node(str(int(left_tree.get_right().get_value()) * int(right_tree.get_value()))))
        return tree

    else:
        return None

def concatinate_opers(root_val, left_tree, right_tree):
    tree = None
    if(root_val == plus):
        tree = handle_plus_concatination(left_tree, right_tree)

    if (root_val == minus):
        tree = handle_minus_concatination(left_tree, right_tree)

    if (root_val == mult):
        tree = handle_mult_concatination(left_tree, right_tree)

    if (root_val == div):
        tree = handle_div_concatination(left_tree, right_tree)

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

    elif (loops.__contains__(h_list_line[0]) or ifs.__contains__(h_list_line[0])):
        start_inside_loop_if = h_list_line.index(special_bracket_start)
        root_val = h_list_line[0]
        left_tree = from_line_to_tree(h_list_line[1:start_inside_loop_if])
        right_tree = from_line_to_tree(h_list_line[start_inside_loop_if:])

    elif (h_list_line[0] == special_bracket_start):
        end_special_brackets = get_branch_end(h_list_line)
        if (end_special_brackets == h_list_line.__len__()):
            bracket_tree = from_line_to_tree(h_list_line[1:-1])
            bracket_tree.set_most_left(special_bracket_start)
            bracket_tree.set_most_right(special_bracket_close)
            return bracket_tree
        else:
            root_val = line_separator
            left_tree = from_line_to_tree(h_list_line[:end_special_brackets])
            right_tree = from_line_to_tree(h_list_line[end_special_brackets:])


    elif (h_list_line.__contains__(line_separator)):
        index = h_list_line.index(line_separator)
        root_val = line_separator
        left_tree = from_line_to_tree(h_list_line[:index])
        right_tree = from_line_to_tree(h_list_line[index + 1:])

    else:
        oper_index = find_oper_idex(h_list_line)
        if (oper_index != none_oper_index):
            root_val = h_list_line[oper_index]
            left_tree = from_line_to_tree(h_list_line[:oper_index])
            right_tree = from_line_to_tree(h_list_line[oper_index + 1:])
            return concatinate_opers(root_val, left_tree, right_tree)

        if (h_list_line[0] == start_bracket):
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
        if (h_list.__contains__(loops[0]) and h_list.index(loops[0]) == 0):
            index_end = get_branch_end(h_list)
            index_start = index_end + 1
        elif (h_list.__contains__(ifs[0]) and h_list.index(ifs[0]) == 0):
            index_end = get_branch_end(h_list)
            index_start = index_end + 1
        elif (h_list.__contains__(ifs[1]) and h_list.index(ifs[1]) == 0):
            index_end = get_branch_end(h_list)
            index_start = index_end + (0 if h_list[index_end] == ifs[0] else 1)
        else:
            index_end = h_list.index(line_separator)
            index_start = index_end + 1

        lines.append(from_line_to_tree(h_list[:index_end]))
        # lines.append(h_list[:index_end])
        h_list = h_list[index_start:]

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
    if (h_val == line_separator):
        return 'line_separator'


def compare_node(h_val, hl_val):
    if (h_val == hl_val):
        return [True, '']

    h_type = get_type(h_val)
    hl_type = get_type(hl_val)
    if (h_type == hl_type):
        if ((h_type == div and hl_type == mod)
              or (h_type == mod and hl_type == div)):
              exp = 'div_mod' + ', model: ' + h_val + ' wanted: ' + hl_val
        else:
            exp = h_type + ', model: ' + h_val + ' wanted: ' + hl_val
    elif ((h_type == 'var' and hl_type == 'number')
              or (h_type == 'number' and hl_type == 'var')):
        exp = 'num_var, model: ' + h_val + ' wanted: ' + hl_val
    else:
        exp = 'type_diff, model: ' + h_val + ' wanted: ' + hl_val
    # print ('h_val: ' + h_val + ' hl_val: ' + hl_val)
    # print ('h_type: ' + h_type + ' hl_type: ' + hl_type)
    # print ('result: ' + exp)
    return [False, [exp]]


def opposite_cond(h_val, hl_val):
    return (( ((h_val == '>') or (h_val == '>=')) and ((hl_val == '<') or (hl_val == '<=')) )
            or ( ((h_val == '<') or (h_val == '<=')) and ((hl_val == '>') or (hl_val == '>=')) ))

def allmost_same_cond(h_val, hl_val):
    return ((h_val == '>' and hl_val == '>=')
            or (h_val == '<' and hl_val == '<=')
                or (h_val == '>=' and hl_val == '>')
                    or (h_val == '<=' and hl_val == '<'))

def combine_two_returns_and(to_return_1, to_return_2):
    # print(to_return_1)
    # print(to_return_2)
    if (to_return_1[0] and to_return_2[0]):
        return [True, '', to_return_2[2] + to_return_1[2]]
    elif (to_return_1[0]):
        return to_return_2
    elif (to_return_2[0]):
        return to_return_1
    else:
        return [False, to_return_1[1] + to_return_2[1], to_return_1[2] + to_return_2[2]]

def get_to_return_not_same_side(h_tree_line, hl_tree_line, depth):
    to_return_right_left = compare_lines(h_tree_line.right, hl_tree_line.left, depth)
    to_return_left_right = compare_lines(h_tree_line.left, hl_tree_line.right, depth)
    return combine_two_returns_and(to_return_right_left, to_return_left_right)

def get_to_return_4_combinations(h_tree_line, hl_tree_line, depth):
    to_return_same_side = get_to_return_same_side(h_tree_line, hl_tree_line, depth)
    if (to_return_same_side[0]):
        return to_return_same_side

    to_return_not_same_side = get_to_return_not_same_side(h_tree_line, hl_tree_line, depth)
    if (to_return_not_same_side[0]):
        return to_return_not_same_side

    return combine_two_returns_or(to_return_same_side, to_return_not_same_side)

def combine_two_returns_or(to_return_1, to_return_2):
    worst_type1 = get_worst_or_best_type(map(lambda x: x.split(',')[0], [item for sublist in [to_return_1] for item in sublist[1]]))
    worst_type2 = get_worst_or_best_type(map(lambda x: x.split(',')[0], [item for sublist in [to_return_2] for item in sublist[1]]))
    if (types_with_victory.index(worst_type1) > types_with_victory.index(worst_type2)):
        return to_return_1
    else:
        return to_return_2


def get_to_return_same_side(h_tree_line, hl_tree_line, depth):
    to_return_right = compare_lines(h_tree_line.right, hl_tree_line.right, depth)
    to_return_left = compare_lines(h_tree_line.left, hl_tree_line.left, depth)
    return combine_two_returns_and(to_return_right, to_return_left)


def make_to_return(compared_nodes, continued_tree, depth):
    return [False, compared_nodes[1] + ([] if continued_tree[1] == '' else continued_tree[1]), [depth] + continued_tree[2]]


def compare_lines(h_tree_line, hl_tree_line, depth):
    to_return = []
    if(h_tree_line == None or hl_tree_line == None):
        return [h_tree_line == hl_tree_line, [], [depth]]
    else:
        compared_nodes = compare_node(h_tree_line.value, hl_tree_line.value)
        if(compared_nodes[0]):
            if (is_var(h_tree_line.value)):
                to_return = [True, [], [depth]]
            elif (is_number(h_tree_line.value)):
                to_return = [True, [], [depth]]
            elif (h_tree_line.value == special_bracket_close):
                to_return = [True, [], [depth]]
            elif (loops.__contains__(h_tree_line.value) or ifs.__contains__(h_tree_line.value)):
                to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
            elif (opers.__contains__(hl_tree_line.value)):
                if (non_komotative_opers.__contains__(hl_tree_line.value)):
                    to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
                    if (not to_return[0]):
                        not_same_side = [False,['wrong_sides_oper, ' + hl_tree_line.value]]
                        check_wrong_sides = make_to_return(not_same_side, get_to_return_not_same_side(h_tree_line, hl_tree_line, depth + 1), depth)
                        to_return = combine_two_returns_or(to_return, check_wrong_sides)
                else:
                    to_return = get_to_return_4_combinations(h_tree_line, hl_tree_line, depth + 1)
            elif (h_tree_line.value == equal or conditions.__contains__(h_tree_line.value)):
                if (h_tree_line.value == '=='):
                    to_return = get_to_return_4_combinations(h_tree_line, hl_tree_line, depth + 1)
                else:
                    to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
            elif (short_opers.__contains__(h_tree_line.value)):
                if (h_tree_line.get_left() is not None) and is_var(h_tree_line.get_left().value):
                    to_return = compare_lines(h_tree_line.get_left(), hl_tree_line.get_left(), depth + 1)
                else:
                    to_return = compare_lines(h_tree_line.get_right(), hl_tree_line.get_right(), depth + 1)
            elif (h_tree_line.value == special_bracket_start):
                to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
            elif (h_tree_line.value == line_separator):
                to_return = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)

        elif (not compared_nodes[1][0].__contains__('type_diff')):
            if (opposite_cond(h_tree_line.value, hl_tree_line.value)):
                continue_with_mistake = make_to_return(compared_nodes, get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1), depth)
                try_opposite_cond = get_to_return_not_same_side(h_tree_line, hl_tree_line, depth + 1)
                if (try_opposite_cond[0]):
                    to_return = try_opposite_cond
                else:
                    to_return = combine_two_returns_or(continue_with_mistake, try_opposite_cond)
            elif (allmost_same_cond(h_tree_line.value, hl_tree_line.value)):
                continued_tree = get_to_return_same_side(h_tree_line, hl_tree_line, depth + 1)
                to_return = make_to_return(compared_nodes, continued_tree, depth)
            elif (opers.__contains__(hl_tree_line.value)):
                continued_tree = get_to_return_4_combinations(h_tree_line, hl_tree_line, depth + 1)
                to_return = make_to_return(compared_nodes, continued_tree, depth)
            elif (short_opers.__contains__(h_tree_line.value)):
                if (h_tree_line.get_left() is not None) and is_var(h_tree_line.get_left().value):
                    continued_tree = compare_lines(h_tree_line.get_left(), hl_tree_line.get_left(), depth + 1)
                    to_return = make_to_return(compared_nodes, continued_tree, depth)
                else:
                    continued_tree = compare_lines(h_tree_line.get_right(), hl_tree_line.get_right(), depth + 1)
                    to_return = make_to_return(compared_nodes, continued_tree, depth)
            else:
                to_return = [False, compared_nodes[1], [depth]]
        else:
            to_return = [False, compared_nodes[1], [depth]]

    # print 'h_tree_line: ' + h_tree_line.__str__()
    # print 'h value: ' + h_tree_line.value
    # print 'hl_tree_line: ' + hl_tree_line.__str__()
    # print 'hl value: ' + hl_tree_line.value
    # print to_return

    return to_return


def get_beanches_nums_diffs(h_tree, hl_tree):
    to_return = []
    for branch_type in branch_types:
        h_branch_num = sum(map(lambda x: x.get_branch_number(branch_type), h_tree))
        hl_branch_num = sum(map(lambda x: x.get_branch_number(branch_type), hl_tree))
        if (not h_branch_num == hl_branch_num):
            to_return.append([branch_type + '_num', str(h_branch_num), str(hl_branch_num)])
    return to_return

def compare_trees(h_tree, hl_tree):
    to_return = []
    for x in range(min(h_tree.__len__(),hl_tree.__len__())):
        h_tree_line = h_tree[x]
        hl_tree_line = hl_tree[x]

        # print compare_lines(h_tree_line, hl_tree_line, 0)
        compared_line = compare_lines(h_tree_line, hl_tree_line, 0)

        if(not compared_line == []):
            if (not hl_tree_line.get_nodes_num() == h_tree_line.get_nodes_num()):
                compared_line = make_to_return(
                    ['', ['nodes_num, missing: ' + str(hl_tree_line.get_nodes_num() - h_tree_line.get_nodes_num()) + ' levels']], compared_line, 0)
            to_return.append(compared_line)

    branches_nums_diffs = get_beanches_nums_diffs(h_tree, hl_tree)
    for num_diffs in branches_nums_diffs:
        to_return.append([False, [num_diffs[0] + ', model num: ' + num_diffs[1] + ' origin: ' + num_diffs[2]], [0]])

    if (not h_tree.__len__() == hl_tree.__len__()):
        to_return.append([False, ['lines, diff. model: ' + str(h_tree.__len__()) + 'origin: ' + str(hl_tree.__len__())], [0]])

    return to_return


def get_worst_or_best_type(error_types, get_worst=True):
    types_to_use = types if get_worst else types[::-1]
    if not get_worst and error_types.__contains__('victory!!'):
        return 'victory!!'
    for type in types_to_use:
        if error_types.__contains__(type):
            return type
    return 'victory!!'


def calculate_hl_stats(hl):
    normal_order_hl = postOrderUtil.parse(hl)[1].c()
    hl_tree = from_list_to_tree(normal_order_hl.split(' '))
    stats = []

    nodes_nums = map(lambda x: x.get_nodes_num(), hl_tree)
    depths = map(lambda x: x.get_depth(), hl_tree)
    stats.append(sum(nodes_nums))
    stats.append(sum(depths))
    stats.append(max(nodes_nums))
    stats.append(max(depths))
    stats.append(0) # mistake_line
    stats.append(0) # mistake_depth
    stats.append(hl_tree.__len__())
    stats.append(normal_order_hl.count(ifs[1]))
    stats.append(normal_order_hl.count(ifs[0]))
    stats.append(normal_order_hl.count(loops[0]))
    return stats

def writeMisMatches_hl(i, failed_dataset, h, hl):
    normal_order_h = postOrderUtil.parse(h)[1].c()
    normal_order_hl = postOrderUtil.parse(hl)[1].c()
    h_tree = from_list_to_tree(normal_order_h.split(' '))
    hl_tree = from_list_to_tree(normal_order_hl.split(' '))
    compared_trees = compare_trees(h_tree, hl_tree)
    to_write_in_csv_origin_hl = ' ; '.join(map(lambda x: str(x), hl_tree))
    to_write_in_csv_models_h = ' ; '.join(map(lambda x: str(x), h_tree))
    error_types = []
    first_line_mistaken = 0
    first_depth_mistaken = 0
    j = 0
    for compared_line in compared_trees:
        if not compared_line == []:
            error_types += map(lambda x: x.split(',')[0], compared_line[1])
            if (first_line_mistaken == 0 and not compared_line[0]):
                first_line_mistaken = j
                first_depth_mistaken = min(compared_line[2])
            j += 1

    worst_type = get_worst_or_best_type(error_types)
    with open(failed_dataset + 'understand_fails.csv', 'a') as f:
        csv.writer(f).writerow([str(i), to_write_in_csv_origin_hl, to_write_in_csv_models_h, str(compared_trees), str(error_types), str(first_line_mistaken), str(first_depth_mistaken), worst_type])


def one_percentile(df, percentage):
    titles = ['total_nodes_num', 'total_depth', 'largest_nodes_num', 'largest_depth', 'lines_num', 'mistake_line', 'mistake_depth', 'ifs_num', 'else_num', 'loops_num']
    percentile = [str(percentage)]
    for title in titles:
        percentile.append(str(numpy.percentile(df[title], percentage)))
    return percentile

def calculate_all_percentiles(df):
    to_return = [one_percentile(df, 0)]
    to_return.append(one_percentile(df, 10))
    to_return.append(one_percentile(df, 50))
    to_return.append(one_percentile(df, 75))
    to_return.append(one_percentile(df, 90))
    to_return.append(one_percentile(df, 100))
    return to_return


def analize_mistakes(failed_dataset, fails_num):
    # create mistakes CSV
    data_path = failed_dataset + 'understand_fails.csv'
    df = pd.read_csv(data_path)
    worst_types = df[['sentence_id', 'worst_type']]
    ids = numpy.unique(worst_types['sentence_id'])
    times_dict = {}
    for id in ids:
        type = get_worst_or_best_type((worst_types.loc[worst_types['sentence_id'] == id])['worst_type'].values, False)
        if type not in times_dict.keys():
            times_dict[type] = {}
            times_dict[type]['times'] = 1
        else:
            times_dict[type]['times'] += 1
    if(ids.__len__() < fails_num):
        times_dict['compile_err'] = {}
        times_dict['compile_err']['times'] = fails_num - ids.__len__()

    for type in times_dict.keys():
        times_dict[type]['percentage'] = float(times_dict[type]['times']) / float(fails_num)

    with open(failed_dataset + 'mistakes_stats.csv', 'wb') as f:
        w = csv.writer(f)
        w.writerow(times_dict.keys())
        w.writerow(map(lambda x: x['times'], times_dict.values()))
        w.writerow(map(lambda x: x['percentage'], times_dict.values()))

    # create Tree's CSV
    data_path = failed_dataset + 'trees_stats.csv'
    df = pd.read_csv(data_path)
    titles = ['percentile', 'total_nodes_num', 'total_depth', 'largest_nodes_num', 'largest_depth', 'lines_num', 'mistake_line', 'mistake_depth', 'ifs_num', 'else_num', 'loops_num']
    with open(failed_dataset + 'analyzed_tree_stats.csv', 'wb') as f:
        w = csv.writer(f)
        w.writerow(titles)
        w.writerow(['all sentences'])
        w.writerows(calculate_all_percentiles(df))
        w.writerow(['only failed'])
        w.writerows(calculate_all_percentiles(df[(df.is_successful == False)]))
        w.writerow(['only success'])
        w.writerows(calculate_all_percentiles(df[(df.is_successful == True)]))

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

def get_branch_end(h_list):
    open_brackets = 1
    i = h_list.index(special_bracket_start) + 1

    for word in h_list[h_list.index(special_bracket_start) + 1:]:
        i += 1
        if (word == special_bracket_start):
            open_brackets += 1
        elif (word == special_bracket_close):
            open_brackets -= 1
        if (open_brackets == 0):
            return i

def get_cut_index_loop(h_list):
    return get_branch_end(h_list)

def get_cut_index_branch(h_list):
    index = get_branch_end(h_list)
    if (h_list[index] == ifs[0]):
        index += get_branch_end(h_list[index:])

    return index

if __name__ == "__main__":
    # h_sentence = '( X1 + 5 ) - 6 ;'
    # h_tree = from_list_to_tree(h_sentence.split(' '))
    # print h_tree[0]
    # exit (0)
    h_post_order = '96 X11 0 - + 33 / 86 / X0 % X13 36 + X6 * 29 / % X13 ='
    hl_post_order = '96 X11 0 - + 33 / 86 / X0 % X13 36 + X6 * 29 / % X13 ='
    # h_post_order = '18 X7 ='
    # hl_post_order = '18 X7 ='
    # h_post_order_list = h_post_order.split(' ')
    # hl_post_order_list = hl_post_order.split(' ')
    #
    # print find_first_difference(h_post_order_list, hl_post_order_list)

    # h_sentence = postOrderUtil.parse(h_post_order)[1].c()
    # hl_sentence = postOrderUtil.parse(hl_post_order)[1].c()

    h_sentence = 'if ( X14 >= -- X13 ) { X6 = X9 -- ; } '
    hl_sentence = 'if ( -- X13 < X14 ) { X6 = X9 -- ; } '

    # h_sentence = 'if ( 80 >= X2 ) { X11 = 5 ; X12 = 6 } ;'

    # print from_list_to_tree(hl_sentence.split(' '))[0]
    # print from_list_to_tree(hl_sentence.split(' '))[1]
    # exit(0)
    # h_sentence = postOrderUtil.parse('X5 X8 ++X 21 % N11 + + X5 + X0 X-- * X12 ++X != COND X6 ++X N7 * X7 51 - N2 X14 X10 % N4 * % / - X0 = WHILE')[1].c()
    # hl_sentence = postOrderUtil.parse('X5 X++ X8 ++X X10 --X / > COND X3 N5 + X7 X++ X1 * - X14 = TRUE IF X5 X-- 2 + N3 N8 X4 67 / X3 / % / - X13 = X5 X++ X12 = N2 X14 --X >= COND X5 X-- X5 / X14 X12 * X0 X4 - X4 56 / / / * X11 = X8 --X X11 ++X X13 X-- / % X2 = WHILE N18 X3 / X7 / N10 + N12 X11 --X + + X11 =')[1].c()



    h_tree = from_list_to_tree(h_sentence.split(' '))
    hl_tree = from_list_to_tree(hl_sentence.split(' '))
    print h_tree[0]
    print hl_tree[0]
    compared_line = compare_lines(h_tree[0], hl_tree[0], 0)
    if (not compared_line == []):
        if (not hl_tree[0].get_nodes_num() == h_tree[0].get_nodes_num()):
            compared_line = make_to_return(
                ['', ['nodes_num, missing: ' + str(hl_tree[0].get_nodes_num() - h_tree[0].get_nodes_num()) + ' levels']],
                    compared_line, 0)
    print compared_line
    exit (0)
    compared_trees = compare_trees(h_tree, hl_tree)
    print compared_trees
    error_types = map(lambda x: x.split(',')[0], [item for sublist in compared_trees for item in sublist[0]])
    print min(map(lambda x: x[1], compared_trees))
    print error_types
    print compared_trees
    # lines = (from_list_to_tree('while ( ( ( X13 ++ % X13 ) % ( ( N8 % X13 ) / X2 -- ) ) >= ( N16 / ( ( X7 * ( N13 + X0 ) ) % X13 ) ) ) { X7 = N2 ; X10 = X2 + ( ( X13 / -- X4 ) + X1 ) ; } ; X7 = -- X9 ; if ( X14 <= ( -- X6 + X6 ++ ) ) { X2 = N14 * ( X4 ++ / ( ( X8 - X1 ) - X11 ) ) ; X11 = ( ( X0 - ( N0 - X8 ) ) * ( N12 * ( X1 + N3 ) ) ) % ( ( 28 * ( N15 + X11 ) ) / ( N11 % -- X6 ) ) ; } else { X6 = N18 - ( ( N7 % X5 ) % -- X13 ) ; } ; X13 = ( 21 * X14 ) * N16 ; if ( 7 > ( -- X1 - X7 -- ) ) { X0 = N6 ; } ;'.split(' ')))
    # for line in lines:
    #     print line

