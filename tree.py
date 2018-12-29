
start_bracket = '('
close_bracket = ')'
special_bracket_start = '{'
special_bracket_close = '}'
brakets = [special_bracket_start, special_bracket_close,start_bracket,close_bracket]

have_conditions = ['if', 'while']

class Node:
    def __init__(self, value):
        self.value = value
        self.left = None
        self.right = None

    def set_right(self, right_tree):
        self.right = right_tree

    def get_value(self):
        return self.value

    def set_value(self, value):
        self.value = value

    def get_right(self):
        return self.right

    def set_left(self, left_tree):
        self.left = left_tree

    def get_left(self):
        return self.left

    def set_most_left(self, value):
        if (self.left == None):
            self.left = Node(value)
        else:
            self.left.set_most_left(value)

    def get_most_left(self):
        if (self.left == None):
            return self.value
        else:
            self.left.get_most_left()

    def set_most_right(self, value):
        if (self.right == None):
            self.right = Node(value)
        else:
            self.right.set_most_right(value)

    def get_most_right(self):
        if (self.right == None):
            return self.value
        else:
            self.right.get_most_right()

    def get_branch_number(self, branch):
        right_number = self.right.get_branch_number(branch) if self.right is not None else 0
        left_number = self.left.get_branch_number(branch) if self.left is not None else 0
        self_number = 1 if self.value == branch else 0
        return right_number + left_number + self_number

    def __str__(self):
        if (self.value in have_conditions):
            right_side = ' ' + self.right.__str__() if (self.right != None) else ''
            left_side = ' ' + self.left.__str__() if (self.left != None) else ''
            return self.value + left_side + right_side

        right_side = ' ' + self.right.__str__() if (self.right != None) else ''
        left_side = self.left.__str__() + ' ' if (self.left != None) else ''
        return left_side + self.value + right_side

    def get_depth(self):
        if self.get_value() == None:
            return 0
        depth_left = 0 if self.get_left() == None else self.get_left().get_depth()
        depth_right = 0 if self.get_right() == None else self.get_right().get_depth()
        return (1 if self.get_value() not in brakets else 0) + depth_left + depth_right
