
class Node:
    def __init__(self, value):
        self.value = value
        self.left = None
        self.right = None

    def set_right(self, right_tree):
        self.right = right_tree

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

    def __str__(self):
        right_side = self.right.__str__() if (self.right != None) else ''
        left_side = self.left.__str__() if (self.left != None) else ''
        return left_side + ' ' + self.value + ' ' + right_side
