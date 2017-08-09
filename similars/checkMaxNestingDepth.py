def process(c,ll,out):
    current = maximum = 0
    for w in c.split(' '):
        if w == '(':
            current += 1
        elif w == ')':
            current -= 1
        maximum = max(maximum,current)
    return maximum

def compare(ref,query):
    return ref == query