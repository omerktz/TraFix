import os
map(lambda y:os.remove(y), filter(lambda x:x.endswith('.c') or x.endswith('.ll'), [f for f in os.listdir('.')]))