import os
def cleanup(dir):
    if os.path.exists(dir):
        map(lambda y:os.remove(os.path.join('out',y)), filter(lambda x:x.endswith('.c') or x.endswith('.ll'), [f for f in os.listdir(dir)]))
        os.rmdir(dir)

if __name__ == "__main__":
    cleanup('out')