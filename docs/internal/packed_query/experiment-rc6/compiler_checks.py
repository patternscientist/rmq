from machine import SubroutineCompiler,run


def check(source,expected):
    p=SubroutineCompiler(source,{}).compile()
    r=run(p,[],16,0,0)
    assert r['resultTag']==expected,(expected,r)


check('''
def bump():
    global G
    G = 2
    return 3
def query(left,right):
    global G
    G = 1
    return G + bump()
''',4)

check('''
def bump():
    global G
    G = 8
    return 3
def combine(a,b):
    return a * 10 + b
def query(left,right):
    global G
    G = 1
    return combine(G,bump())
''',13)

check('''
def f(x):
    return x + 1
def g(x):
    a = f(x)
    b = f(a)
    return a * 10 + b
def query(left,right):
    a = g(2)
    b = g(3)
    return a * 100 + b
''',3445)

check('''
def query(left,right):
    x = 3
    while x < 17:
        x = x * 2
    return (2 - 3) + (x >> 2)
''',6)
print('COMPILER EDGE CHECKS PASS')
