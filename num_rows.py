from z3 import Int, Solver, sat, Not, And
import math
from itertools import permutations

block = ['a', 'b', 'c', 'd']
varperm = list(permutations(list(range(5))))

def ivar(abcd, label):
    return Int(f'{abcd}{label}')

s = Solver()
for label in range(5):
    s.add(5*ivar('a', label) + 3*ivar('b', label) + 2*ivar('c', label) + 1*ivar('d', label) == 21)
s.add(ivar('a', 0) + ivar('a', 1) + ivar('a', 2) + ivar('a', 3) + ivar('a', 4) == 10)
s.add(ivar('b', 0) + ivar('b', 1) + ivar('b', 2) + ivar('b', 3) + ivar('b', 4) == 7)
s.add(ivar('c', 0) + ivar('c', 1) + ivar('c', 2) + ivar('c', 3) + ivar('c', 4) == 8)
s.add(ivar('d', 0) + ivar('d', 1) + ivar('d', 2) + ivar('d', 3) + ivar('d', 4) == 18)
s.add([ivar(abcd, label)>=0 for label in range(5) for abcd in block])

num_solutions = 0
while True:
    result = s.check()
    if result == sat:
        num_solutions = num_solutions + 1
        m = s.model()
        print()
        print(num_solutions)
        a = 10
        b = 7
        c = 8
        d = 18
        for label in range(5):
            model_ints = [m.eval(ivar(abcd, label)).as_long() for abcd in block]
            combinations = math.prod([math.comb(abcd, modelint) for abcd,modelint in zip([a,b,c,d], model_ints)])
            a = a - model_ints[0]
            b = b - model_ints[1]
            c = c - model_ints[2]
            d = d - model_ints[3]
            print(f'{label} 5*a={model_ints[0]} 3*b={model_ints[1]} 2*c={model_ints[2]} 1*d={model_ints[3]} combinations={combinations}')

        for perm in varperm:
            s.add(Not(And([ivar(abcd, perm[label]) == m.eval(ivar(abcd, label)).as_long() for label in range(5) for abcd in block])))
    else:
        break

#s.add(5*Int('a') + 3*Int('b') + 2*Int('c') + 1*Int('d') == 21)
#s.add(Int('a') >= 0)
#s.add(Int('a') <= 10)
#s.add(Int('b') >= 0)
#s.add(Int('b') <= 7)
#s.add(Int('c') >= 0)
#s.add(Int('c') <= 8)
#s.add(Int('d') >= 0)
#s.add(Int('d') <= 18)

#num_solutions = 0
#total_combinations = 0
#while True:
#    result = s.check()
#    if result == sat:
#        model = s.model()
#        a = model.eval(Int('a')).as_long()
#        b = model.eval(Int('b')).as_long()
#        c = model.eval(Int('c')).as_long()
#        d = model.eval(Int('d')).as_long()
#        #ten_choose_a = math.comb(10, a)
#        #seven_choose_b = math.comb(7, b)
#        #eight_choose_c = math.comb(8, c)
#        #eighteen_choose_d = math.comb(18, d)
#        #combinations = ten_choose_a * seven_choose_b * eight_choose_c * eighteen_choose_d
#        #print(f'{num_solutions} 5*a={a} 3*b={b} 2*c={c} 1*d={d} combinations={combinations}')
#        s.push()
#        s.add(Int('a') <= 10 - a)
#        s.add(Int('b') <= 7 - b)
#        s.add(Int('c') <= 8 - c)
#        s.add(Int('d') <= 18 - d)
#        result = s.check()
#        if result == sat:
#            model = s.model()
#            a = model.eval(Int('a')).as_long()
#            b = model.eval(Int('b')).as_long()
#            c = model.eval(Int('c')).as_long()
#            d = model.eval(Int('d')).as_long()
#            a2 = m
#
#        else:
#            s.pop()
#
#        s.add(Not(And(Int('a')==a, Int('b')==b, Int('c')==c, Int('d')==d)))
#        num_solutions = num_solutions + 1
#        total_combinations = total_combinations + combinations
#    else:
#        break
#
#print(f'num_solutions={num_solutions}')
#print(f'total_combinations={total_combinations}')
