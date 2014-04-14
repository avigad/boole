################################################################################
#
# z3_examples.py
#
# Author:
# Jeremy Avigad
#
################################################################################

from boole import *
from boole.interfaces.z3_interface import *


def test0():
    
    x, y, z = Real('x, y, z')
    i, j, k = Int('i, j, k')
    p, q, r = Bool('p, q, r')
    f = (Real >> Real)('f')
    Beatles, (John, Paul, George, Ringo) = \
        defenum('Beatles', ['John', 'Paul', 'George', 'Ringo'])
    Likes = (Beatles >> (Beatles >> Bool))('Likes')
    
    T1 = Boole_to_Z3()
    T2 = Z3_to_Boole(current_ctxt())
    
    def test(expr):
        print 'Boole expression:', expr
        e1 = T1(expr)
        print 'Translated to Z3:', e1
        e2 = T2(e1)
        print 'Translated back:', e2
        print
        
    test(p)
    test(And(p,q))
    test(And(p, q, Not(r)))
    test(x + y)
    test(x + y + 3)
    test(f(x + y) + f(f(x)))
    test((x + y) * (i + j))
    test(And((x + y) <= f(x), Not(y < z)))
    test(forall(x, x == x))
    test(forall([x, y], exists(z, x + z == y)))
    test(implies([p, q], Or(r, (x == 7))))  
    test(John)
    test(Likes(John, Paul))
    
    S = Z3_Solver()
    S.add(implies([p, q], Or(r, (x == 7))))
    S.add(And(p, q))
    S.add(Not(r))
    if (S.check()):
        print S.z3_model()


def test1():
    
    p, q, r, s, t, u = Bool('p q r s t u')
    x, y, z = Real('x y z')
    
    formula = Not(implies(And(p, Or(q, Not(r))), And(p, q, Not(r), x == y)))
    print 'Formula: ', formula
    
    s = Z3_Solver()
    s.add(formula)
    print 'Check: ', s.check()
    print 'Model: ', s.z3_model()
    
    
def test2():
    
    Men, (Alex, Bill, Charles)= defenum('Men', ('Alex', 'Bill', 'Charles'))
         
    Likes = (Men >> (Men >> Bool))('Likes')
    x, y, z = Men('x y z')
    
    s = Z3_Solver()
    s.add(Likes(x, Bill))
    print 'Check: ', s.check()
    print 'Model: ', s.z3_model()
    
    
def test3():

    x = Real('x')
    p = x ** 2 + 1.01
    q = 0.1 * x ** 3
    print p
    print q

    s = Z3_Solver()
    s.add(q > p)
    print 'Check: ', s.check()
    print 'Model: ', s.z3_model()


# tall, dark, and handsome puzzle
def test4():
    
    Men, (Alec, Bill, Carl, Dave) = \
        defenum('Men', ('Alec', 'Bill', 'Carl', 'Dave'))
    tall, dark, handsome = (Men >> Int)('tall, dark, handsome')
    ideal = Men('ideal')
    x = Men('x')
    
    s = Z3_Solver()
    s.add(forall(x, Or(tall(x) == 0, tall(x) == 1)))
    s.add(forall(x, Or(dark(x) == 0, dark(x) == 1)))
    s.add(forall(x, Or(handsome(x) == 0, handsome(x) == 1)))
    s.add(tall(Alec) + tall(Bill) + tall(Carl) + tall(Dave) == 3)
    s.add(dark(Alec) + dark(Bill) + dark(Carl) + dark(Dave) == 2)
    s.add(handsome(Alec) + handsome(Bill) + handsome(Carl) + handsome(Dave) == 1)
    s.add(forall(x, Or(tall(x) == 1, dark(x) == 1, handsome(x) == 1)))
    s.add(dark(Alec) == dark(Dave))   
    s.add(tall(Bill) == tall(Carl))
    s.add(tall(Carl) != tall(Dave))
    s.add(And(tall(ideal) == 1, dark(ideal) == 1, handsome(ideal) == 1))
    
    print 'Check:', s.check()
    print 'Model: ', s.z3_model()

def test5():

    Person = deftype('Person')
    Liar = defconst('Liar', Person >> Bool)
    Says = defconst('Says', Person >> (Bool >> Bool))
    x = Person('x')
    p = Bool('p')
    lies = forall([x, p], implies([Liar(x), Says(x, p)], Not(p)))
    truth = forall([x, p], implies([Not(Liar(x)), Says(x, p)], p))
    # defhyp('lies', forall(x, implies([Liar(x), Says(x, p)], Not(p))))
    knave = defconst('knave', Person)
    # paradox = Says(knave, Liar(knave))
    s = Z3_Solver()
    s.add(lies)
    s.add(truth)
    # s.add(paradox)

    knight = defconst('knight', Person)
    puzzle = Says(knight, Says(knave, Liar(knight)))
    s.add(puzzle)
    s.add(Not(Liar(knight)))

    print 'Check:', s.check()
    print 'Model: ', s.z3_model()

    B = Z3_to_Boole()
    b_mod = B.model(s.z3_model())
    #TODO: make the names correspond!
    print b_mod


    
if __name__ == '__main__':

    print '******'
    print 'Test0:'
    print '******'
    test0()
    print
    
    # print '******'
    # print 'Test1:'
    # print '******'
    # test1()
    # print
    
    # print '******'
    # print 'Test2:'
    # print '******'
    # test2()
    # print

    # print '******'
    # print 'Test3:'
    # print '******'
    # test3()
    # print
    
    # print '******'
    # print 'Test4:'
    # print '******'
    # test4()
    # print        
        
    print '******'
    print 'Test5:'
    print '******'
    test5()
    print        
    
    
