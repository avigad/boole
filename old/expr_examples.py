################################################################################
#
# expr_examples.py
#
################################################################################

from boole.core.model import *
        
################################################################################
#
# Examples
#
################################################################################

if __name__ == '__main__':
 
    print "Built-in language:"
    print
    built_in_language.show()
    print
       
    i, j, k = Int('i j k')
    x = Const('x', Real)
    y, z = Real('y, z')
    p, q, r = Bool('p q r')    
    A = BasicType('A')
    B = BasicType('B')
    f = (A >> B)('f')
    g = Const('g', A * A >> B)
    a1, a2 = A('a1 a2')

    print 'Global language:'
    print
    global_language.show()
    print
    
    def check(e):
        print 'Expression:', e
        try:
            etype = e.etype()
        except TypeError as err:
            print 'Type error:', err
        else:
            print 'Type:', etype
        print
        
    check(j)
    check(i + j)
    check(x)
    check(x + i)
    check(i + rr(4.2))
    check(f(a1))
    check(f(a1, a2))
    check(g(a1))
    check(g(a1, a2))
    check(ii(42))
    check(rr(42))
    
    adder = Abs([i, j], i + j)
    check(adder)
    check(adder(i, ii(3)))
    
    check(plus)
    check(x ** ii(2) + ii(3) * x + ii(7))
    check(j ** ii(2) + ii(3) * j + ii(7))
    check(Sum(x ** ii(2), ii(3) * x, ii(7)))
    check(Sum(j ** ii(2), ii(3) * j, ii(7)))
    check((x * rr(3.0) >= ii(17)) & (p | q))
    check(x + p)
    check(p & q)
    check(And(p,q))
    check(And(p, q, r))
    check(~And(p, ~q, (r | p)))
    check(Forall(x, x == x))
    check(Forall([x, y], x == y))
    check(Exists([x, y], (rr(0) < x) & (x + y < rr(3))))

    L = Language()
    set_default_language(L)
    m, n, p, q = Int('m n p q')
    prime = Const('Prime', Int >> Bool)
    even = Const('Even', Int >> Bool)   
    f = (Int >> Int)('f') 
    People = EnumType('People', ['Alice', 'Bob', 'Cathy'])
    Alice, Bob, Cathy = People.make_constants()
    x = People('x')

    print 'Language L:'
    print
    L.show()
    print

    
    check (Forall([f, m, n], f(m) == f(n)))
    
    def precond(n):
        return (ii(2) < n) & even(n)
    
    def goldbach(n):
        return Exists([p,q], (precond(n)) >> 
                      (prime(p) & prime(q) & (p + q == n)))
    
    Goldbach = Forall(n, goldbach(n))
    check(Goldbach)
    
    check(Forall(x, (x == Alice) | (x == Bob) | (x == Cathy)))
    check(Forall(x, (x == Alice) | (x == Bob)))
