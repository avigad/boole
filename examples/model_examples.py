################################################################################
#
# model_examples.py
#
# authors:
# Jeremy Avigad
#
################################################################################

from boole.elab.prelude import *
from boole.semantics.value import *
from boole.elab.terms import ii, rr
        
################################################################################
#
# Examples
#
################################################################################

if __name__ == '__main__':

    x, y, z = Int('x y z')
    p, q, r, s = Bool('p q r s')
    People, (Alice, Bob, Carol) = defenum('People', ['Alice', 'Bob', 'Carol'])
    u1, u2, u3, u4, u5 = People('u1 u2 u3 u4 u5')
    
    def check(e, model=None):
        print 'Expression:', e
        try:
            val = eval_expr(elab(e), model)
        except Exception as err:
            print 'Error in evaluation:', err
        else:
            print 'Value:', val
        # print 'Value:', val_strict(e, *models)
        print
        
    # these do not require any model
    
    check(ii(3))
    check(rr(4.5))
    check(-ii(3) + rr(4.5) * ii(2))
    check(Alice)
    check(Bob)
    # check(x)
    # check(Alice + x)
    # check(x + y)
    check(forall(u1, Or(u1 == Alice, u1 == Bob, u1 == Carol)))
    check(forall(u1, Or(u1 == Alice, u1 == Bob)))
    check(true != true)
    check(exists([u1, u2, u3, u4], And(u1 != u2, u1 != u3, u1 != u4,
          u2 != u3, u2 != u4, u3 != u4)))
    check(And(true, implies(false, true)))
    check(And(true, Not(implies(false, true))))
    check(abst([x, y], x + y)(ii(5), ii(7)))
    check(exists(p, p))
    e = exists([p, q, r], And(implies(p, And(q,r)), Not(implies(r, And(p, q)))))
    check(e)
#    print 'Witness:', e.witness
#    print
    check(forall([p,q], exists(r, implies([p, And(r, q)], Not(r)))))
    check(forall([p,q], implies(implies(implies(p, q), p), p)))
    print

    Int = deftype('Int')
    a, b, c = Int('a, b, c')
    even = defconst('even', Int >> Bool)
    prime = defconst('prime', Int >> Bool)
    suc, square = (Int >> Int)('suc, square')
    
    def is_prime(x):
        if x == 0 or x == 1:
            return False
        elif x == 2:
            return True
        else:
            for i in range(2, x):
                if x % i == 0:
                    return False
            return True

    M = Model({}, { 'a' : Value(5), 'b' : Value(2), 'c' : Value(7)})
    # TODO: this next assignment is convenient. Is it kosher?
    M.vals['Int'] = Value(range(20))
    M.vals['even'] = Value(lambda x: x % 2 == 0)
    M.vals['prime'] = Value(is_prime)
    M.vals['suc'] = Value(lambda x: x + 1)
    M.vals['square'] = Value(lambda x: x * x)
    
    print "Model M:"
    print
    print M.vals
    print
    
    def checkM(e): check(e, M)
    
    checkM(a)
    checkM(a + b * c)
    checkM(a + x)
    checkM(exists(x, b + x == c))
    checkM(even(a))
    checkM(prime(23))
    checkM(prime(22))
    checkM(And(prime(a), prime(b), prime(c)))
    checkM(Or(even(c),And(prime(a), prime(b), prime(c))))
    checkM(Or(even(c), And(prime(suc(a)), prime(suc(b)), prime(c))))
    checkM(exists(x, even(x)))
    checkM(exists(x, And(prime(x), even(x))))
    checkM(exists(x, And(prime(x), even(x), c < x)))
    checkM(exists([x, y], And(prime(x), prime(y), x < y)))
    checkM(exists([x, y], And(prime(x), prime(y), x !=  y)))
    checkM(exists([x, y], And(prime(x), prime(y), x < y, even(y))))
    checkM(exists([x, y], And(prime(x), prime(y), x < y, even(x))))
    checkM(forall(x, even(x)))
    checkM(forall(x, Or(even(x), Not(even(x)))))
    checkM(forall(x, implies(even(x), Not(even(suc(x))))))
    checkM(forall(x, implies(even(x), even(square(x)))))
    checkM(exists(x, And(even(x), Not(even(square(x))))))
    checkM(forall(x, implies(even(square(x)), even(x))))
    checkM(forall([x, y], implies([prime(x), prime(y), x < y], even(x))))
    checkM(forall([x, y], implies([prime(x), prime(y), x < y], Not(even(y)))))
    checkM(forall(x, exists(y, x < y)))
    checkM(forall([x, y], implies(x < y, exists(z, And(x < z, z < y)))))
    checkM(forall([x, y], implies([even(x), even(y), x < y], exists(z, And((x < z), (z < y))))))
    checkM(exists(x, And(x < 10, forall(y, And(x < y, implies(prime(y), Not(even(y))))))))

    def precond(n):
        return And((2 < n), even(n))
    
    def goldbach(n):
        return implies(precond(n), exists([x,y], And(prime(x), prime(y), (x + y == n))))
    
    Goldbach = forall(z, goldbach(z))
    checkM(Goldbach)
