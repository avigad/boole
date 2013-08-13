################################################################################
#
# model_examples.py
#
################################################################################

from boole.core.model import *
        
################################################################################
#
# Examples
#
################################################################################

if __name__ == '__main__':

    x, y, z = Int('x y z')
    p, q, r, s = Bool('p q r s')
    People = EnumType('People', ['Alice', 'Bob', 'Carol'])
    Alice, Bob, Carol = People.make_constants()
    u1, u2, u3, u4, u5 = People('u1 u2 u3 u4 u5')
    
    def check(e, *models):
        print 'Expression:', e
        try:
            val = val_strict(e, *models)
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
    check(Forall(u1, (u1 == Alice) | (u1 == Bob) | (u1 == Carol)))
    check(Forall(u1, (u1 == Alice) | (u1 == Bob)))
    check(true != true)
    check(Exists([u1, u2, u3, u4], And(u1 != u2, u1 != u3, u1 != u4, 
          u2 != u3, u2 != u4, u3 != u4)))
    check(true & (false >> true))
    check(true & ~(false >> true))
    check(Abs([x, y], x + y)(ii(5), ii(7)))
    check(Exists(p, p))
    e = Exists([p, q, r], (p >> q & r) & ~(r >> p & q))
    check(e)
    print 'Witness:', e.witness
    print 
    check(Forall([p,q], Exists(r, p >> r & q >> ~r)))
    check(Forall([p,q], (((p >> q) >> p) >> p)))
    print
    
    a, b, c = Int('a, b, c')
    Even = Const('Even', Int >> Bool)
    Prime = Const('Prime', Int >> Bool)
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

    M = Model({(a, 5), (b, 2), (c, 7)})
    # TODO: this next assignment is convenient. Is it kosher?
    M[Int] = dom_range(0,20)
    M[Even] = lambda x: x % 2 == 0
    M[Prime] = is_prime
    M[suc] = lambda x: x + 1
    M[square] = lambda x: x * x
    
    print "Model M:"
    print
    M.show()
    print
    
    def checkM(e): check(e, M)
    
    checkM(a)
    checkM(a + b * c)
    checkM(a + x)
    checkM(Exists(x, b + x == c))
    checkM(Even(a))
    checkM(Prime(ii(23)))
    checkM(Prime(ii(22)))
    checkM(And(Prime(a), Prime(b), Prime(c)))
    checkM(Even(c) | And(Prime(a), Prime(b), Prime(c)))
    checkM(Even(c) | And(Prime(suc(a)), Prime(suc(b)), Prime(c)))
    checkM(Exists(x, Even(x)))
    checkM(Exists(x, And(Prime(x), Even(x))))
    checkM(Exists(x, And(Prime(x), Even(x), c < x)))
    checkM(Exists([x, y], And(Prime(x), Prime(y), x < y)))
    checkM(Exists([x, y], And(Prime(x), Prime(y), x !=  y)))
    checkM(Exists([x, y], And(Prime(x), Prime(y), x < y, Even(y))))
    checkM(Exists([x, y], And(Prime(x), Prime(y), x < y, Even(x))))
    checkM(Forall(x, Even(x)))
    checkM(Forall(x, Or(Even(x), ~Even(x))))
    checkM(Forall(x, Even(x) >> ~Even(suc(x))))
    checkM(Forall(x, Even(x) >> Even(square(x))))
    checkM(Exists(x, And(Even(x), ~Even(square(x)))))
    checkM(Forall(x, Even(square(x)) >> Even(x)))
    checkM(Forall([x, y], And(Prime(x), Prime(y), x < y) >> Even(x)))
    checkM(Forall([x, y], And(Prime(x), Prime(y), x < y) >> ~Even(y)))
    checkM(Forall(x, Exists(y, x < y)))
    checkM(Forall([x, y], x < y >>  Exists(z, And(x < z, z < y))))
    checkM(Forall([x, y], And(Even(x), Even(y), x < y) >> 
        Exists(z, (x < z) & (z < y))))
    checkM(Exists(x, (x < ii(10)) & Forall(y, (x < y) & Prime(y) >> ~Even(y))))

    def precond(n):
        return (ii(2) < n) & Even(n)
    
    def goldbach(n):
        return precond(n) >> Exists([x,y], Prime(x) & Prime(y) & (x + y == n))
    
    Goldbach = Forall(z, goldbach(z))
    checkM(Goldbach)
