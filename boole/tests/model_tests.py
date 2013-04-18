##################################################
#
# Tests for model.py
#
#
#
#
#
#
#
#
#
#
#
##################################################

from boole.core.model import *
from boole.core.language import clear_default_language
from nose.tools import *


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

def test_val_strict():
    #It is annoying that types can not be redefined: turn into a warning?
    clear_default_language()
    x, y, z = Int('x y z')
    p, q, r, s = Bool('p q r s')
    People = EnumType('People', ['Alice', 'Bob', 'Carol'])
    Alice, Bob, Carol = People.make_constants()
    u1, u2, u3, u4, u5 = People('u1 u2 u3 u4 u5')
    assert_equal(val_strict(ii(3)), 3)
    assert_equal(val_strict(rr(4.5)), 4.5)
    assert_equal(val_strict(-ii(3) + (4.5) * (2)), 6)
    assert_equal(val_strict(Alice), 'Alice')
    assert_equal(val_strict(Bob), 'Bob')

    assert(val_strict(Forall(u1, (u1 == Alice) | (u1 == Bob) | (u1 == Carol))))
    assert(not val_strict(Forall(u1, (u1 == Alice) | (u1 == Bob))))
    assert(not val_strict(true != true))
    assert(not val_strict(Exists([u1, u2, u3, u4], And(u1 != u2, u1 != u3, u1 != u4, 
          u2 != u3, u2 != u4, u3 != u4))))
    assert(val_strict(true & (false >> true)))
    assert(not val_strict(true & ~(false >> true)))
    assert(val_strict(Abs([x, y], x + y)((5), (7))))
    assert(val_strict(Exists(p, p)))
    e = Exists([p, q, r], (p >> q & r) & ~(r >> p & q))
    assert(val_strict(e))
    assert(not val_strict(Forall([p,q], Exists(r, p >> r & q >> ~r))))
    assert(val_strict(Forall([p,q], (((p >> q) >> p) >> p))))
    a, b, c = Int('a, b, c')
    Even = Const('Even', Int >> Bool)
    Prime = Const('Prime', Int >> Bool)
    suc, square = (Int >> Int)('suc, square')
    a, b, c = Int('a, b, c')
    Even = Const('Even', Int >> Bool)
    Prime = Const('Prime', Int >> Bool)
    suc, square = (Int >> Int)('suc, square')

    M = Model({(a, 5), (b, 2), (c, 7)})
    M[Int] = dom_range(0,20)
    M[Even] = lambda x: x % 2 == 0
    M[Prime] = is_prime
    M[suc] = lambda x: x + 1
    M[square] = lambda x: x * x
    
    
    assert_equal(val_strict(a, M), 5)
    assert_equal(val_strict(a + b * c, M), 19)
    assert(val_strict(Exists(x, b + x == c), M))
    assert(not val_strict(Even(a), M))
    assert(val_strict(Prime((23)), M))
    assert(not val_strict(Prime((22)), M))
    assert(val_strict(And(Prime(a), Prime(b), Prime(c)), M))
    assert(val_strict(Even(c) | And(Prime(a), Prime(b), Prime(c)), M))
    assert(not val_strict(Even(c) | And(Prime(suc(a)), Prime(suc(b)), Prime(c)), M))
    assert(val_strict(Exists(x, Even(x)), M))
    assert(val_strict(Exists(x, And(Prime(x), Even(x))), M))
    assert(not val_strict(Exists(x, And(Prime(x), Even(x), c < x)), M))
    assert(val_strict(Exists([x, y], And(Prime(x), Prime(y), x < y)), M))
    assert(val_strict(Exists([x, y], And(Prime(x), Prime(y), x !=  y)), M))
    assert(not val_strict(Exists([x, y], And(Prime(x), Prime(y), x < y, Even(y))), M))
    assert(val_strict(Exists([x, y], And(Prime(x), Prime(y), x < y, Even(x))), M))
    assert(not val_strict(Forall(x, Even(x)), M))
    assert(val_strict(Forall(x, Or(Even(x), ~Even(x))), M))
    assert(val_strict(Forall(x, Even(x) >> ~Even(suc(x))), M))
    assert(val_strict(Forall(x, Even(x) >> Even(square(x))), M))
    assert(not val_strict(Exists(x, And(Even(x), ~Even(square(x)))), M))
    assert(val_strict(Forall(x, Even(square(x)) >> Even(x)), M))
    assert(not val_strict(Forall([x, y], And(Prime(x), Prime(y), x < y) >> Even(x)), M))
    assert(val_strict(Forall([x, y], And(Prime(x), Prime(y), x < y) >> ~Even(y)), M))
    assert(not val_strict(Forall(x, Exists(y, x < y)), M))
    assert(not val_strict(Forall([x, y], x < y >>  Exists(z, And(x < z, z < y))), M))
    assert(val_strict(Forall([x, y], And(Even(x), Even(y), x < y) >> 
        Exists(z, (x < z) & (z < y))), M))

    def precond(n):
        return ((2) < n) & Even(n)
    
    def goldbach(n):
        return precond(n) >> Exists([x,y], Prime(x) & Prime(y) & (x + y == n))
    
    Goldbach = Forall(z, goldbach(z))
    assert(val_strict(Goldbach, M))

def test_val_non_strict():

    clear_default_language()
    x, y, z = Int('x y z')
    p, q, r, s = Bool('p q r s')
    People = EnumType('People', ['Alice', 'Bob', 'Carol'])
    Alice, Bob, Carol = People.make_constants()
    u1, u2, u3, u4, u5 = People('u1 u2 u3 u4 u5')
    assert_equal(val_non_strict(ii(3)), 3)
    assert_equal(val_non_strict(rr(4.5)), 4.5)
    assert_equal(val_non_strict(-(3) + (4.5) * ii(2)), 6)
    assert_equal(val_non_strict(Alice), 'Alice')
    assert_equal(val_non_strict(Bob), 'Bob')
    assert_equal(val_non_strict(x), None)

    assert(val_non_strict(Forall(u1, (u1 == Alice) | (u1 == Bob) | (u1 == Carol))))
    assert(not val_non_strict(Forall(u1, (u1 == Alice) | (u1 == Bob))))
    assert(not val_non_strict(true != true))
    assert(not val_non_strict(Exists([u1, u2, u3, u4], And(u1 != u2, u1 != u3, u1 != u4, 
          u2 != u3, u2 != u4, u3 != u4))))
    assert(val_non_strict(true & (false >> true)))
    assert(not val_non_strict(true & ~(false >> true)))
    assert(val_non_strict(Abs([x, y], x + y)((5), (7))))
    assert(val_non_strict(Exists(p, p)))
    e = Exists([p, q, r], (p >> q & r) & ~(r >> p & q))
    assert(val_non_strict(e))
    assert(not val_non_strict(Forall([p,q], Exists(r, p >> r & q >> ~r))))
    assert(val_non_strict(Forall([p,q], (((p >> q) >> p) >> p))))
    assert(val_non_strict(true | p))
    
    a, b, c = Int('a, b, c')
    Even = Const('Even', Int >> Bool)
    Prime = Const('Prime', Int >> Bool)
    suc, square = (Int >> Int)('suc, square')
    a, b, c = Int('a, b, c')
    Even = Const('Even', Int >> Bool)
    Prime = Const('Prime', Int >> Bool)
    suc, square = (Int >> Int)('suc, square')
    

    M = Model({(a, 5), (b, 2), (c, 7)})
    M[Int] = dom_range(0,20)
    M[Even] = lambda x: x % 2 == 0
    M[Prime] = is_prime
    M[suc] = lambda x: x + 1
    M[square] = lambda x: x * x
    
    
    assert_equal(val_non_strict(a, M), 5)
    assert_equal(val_non_strict(a + b * c, M), 19)
    assert(val_non_strict(Exists(x, b + x == c), M))
    assert(not val_non_strict(Even(a), M))
    assert(val_non_strict(Prime((23)), M))
    assert(not val_non_strict(Prime((22)), M))
    assert(val_non_strict(And(Prime(a), Prime(b), Prime(c)), M))
    assert(val_non_strict(Even(c) | And(Prime(a), Prime(b), Prime(c)), M))
    assert(not val_non_strict(Even(c) | And(Prime(suc(a)), Prime(suc(b)), Prime(c)), M))
    assert(val_non_strict(Exists(x, Even(x)), M))
    assert(val_non_strict(Exists(x, And(Prime(x), Even(x))), M))
    assert(not val_non_strict(Exists(x, And(Prime(x), Even(x), c < x)), M))
    assert(val_non_strict(Exists([x, y], And(Prime(x), Prime(y), x < y)), M))
    assert(val_non_strict(Exists([x, y], And(Prime(x), Prime(y), x !=  y)), M))
    assert(not val_non_strict(Exists([x, y], And(Prime(x), Prime(y), x < y, Even(y))), M))
    assert(val_non_strict(Exists([x, y], And(Prime(x), Prime(y), x < y, Even(x))), M))
    assert(not val_non_strict(Forall(x, Even(x)), M))
    assert(val_non_strict(Forall(x, Or(Even(x), ~Even(x))), M))
    assert(val_non_strict(Forall(x, Even(x) >> ~Even(suc(x))), M))
    assert(val_non_strict(Forall(x, Even(x) >> Even(square(x))), M))
    assert(not val_non_strict(Exists(x, And(Even(x), ~Even(square(x)))), M))
    assert(val_non_strict(Forall(x, Even(square(x)) >> Even(x)), M))
    assert(not val_non_strict(Forall([x, y], And(Prime(x), Prime(y), x < y) >> Even(x)), M))
    assert(val_non_strict(Forall([x, y], And(Prime(x), Prime(y), x < y) >> ~Even(y)), M))
    assert(not val_non_strict(Forall(x, Exists(y, x < y)), M))
    assert(not val_non_strict(Forall([x, y], x < y >>  Exists(z, And(x < z, z < y))), M))
    assert(val_non_strict(Forall([x, y], And(Even(x), Even(y), x < y) >> 
        Exists(z, (x < z) & (z < y))), M))

    def precond(n):
        return ((2) < n) & Even(n)
    
    def goldbach(n):
        return precond(n) >> Exists([x,y], Prime(x) & Prime(y) & (x + y == n))
    
    Goldbach = Forall(z, goldbach(z))
    assert(val_non_strict(Goldbach, M))




def test_lazy_models():
    clear_default_language()
    def nats():
        i = 0
        while True:
            yield i
            i += 1

    nat_dom = Domain('nat', nats)
    Prime = Const('Prime', Int >> Bool)

    M = Model()
    M[Int] = nat_dom
    M[Prime] = is_prime

    x = Int('x')

    assert(val_strict(Exists(x, Prime(x)), M))


