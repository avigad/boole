##################################################
#
# Tests for expr.py
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

from boole.core.language import *
from boole.core.expr import *
from nose.tools import *


def test_types():
    """
    """
    i, j, k = Int('i j k')
    x = Const('x', Real)
    y, z = Real('y, z')
    p, q, r = Bool('p q r')    
    adder = Abs([i, j], i + j)
    A = BasicType('A')
    B = BasicType('B')
    f = (A >> B)('f')
    g = Const('g', A * A >> B)
    a1, a2 = A('a1 a2')
    assert_equal(j.etype(), Int)
    assert_equal((i + j).etype(), Int)
    assert_equal(x.etype(), Real)
    assert_equal((x + i).etype(), Real)
    assert_equal((i + (4.2)).etype(), Real)
    assert_equal(f(a1).etype(), B)
    assert_equal(g(a1, a2).etype(), B)
    assert((Int * Int >> Int).is_super(adder.etype()))
    assert_equal(ii(42).etype(), Int)
    assert_equal(rr(42).etype(), Real)
    assert_equal((adder(i, (3))).etype(), Int)
    assert((Real * Real >> Real).is_super(plus.etype()))
    assert_equal((x ** (2) + (3) * x + (7)).etype(), Real)
    assert_equal((j ** (2) + (3) * j + (7)).etype(), Int)
    assert_equal((Sum(x ** (2), (3) * x, (7))).etype(), Real)
    assert_equal((Sum(j ** (2), (3) * j, (7))).etype(), Int)
    assert_equal(((x * (3.0) >= (17)) & (p | q)).etype(), Bool)
    assert_equal((And(p,q)).etype(), Bool)
    assert_equal((And(p, q, r)).etype(), Bool)
    assert_equal((~And(p, ~q, (r | p))).etype(), Bool)
    assert_equal((Forall(x, x == x)).etype(), Bool)
    assert_equal((Forall([x, y], x == y)).etype(), Bool)
    assert_equal((Exists([x, y], ((0) < x) & (x + y < (3)))).etype(), Bool)

def test_lang():
    """
    """
    L = Language()
    set_default_language(L)
    m, n, p, q = Int('m n p q')
    prime = Const('Prime', Int >> Bool)
    even = Const('Even', Int >> Bool)   
    f = (Int >> Int)('f') 
    People = EnumType('People', ['Alice', 'Bob', 'Cathy'])
    Alice, Bob, Cathy = People.make_constants()
    x = People('x')
    assert(get_default_language().has_const('Prime'))
    assert(not get_default_language().has_const('y'))
    assert(get_default_language().has_type('People'))
