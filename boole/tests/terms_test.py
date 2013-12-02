# Tests for type inference with subtypes and dependencies

from boole.elaboration.prelude import *
from boole.elaboration.terms import elaborate
from nose.tools import *



Nat = deftype('Nat')
defsub('nat_sub_int', Nat <= Int)

add_nat = defconst('add_nat', Nat >> (Nat >> Nat))
definstance('Add_nat', Add(Nat, add_nat), triv())

Rat = deftype('Rat')
defsub('int_sub_rat', Int <= Rat)
defsub('rat_sub_real', Rat <= Real)

add_rat = defconst('add_rat', Rat >> (Rat >> Rat))
definstance('Add_rat', Add(Rat, add_rat), triv())

x = Real('x')
i = Int('i')
n = Nat('n')
q = Rat('q')


def test_tm_str():
    """
    """

def test_to_expr():
    """
    """

def test_pair():
    """
    """
    

def test_tm_call():
    """
    """

def test_iterative_app_call():
    """
    """

def test_implies_call():
    """
    """

def test_get_pair():
    """
    """
    

def test_typ_call():
    """
    """

def test_constructors():
    """
    """
    

def test_root_app_implicit():
    """
    """

def test_dest_binop_left():
    """
    """

def test_dest_binop_right():
    """
    """
    

def test_elaborate():
    """
    """

def test_check():
    """
    """
    






def test_sub():
    
    assert(elaborate(i + x, None, None)[2].is_solved())
    assert(elaborate(x + i, None, None)[2].is_solved())
    assert(elaborate(i + i, None, None)[2].is_solved())
    assert(elaborate(n + n, None, None)[2].is_solved())
    assert(elaborate(n + i, None, None)[2].is_solved())
    assert(elaborate(x + (i + n), None, None)[2].is_solved())
    assert(elaborate((i + n) + x, None, None)[2].is_solved())
    assert(elaborate((x + n) + i, None, None)[2].is_solved())
    assert(elaborate((q + n) + x, None, None)[2].is_solved())
    assert(elaborate((i + q) + x, None, None)[2].is_solved())
    assert(elaborate(x + (n + q), None, None)[2].is_solved())
    assert(elaborate(i + (n + x) + (n + q + x) + i, None, None)[2].is_solved())


Vec = defconst('Vec', pi(n, Type))

succ = defconst('succ', Nat >> Nat)

zero = defconst('zero', Nat)

nil = defconst('nil', Vec(zero))

cons = defconst('cons', pi(n, Real >> (Vec(n) >> Vec(succ(n))), impl=True))

sum_vec = defconst('sum_vec', pi(n, Vec(n) >> (Vec(n) >> Vec(n)), impl=True))


def test_implicit():

    assert(elaborate(sum_vec(nil, nil) == nil, None, None)[2].is_solved())

    v1 = defvar('v1', Vec(n))
    
    v2 = defvar('v2', Vec(n))

    a = defvar('a', Real)
    
    b = defvar('b', Real)
    
    assert(elaborate(forall([n, a, b, v1, v2],
                       sum_vec(cons(a, v1), cons(b, v2)) == cons(a+b, sum_vec(v1, v2))),
                     None, None)\
           [2].is_solved())
