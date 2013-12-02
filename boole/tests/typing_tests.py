##################################################
#
# Tests for typing.py
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

from boole.core.typing import *
from nose.tools import *


Real = Const('Real', Type())

x = Const('x', Real)

y = Const('y', Real)

op = Const('op', Bound(Pi('_'), Real, Real))

triv = Ev(Tele([], []))

tm = App(triv, op, DB(0))

atm = Bound(Abst('x'), Real, tm)

ho_tm = App(triv, DB(0), y)

aho_tm = Bound(Abst('f'), Bound(Pi('_'), Real, Real), ho_tm)

super_beta = App(triv, aho_tm, atm)

def test_max_sort():
    """
    """
    

def test_expr_type_infer():
    """
    """

def test_expr_type_check():
    """
    """
    



def test_infer():
    ty, _ = infer(Bound(Pi('_'), Real, Real))
    assert(ty.equals(Type()))

    ty, _ = infer(Bound(Pi('_'), Real, Bool()))
    assert(ty.equals(Type()))
    
    ty, _ = infer(atm)
    assert(ty.equals(Bound(Pi('x'), Real, Real)))
    
    ty, obl = infer(super_beta)
    assert(ty.equals(Real))

