##################################################
#
# Tests for conv.py
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

from boole.core.conv import *
from boole.core.context import Context
from nose.tools import *


Real = Const('Real', Type())

x = Const('x', Real)

y = Const('y', Real)

op = Const('op', Bound(Pi('_'), Real, Real))

triv = Ev(Tele([], []))

tm = App(triv, op, DB(0))

atm = Bound(Abst('x'), Real, tm)

beta_redex = App(triv, atm, y)

def test_head_beta():
    


def test_par_beta():
    assert(par_beta(beta_redex).equals(App(triv, op, y)))

ho_tm = App(triv, DB(0), y)

aho_tm = Bound(Abst('f'), Bound(Pi('_'), Real, Real), ho_tm)

super_beta = App(triv, aho_tm, atm)

def test_beta_norm():
    assert(beta_norm(super_beta).equals(App(triv, op, y)))

my_ctxt = Context("conv_tests")

my_ctxt.defs[x.name] = y

my_child_ctxt = Context("conv_tests2")
my_child_ctxt.parent["conv_tests"] = my_ctxt

my_grand_child_ctxt = Context("conv_tests3")
my_grand_child_ctxt.parent["conv_tests2"] = my_child_ctxt

def test_unfold():
    assert(unfold(x.name, x, my_ctxt).equals(y))
    assert(unfold(x.name, x, my_child_ctxt).equals(y))
    assert(unfold(x.name, x, my_grand_child_ctxt).equals(y))
    
def test_unfold_once():

def test_unfold_all():
    

