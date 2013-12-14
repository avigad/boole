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
from boole.core.context import *
from nose.tools import *


Real = Const('Real', Type())

x = Const('x', Real)

y = Const('y', Real)

z = Const('z', Real)

op = Const('op', Bound(Pi('_'), Real, Real))

triv = Ev(Tele([], []))

op_x = App(triv, op, DB(0))

lam_x_op_x = Bound(Abst('x'), Real, op_x)

beta_redex = App(triv, lam_x_op_x, y)

def test_head_beta():
    assert(par_beta(beta_redex).equals(App(triv, op, y)))

double_beta = App(triv, lam_x_op_x, beta_redex)

def test_par_beta():
    assert(par_beta(double_beta).equals(App(triv, op, App(triv, op, y))))

f_y = App(triv, DB(0), y)

lam_f_f_y = Bound(Abst('f'), Bound(Pi('_'), Real, Real), f_y)

super_beta = App(triv, lam_f_f_y, lam_x_op_x)

def test_beta_norm():
    assert(beta_norm(super_beta).equals(App(triv, op, y)))

my_ctxt = Context("conv_tests")

my_ctxt.defs[x.name] = y

my_ctxt.defs[y.name] = z

my_child_ctxt = Context("conv_tests2")
my_child_ctxt.parent["conv_tests"] = my_ctxt

my_grand_child_ctxt = Context("conv_tests3")
my_grand_child_ctxt.parent["conv_tests2"] = my_child_ctxt

def test_unfold():
    assert(unfold(x.name, x, my_ctxt).equals(y))
    assert(unfold(x.name, x, my_child_ctxt).equals(y))
    assert(unfold(x.name, x, my_grand_child_ctxt).equals(y))
    
def test_unfold_once():
    assert(unfold_once(App(triv, x, y), my_ctxt).equals(App(triv, y, z)))

def test_unfold_all():
    assert(unfold_all(x, my_ctxt).equals(z))

