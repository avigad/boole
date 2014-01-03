##################################################
#
# Tests for elab.py
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

from boole.core.expr import *
from boole.elaboration.elab import *
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

double_beta = App(triv, lam_x_op_x, beta_redex)

f_y = App(triv, DB(0), y)

lam_f_f_y = Bound(Abst('f'), Bound(Pi('_'), Real, Real), f_y)

super_beta = App(triv, lam_f_f_y, lam_x_op_x)

x1 = mk_meta('x', Real)
x2 = mk_meta('x', Real)


def test_mk_meta():
    assert(not x1.equals(x2))
    

def test_mvar_infer():
    ty, _ = mvar_infer(x1)
    assert(Real.equals(ty))

    
def test_sub_mvar():
    x2.set_val(z)
    x1.set_val(x2)
    assert(sub_mvar(x2).equals(z))


def test_enrich():
    t = enrich('w', Real, lam_x_op_x)
    assert('w' in t.body.conv.tele.vars)


def test_app_expr():
    lam_x_type = Bound(Pi('_'), Real, Real)
    lam_x_type.info['implicit'] = True
    t = app_expr(lam_x_op_x, lam_x_type, [], [])
    assert(t.arg.is_mvar())

