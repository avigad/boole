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
from nose.tools import *


Real = Const('Real', Type())

x = Const('x', Real)

y = Const('y', Real)

op = Const('op', Bound(Pi('_'), Real, Real))

triv = Ev(Tele([], []))

tm = App(triv, op, DB(0))

atm = Bound(Abst('x'), Real, tm)

beta_redex = App(triv, atm, y)

def test_par_beta():
    assert(par_beta(beta_redex).equals(App(triv, op, y)))

ho_tm = App(triv, DB(0), y)

aho_tm = Bound(Abst('f'), Bound(Pi('_'), Real, Real), ho_tm)

super_beta = App(triv, aho_tm, atm)

def test_beta_norm():
    assert(beta_norm(super_beta).equals(App(triv, op, y)))
