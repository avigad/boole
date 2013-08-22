##################################################
#
# Tests for tactics.py
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

from boole.core.tactics import *
from boole.core.expr import *
from boole.core.goals import *

from nose.tools import *

import boole.core.context as context
import boole.core.conv as conv


Real = Const('Real', Type())

x = Const('x', Real)

y = Const('y', Real)

op = Const('op', Bound(Pi('_'), Real, Real))

empty_tel = Tele([], [])

triv = Ev(empty_tel)

tm = App(triv, op, x)

atm_y = Bound(Abst('y'), Real, tm)

atm = Bound(Abst('x'), Real, tm)

db_tm = App(triv, op, DB(0))

db_atm_y = Bound(Abst('y'), Real, db_tm)

db_atm = Bound(Abst('x'), Real, db_tm)

beta_redex = App(triv, db_atm, y)

p = Const('p', Bool())

q = Const('q', Bool())

bool_op = Bound(Pi('_'), Bool(), Bound(Pi('_'), Bool(), Bool()))

def impl(a, b):
    return App(triv, App(triv, Const('implies', bool_op), a), b)

prop = Bound(Forall('x'), Real, Bound(Forall('y'), Real, impl(p, q)))

bin_op = Const('bin_op', Bound(Pi('x'), Real, Bound(Pi('y'), Real, Bool())))

sig = Bound(Sig('x'), Real, Bound(Sig('y'), Real, \
                                  App(triv, App(triv, bin_op, DB(1)), DB(0))))

bin_op_x_y = App(triv, App(triv, bin_op, x), y)

def test_triv():
    """
    """
    ctxt = context.Context('test_ctxt')
    g = Goals('test', ctxt, goals = sub_goal(empty_tel, atm, atm))
    g.solve_with(trivial)
    assert(g.is_solved())

    g = Goals('test', ctxt, goals = [Goal(Tele(['_'], [p]), p)])
    g.solve_with(trivial)
    assert(g.is_solved())
    

def test_simpl():
    ctxt = context.Context('test_ctxt')
    g = Goals('test', ctxt, goals = \
              sub_goal(empty_tel, beta_redex, App(triv, op, y)))

    g.solve_with(simpl(conv.par_beta))
    g.solve_with(trivial)
    assert(g.is_solved())

def test_intro():
    ctxt = context.Context('test_ctxt')
    g = Goals('test', ctxt, goals = \
              [Goal(empty_tel, Bound(Forall('x'), Real, impl(p, impl(p, q))))])

    g.solve_with(intros)
    assert(g.goals[0].prop.equals(q))

def test_destruct():
    ctxt = context.Context('test_ctxt')
    Real2 = Const('Real2', Type())
    rfun = Bound(Pi('x'), Real, Real)
    r2fun = Bound(Pi('y'), Real2, Real2)
    
    g = Goals('test', ctxt, goals = sub_goal(empty_tel, rfun, r2fun))
    g.solve_with(destruct)
    assert(g.goals[0].prop.is_sub())
    assert(g.goals[0].prop.lhs.equals(Real))
    assert(g.goals[0].prop.rhs.equals(Real2))

    assert(g.goals[1].prop.is_sub())
    assert(g.goals[1].prop.lhs.equals(Real2))
    assert(g.goals[1].prop.rhs.equals(Real))

    assert(g.goals[2].prop.is_sub())
    assert(g.goals[2].prop.lhs.equals(Real))
    assert(g.goals[2].prop.rhs.equals(Real2))

def test_unpack():
    ctxt = context.Context('test_ctxt')
    s = Const('s', sig)
    goal = Goal(Tele(['s'], [sig]), Sub(s, s))
    g = Goals('test', ctxt, goals = [goal])
    g.solve_with(unpack('s'))
    assert(g.goals[0]['h'].equals(bin_op_x_y))
    assert(g.goals[0].prop.lhs.is_pair())

