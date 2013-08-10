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

from boole.core.expr import *
from nose.tools import *


Real = Const('Real', Type())

x = Const('x', Real)

y = Const('y', Real)

op = Const('op', Bound(Pi('_'), Real, Real))

triv = Ev(Tele([], []))

tm = App(triv, op, x)

atm_y = Bound(Abst('y'), Real, tm)

atm = Bound(Abst('x'), Real, tm)

def test_subst():
    assert(subst_expr([x], abstract_expr(['x'], tm)).equals(tm))
    assert(subst_expr([x], abstract_expr(['x'], atm)).equals(atm))
    assert(subst_expr([x], abstract_expr(['x'], atm_y)).equals(atm_y))

db_tm = App(triv, op, DB(0))

db_atm_y = Bound(Abst('y'), Real, db_tm)

db_atm = Bound(Abst('x'), Real, db_tm)

def test_abst():
    assert(abstract_expr(['x'], subst_expr([x], db_tm)).equals(db_tm))
    assert(abstract_expr(['x'], subst_expr([x], db_atm)).equals(db_atm))
    assert(abstract_expr(['x'], subst_expr([x], db_atm_y)).equals(db_atm_y))

def test_open():
    v, body = open_bound_fresh(db_atm)
    assert(body.equals(tm))
    assert(v == 'x')

def test_root():
    root, args = root_app(tm)
    assert(root.equals(op))
    assert(len(args) == 1)
    assert(args[0].equals(x))

p = Const('p', Bool())

q = Const('q', Bool())

bool_op = Bound(Pi('_'), Bool(), Bound(Pi('_'), Bool(), Bool()))

def impl(a, b):
    return App(triv, App(triv, Const('implies', bool_op), a), b)


prop = Bound(Forall('x'), Real, Bound(Forall('y'), Real, impl(p, q)))


def test_root_clause():
    assert(root_clause(prop).equals(q))

bin_op = Const('bin_op', Bound(Pi('x'), Real, Bound(Pi('y'), Real, Bool())))

sig = Bound(Sig('x'), Real, Bound(Sig('y'), Real, \
                                  App(triv, App(triv, bin_op, DB(1)), DB(0))))

tele = Tele(['x', 'y', 'hyp'], [Real, Real, App(triv, App(triv, bin_op, x), y)])

def test_sig_to_tele():
    assert(sig_to_tele(sig, open_bound_fresh).equals(tele))

def test_unpack_sig():
    tup = unpack_sig(sig, open_bound_fresh)
    assert(tup.fst.equals(x))
    assert(tup.snd.fst.equals(y))
    assert(tup.snd.snd.type.equals(App(triv, App(triv, bin_op, x), y)))

