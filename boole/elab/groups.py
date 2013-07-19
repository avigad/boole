#############################################################################
#
# groups.py
#
# description: A possible implementation of the Group module
#
#
# Authors:
# Cody Roux
#
#
#
##############################################################################

import boole.core.expr as expr
import boole.core.tactics as tac
import boole.core.conv as conv
import unif
import terms
from terms import *


if __name__ == '__main__':


    el = defconst('el', X)

    One = defclass('One', pi(X, pi(el, Bool)), abst(X, abst(el, true)))

    definstance('One_int', One(Int, 1), triv())

    one_inst = defconst('one_inst', One(X, el))
    
    one = defexpr('one', abst(X, abst(el, abst(one_inst, el))), \
                  pi(X, pi(el, pi(one_inst, X, impl=True), impl=True), impl=True))


    op_mul = defconst('op_mul', Mul(X, op))

    el_one = defconst('el_one', One(X, el))


    Unit_left = defclass('Unit_left', \
                         pi(X, pi(op, pi(el, Mul(X, op) >> (One(X, el) >> Bool)))),
                         abst(X, abst(op, abst(el, abst(op_mul, abst(el_one, \
                                                                     forall(x, one() * x == x)))))))


    Unit_right = defclass('Unit_right', \
                         pi(X, pi(op, pi(el, Mul(X, op) >> (One(X, el) >> Bool)))),
                         abst(X, abst(op, abst(el, abst(op_mul, abst(el_one, \
                                                                     forall(x, x * one() == x)))))))

    G = deftype('G')

    G_mul = defconst('G_mul', G >> (G >> G))

    G_one = defconst('G_one', G)

    g = G('g')

    G_unit_l = defconst('G_unit_l', forall(g, G_mul(G_one, g) == g))

    G_unit_r = defconst('G_unit_r', forall(g, G_mul(g, G_one) == g))

    grp_def = sig(G, sig(G_mul, sig(G_one, sig(G_unit_l, sig(G_unit_r, true)))))

    Grp = defexpr('Grp', grp_def)

    grp = defconst('grp', Grp)

    grp_carr = defexpr('grp_carr', abst(grp, cast(grp, grp_def)[0]), \
                       pi(grp, Type), \
                       tactic=tac.par(tac.unfold('Grp')>>tac.trivial))


    op_cast = cast(cast(grp, grp_def)[1][0], \
                   grp_carr(grp) >> (grp_carr(grp) >> grp_carr(grp)))

    grp_op = defexpr('grp_op', abst(grp, op_cast), \
                       tactic=tac.par(tac.unfold('Grp', 'grp_carr')>>tac.auto))

    definstance('Mul_grp', forall(grp, Mul(grp_carr(grp), grp_op(grp))), triv())


    one_cast = cast(cast(grp, grp_def)[1][1][0], grp_carr(grp))

    grp_one = defexpr('grp_one', abst(grp, one_cast),
                      tactic=tac.par(tac.unfold('Grp', 'grp_carr')>>tac.auto))

    definstance('One_grp', forall(grp, One(grp_carr(grp), grp_one(grp))), triv())
    

    definstance('Unit_right_grp', \
                forall(grp, Unit_right(grp_carr(grp),\
                                       grp_op(grp),\
                                       grp_one(grp), triv(), triv())),\
                triv())

    goal = local_ctxt.next_goal()

    goal.interact(tac.par(tac.trytac(unif.instances)))

    goal.interact(tac.unfold('*', 'one')>>tac.simpl(conv.par_beta))

    goal.interact(tac.unfold('Grp'))

    goal.interact(tac.unpack('grp_28'))

    #This is invisible!
    #it appears in an implicit argument.
    goal.interact(unif.unfold('grp_carr')>>tac.simpl(conv.par_beta))

    goal.interact(unif.unfold('grp_op')>>tac.simpl(conv.par_beta))

    goal.interact(unif.unfold('grp_one')>>tac.simpl(conv.par_beta))

    goal.interact(tac.simpl(conv.par_beta))

    goal.interact(unif.mvar_apply(goal[0]['G_unit_r_73']))

    goal.interact(unif.unify>>tac.par(tac.trivial))


    g = defconst('g', grp_carr(grp))
    h = defconst('h', grp_carr(grp))

    defhyp('toto', g * h == one() * h * g)
