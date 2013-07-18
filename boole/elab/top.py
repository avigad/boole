#############################################################################
#
# top.py
#
# description: The top-level environment in which to play around
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

    terms.verbose = False

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


    # test = defexpr('test', 3 + one())

    # x = Real('x')
    # y = Real('y')
    # z = Real('z')

    # i = Int('i')
    # j = Int('j')
    # k = Int('k')

    # x_y_z = defexpr('x_y_z', x * y * z)
    
    # int_ops = defexpr('int_ops', 3 * i < j * 2)

    # poly = defconst('poly', pi(X, X >> (X >> X), impl=True))

    # poly_z = defexpr('poly_z', poly(z))

    # nat = deftype('nat')
    
    # nat_sub_real = defsub('nat_sub_real', nat <= Real)

    # A = deftype('A')
    # B = deftype('B')
    # op_a = defconst('op_a', A >> (A >> A))
    # op_b = defconst('op_b', B >> (B >> B))

    # p1 = defconst('p1', A*B)
    # p2 = defconst('p2', A*B)

    # op_pair = \
    #         abst(p1, abst(p2, pair(op_a(p1[0], p2[0]), op_b(p1[1], p2[1]))))


    # definstance('mul_prod', \
    #             forall(A, forall(op_a, forall(B, forall(op_b, \
    #             Mul(A, op_a) >= (Mul(B, op_b) >= Mul(A*B, op_pair)))))), \
    #             triv())


    # test3 = defexpr('test3', pair(3, 3.0) * pair(2, 2.0))


    # test3_def = local_ctxt.defs['test3']

    # mul_def = local_ctxt.defs['*']

    # print
    # print conv.beta_norm(expr.sub_in([mul_def], ['*'], test3_def))
    # print
    
    # test4 = defexpr('test4', pair(3.0, pair(3.0, 3)) * pair(2.0, pair(2.0, 2)))

    # test4_def = local_ctxt.defs['test4']

    # print
    # print conv.beta_norm(expr.sub_in([mul_def], ['*'], test4_def))
    # print

    # test5 = defexpr('test5', pair(pair(3.0, 3), pair(3, 3)) * pair(pair(2.0, 2), pair(2, 2)))

    # test5_def = local_ctxt.defs['test5']

    # print
    # print conv.beta_norm(expr.sub_in([mul_def], ['*'], test5_def))
    # print


    # n = Int('n')
    
    # Vec = defconst('Vec', pi(n, Type))

    # succ = defconst('succ', Int >> Int)

    # nil = defconst('nil', Vec(0))

    # cons = defconst('cons', pi(n, Real >> (Vec(n) >> Vec(succ(n))), impl=True))

    # sum_vec = defconst('sum_vec', pi(n, Vec(n) >> (Vec(n) >> Vec(n)), impl=True))

    # add_nil = defhyp('add_nil', sum_vec(nil, nil) == nil)

    # v1 = defconst('v1', Vec(n))

    # v2 = defconst('v2', Vec(n))

    # a = defconst('a', Real)

    # b = defconst('b', Real)

    # add_cons_eq = sum_vec(cons(a, v1), cons(b, v2)) == cons(a+b, sum_vec(v1, v2))

    # add_cons = defhyp('add_cons', \
    #                   forall(n, forall(a, forall(b, forall(v1, forall(v2, add_cons_eq))))))


    # rev = defconst('rev', pi(n, Vec(n) >> Vec(n), impl=True))

    # v3 = defconst('v3', Vec(3))

    # rev_3 = defexpr('rev_3', rev(v3))

    # w = Real('w')
    # t = Real('t')

    # abs_plus = defexpr('abs_plus', abst(t, t + w))

    # sub_test = defexpr('sub_test', abs_plus(i))

    # p = pair(x, y)

    # proj_x_y_0 = defthm('proj_x_y_0', p[0] == x)

    # prop = defexpr('prop', true & (true | false))
    
    # p = (Real * Real)('p')

    # fa = forall(p, (p[0] + p[1]) == (p[1] + p[0]))

    # plus_commut_stmt = defexpr('plus_commut_stmt', fa, type=Bool)
    
    # plus_commut = defexpr('plus_commut', triv(), fa)


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

    obl = local_ctxt.next_goal()

    obl.interact(tac.par(tac.trytac(unif.instances)))

    obl.interact(tac.unfold('*', 'one')>>tac.simpl(conv.par_beta))

    obl.interact(tac.unfold('Grp'))

    obl.interact(tac.unpack('grp_28'))

    #This is invisible!
    #it appears in an implicit argument.
    obl.interact(unif.unfold('grp_carr')>>tac.simpl(conv.par_beta))

    obl.interact(unif.unfold('grp_op')>>tac.simpl(conv.par_beta))

    obl.interact(unif.unfold('grp_one')>>tac.simpl(conv.par_beta))

    obl.interact(tac.simpl(conv.par_beta))

    obl.interact(unif.mvar_apply(obl[0]['G_unit_r_73']))

    obl.interact(unif.unify>>tac.par(tac.trivial))


    # g = defconst('g', grp_carr(grp))
    # h = defconst('h', grp_carr(grp))

    # defhyp('toto', g * h == h * g)
