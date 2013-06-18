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
import boole.core.goals as goals
import boole.core.conv as conv
from terms import *


if __name__ == '__main__':

    z = Real('z')
    w = Real('w')

    X = Type_('X')

    poly = defconst('poly', pi(X, X >> (X >> X)))

    poly_z = defexpr('poly_z', poly(z))

    # _, obl = mvar_infer(poly(z), ctxt=local_ctxt)

    # nat = deftype('nat')
    
    # nat_sub_real = defsub('nat_sub_real', nat <= Real)

    Y = deftype('Y')

    op = defconst('op', Y >> (Y >> Y))
    
    ibinop = X >> (X >> X)
    ibinop.info['implicit'] = True

    iop = defconst('op', ibinop)

    Mul = defclass('Mul', pi(Y, pi('op', Y >> (Y >> Y), Bool)), abst(Y, abst(op, true)))

    mul_app = Mul(X, iop)
    mul_app.info['implicit'] = True

    mul_ev = Const('mul_ev', mul_app)

    mul = defexpr('mul', abst(X, abst(iop, abst(mul_ev, iop))))

    int_mul = defconst('int_mul', Int >> (Int >> Int))

    definstance('mul_int', Mul(Int, int_mul), trivial())

    test = defexpr('test', mul(3, 2))

    definstance('mul_real', Mul(Real, mult), trivial())

    test2 = defexpr('test2', mul(3.0, 2.0))

    A = deftype('A')
    B = deftype('B')
    op_a = defconst('op_a', A >> (A >> A))
    op_b = defconst('op_b', B >> (B >> B))

    p1 = defconst('p1', A*B)
    p2 = defconst('p2', A*B)

    op_pair = \
            abst(p1, abst(p2, pair(op_a(p1[0], p2[0]), op_b(p1[1], p2[1]))))


    definstance('mul_prod', \
                forall(A, forall(op_a, forall(B, forall(op_b, \
                Mul(A, op_a) == (Mul(B, op_b) == Mul(A*B, op_pair)))))), \
                trivial())


    test3 = defexpr('test3', mul(pair(3, 3.0), pair(2, 2.0)))

    obl = local_ctxt.goals['_ty_goals_46']

    mul_prod = local_ctxt.hyps['mul_prod']

    obl.interact(unif.instances)


    # test3 = mul(pair(3, 3.0), pair(2, 2.0))

    # ty, obl = elab.mvar_infer(test3, ctxt=local_ctxt)

    # print ty
    # print obl

    # obl.interact(goals.par(unif.unify))

    # obl.interact(goals.par(unif.instances))

    # mul_def = local_ctxt.defs['mul']

    # print elab.sub_mvar(test3, undef=True)
    # print
    # print expr.sub_in([mul_def], ['mul'], elab.sub_mvar(test3, undef=True))
    # print
    # print conv.beta_norm(expr.sub_in([mul_def], ['mul'], elab.sub_mvar(test3, undef=True)))
    
    # n = Int('n')
    
    # Vec = defconst('Vec', pi(n, Type))

    # Int_ = deftype('Int', implicit=True)
    # m = Int_('m')

    # succ = defconst('succ', Int >> Int)

    # nil = defconst('nil', Vec(0))

    # cons = defconst('cons', pi(m, Real >> (Vec(m) >> Vec(succ(m)))))

    # sum_vec = defconst('sum_vec', pi(m, Vec(m) >> (Vec(m) >> Vec(m))))

    # add_nil = defhyp('add_nil', sum_vec(nil, nil) == nil)

    # v1 = defconst('v1', Vec(m))

    # v2 = defconst('v2', Vec(m))

    # a = defconst('a', Real)

    # b = defconst('b', Real)

    # add_cons_eq = sum_vec(cons(a, v1), cons(b, v2)) == cons(a+b, sum_vec(v1, v2))

    # add_cons = defhyp('add_cons', \
    #                   forall(m, forall(a, forall(b, forall(v1, forall(v2, add_cons_eq))))))


    # rev = defconst('rev', pi(m, Vec(m) >> Vec(m)))

    # v3 = defconst('v3', Vec(3))

    # rev_3 = defexpr('rev_3', rev(v3))

    # x = Int('x')
    # y = Int('y')
    # z = (Real * Real)('z')
    # w = Real('w')
    # t = Real('t')

    # abs_plus = defexpr('abs_plus', abst(t, t + w))

    # typing.check(abs_plus(x), context=local_ctxt)
    
    # typing.check(pair(x, y))

    # typing.check(x + y, \
    #              context=local_ctxt)

    # typing.check(z[0] * z[1] == z[1] * z[0])

    # typing.check(abst(z, pair(x, x)))

    # typing.check(forall(z, (z[0] + z[1]) == (z[1] + z[0])))

    # fa = forall(z, (z[0] + z[1]) == (z[1] + z[0]))

    # plus_commut_stmt = defexpr('plus_commut_stmt', fa, type=Bool)
    
    # typing.check(local_ctxt.decls['Real'])
    # print

    # def definition_of(expr):
    #     """Return the definition of a defined constant.
        
    #     Arguments:
    #     - `expr`:
    #     """
    #     if expr.is_const():
    #         if expr.info.defined:
    #             print expr, ':=', local_ctxt.get_from_field(expr.name, 'defs')
    #             print
    #         else:
    #             print expr, " is not defined!"
    #             print
    #     else:
    #         print expr, " is not a constant!"
    #         print



    # definition_of(plus_commut_stmt)

    # plus_commut = defexpr('plus_commut', trivial(), fa)

    # p = pair(x, y)

    # proj_x_y_0 = defexpr('proj_x_y_0', trivial(), p[0] == x, tactic=goals.simpl)

    # typing.check(conj(true, disj(true, false)))
