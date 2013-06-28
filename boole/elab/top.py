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
from terms import *


if __name__ == '__main__':

    x = Real('x')
    y = Real('y')
    z = Real('z')

    i = Int('i')
    j = Int('j')
    k = Int('k')

    x_y_z = defexpr('x_y_z', x * y * z)
    
    int_ops = defexpr('int_ops', 3 * i < j * 2)

    poly = defconst('poly', pi(X, X >> (X >> X)))

    poly_z = defexpr('poly_z', poly(z))

    nat = deftype('nat')
    
    nat_sub_real = defsub('nat_sub_real', nat <= Real)

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
                Mul(A, op_a) >= (Mul(B, op_b) >= Mul(A*B, op_pair)))))), \
                triv())


    test3 = defexpr('test3', pair(3, 3.0) * pair(2, 2.0))


    test3_def = local_ctxt.defs['test3']

    mul_def = local_ctxt.defs['*']

    print
    print conv.beta_norm(expr.sub_in([mul_def], ['*'], test3_def))
    print
    
    test4 = defexpr('test4', pair(3.0, pair(3.0, 3)) * pair(2.0, pair(2.0, 2)))

    test4_def = local_ctxt.defs['test4']

    print
    print conv.beta_norm(expr.sub_in([mul_def], ['*'], test4_def))
    print

    test5 = defexpr('test5', pair(pair(3.0, 3), pair(3, 3)) * pair(pair(2.0, 2), pair(2, 2)))

    test5_def = local_ctxt.defs['test5']

    print
    print conv.beta_norm(expr.sub_in([mul_def], ['*'], test5_def))
    print


    n = Int('n')
    
    Vec = defconst('Vec', pi(n, Type))

    Int_ = deftype('Int', implicit=True)
    m = Int_('m')

    succ = defconst('succ', Int >> Int)

    nil = defconst('nil', Vec(0))

    cons = defconst('cons', pi(m, Real >> (Vec(m) >> Vec(succ(m)))))

    sum_vec = defconst('sum_vec', pi(m, Vec(m) >> (Vec(m) >> Vec(m))))

    add_nil = defhyp('add_nil', sum_vec(nil, nil) == nil)

    v1 = defconst('v1', Vec(m))

    v2 = defconst('v2', Vec(m))

    a = defconst('a', Real)

    b = defconst('b', Real)

    add_cons_eq = sum_vec(cons(a, v1), cons(b, v2)) == cons(a+b, sum_vec(v1, v2))

    add_cons = defhyp('add_cons', \
                      forall(m, forall(a, forall(b, forall(v1, forall(v2, add_cons_eq))))))


    rev = defconst('rev', pi(m, Vec(m) >> Vec(m)))

    v3 = defconst('v3', Vec(3))

    rev_3 = defexpr('rev_3', rev(v3))

    w = Real('w')
    t = Real('t')

    abs_plus = defexpr('abs_plus', abst(t, t + w))

    sub_test = defexpr('sub_test', abs_plus(i))

    p = pair(x, y)

    proj_x_y_0 = defthm('proj_x_y_0', p[0] == x)

    prop = defexpr('prop', true & (true | false))
    
    p = (Real * Real)('p')

    fa = forall(p, (p[0] + p[1]) == (p[1] + p[0]))

    plus_commut_stmt = defexpr('plus_commut_stmt', fa, type=Bool)
    
    plus_commut = defexpr('plus_commut', triv(), fa)
