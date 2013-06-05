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

    X = Type_('X')

    poly = defconst('poly', pi(X, X >> (X >> X)))

    poly_z = defexpr('poly_z', poly(z))
    
    print local_ctxt.defs['poly_z']

    nat = deftype('nat')
    
    nat_sub_real = defsub('nat_sub_real', nat <= Real)

    # def ii(n):
    #     if isinstance(n, int) and n >= 0:
    #         return defconst(str(n), Int)
    #     else:
    #         raise Exception("Expected a non-negative integer!")

    Y = deftype('Y')

    binop = Y >> (Y >> Y)

    op = defconst('op', binop)

    ibinop = X >> (X >> X)
    ibinop.info['implicit'] = True

    iop = defconst('op', ibinop)

    Mul = defclass('Mul', pi(Y, pi(op, Bool)), abst(Y, abst(op, true)))

    mul_app = Mul(X, iop)
    mul_app.info['implicit'] = True

    mul = defconst('mul', pi(X, pi(iop, mul_app >> (X >> (X >> X)))))

    int_mul = defconst('int_mul', Int >> (Int >> Int))

    definstance('mul_int', Mul(Int, int_mul), trivial())

    test = defexpr('test', mul(3, 2))

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

    add_cons = defhyp('add_cons', sum_vec(cons(a, v1), cons(b, v2)) == cons(a+b, sum_vec(v1, v2)))


    rev = defconst('rev', pi(m, Vec(m) >> Vec(m)))

    v3 = defconst('v3', Vec(3))

    rev_3 = defexpr('rev_3', rev(v3))

    x = Int('x')
    y = Int('y')
    z = (Real * Real)('z')
    w = Real('w')
    t = Real('t')

    abs_plus = defexpr('abs_plus', abst(t, t + w))

    print abs_plus

    typing.check(abs_plus(x), context=local_ctxt)
    
    typing.check(pair(x, y))

    typing.check(x + y, \
                 context=local_ctxt)

    typing.check(z[0] * z[1] == z[1] * z[0])

    typing.check(abst(z, pair(x, x)))

    typing.check(forall(z, (z[0] + z[1]) == (z[1] + z[0])))

    fa = forall(z, (z[0] + z[1]) == (z[1] + z[0]))

    plus_commut_stmt = defexpr('plus_commut_stmt', fa, type=Bool)
    
    typing.check(local_ctxt.decls['Real'])
    print

    def definition_of(expr):
        """Return the definition of a defined constant.
        
        Arguments:
        - `expr`:
        """
        if expr.is_const():
            if expr.info.defined:
                print expr, ':=', local_ctxt.get_from_field(expr.name, 'defs')
                print
            else:
                print expr, " is not defined!"
                print
        else:
            print expr, " is not a constant!"
            print

    x_plus_one = defexpr('x_plus_one', x + 1, Real)

    definition_of(plus_commut_stmt)

    definition_of(x_plus_one)

    plus_commut = defexpr('plus_commut', trivial(), fa)

    p = pair(x, y)

    proj_x_y_0 = defexpr('proj_x_y_0', trivial(), p[0] == x, tactic=goals.simpl)

    boolop = Bool * Bool >> Bool

    typeop = Type * Type >> Type

    typing.check(boolop)
    print
    typing.check(typeop)
    print
    typing.check(conj(true, disj(true, false)))
    print
    print p[1]
    print conv.par_beta(p[0])
    print conv.par_beta(p[1])
