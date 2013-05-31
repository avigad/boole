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
from terms import *


if __name__ == '__main__':



    z = real('z')

    X = Type_('X')
    X.info.update(StTyp())


    poly = defconst('poly', pi(X, Type_, X >> (X >> X)))

    poly_z = defexpr('poly_z', poly(z))

    nat = deftype('nat')

    def ii(n):
        if isinstance(n, int) and n >= 0:
            return defconst(str(n), nat)
        else:
            raise Exception("Expected a non-negative integer!")

    n = nat('n')
    
    Vec = defconst('Vec', pi(n, nat, Type))

    nat_ = deftype('nat', implicit=True)

    m = nat_('m')

    rev = defconst('rev', pi(m, nat_, Vec(m) >> Vec(m)))

    three = ii(3)

    v3 = defconst('v3', Vec(three))

    rev_3 = defexpr('rev_3', rev(v3))

    print dummy()

    nat = deftype('nat')

    not_bin_op = nat >> nat >> nat

    nat_sub_real = (nat <= real)('nat_sub_real')

    #TODO: should we add the hypothesis or the constant?
    local_ctxt.add_to_field('nat_sub_real', nat_sub_real.type, 'hyps')

    print not_bin_op

    x = nat('x')
    y = nat('y')
    z = (real * real)('z')
    w = real('w')
    t = real('t')

    abs_plus = defexpr('abs_plus', abst(t, real, t + w))

    print abs_plus

    typing.check(abs_plus(x), context=local_ctxt)
    
    typing.check(pair(x, y))

    typing.check(x + y, \
                 context=local_ctxt)

    typing.check(z[0] * z[1] == z[1] * z[0])

    typing.check(abst(z, real * real, pair(x, x)))

    typing.check(forall(z, real * real, (z[0] + z[1]) == (z[1] + z[0])))

    fa = forall(z, real * real, (z[0] + z[1]) == (z[1] + z[0]))

    plus_commut_stmt = defexpr('plus_commut_stmt', fa, type=Bool)
    
    typing.check(local_ctxt.decls['real'])
    print

    def definition_of(expr):
        """Return the definition of a defined constant.
        
        Arguments:
        - `expr`:
        """
        if expr.is_const():
            if expr.info.defined:
                print local_ctxt.get_from_field(expr.name + "_def", 'defs')\
                      .type
                print
            else:
                print expr, " is not defined!"
                print
        else:
            print expr, " is not a constant!"
            print

    two = defexpr('two', one + one, real)

    definition_of(plus_commut_stmt)

    definition_of(two)

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
