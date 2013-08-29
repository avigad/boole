#############################################################################
#
# top.py
#
# description: The top-level environment in which to play around
#
#
# Authors:
# Cody Roux
# Jeremy Avigad
#
##############################################################################

from boole.elab.terms import *
from boole.elab.elab import Mvar


if __name__ == '__main__':

    set_verbose()

    m1 = Mvar('m1', Type)
    m2 = Mvar('m2', Type)
    m3 = Mvar('m3', Type)
    m4 = Mvar('m4', Type)
    A = deftype('A')
    B = deftype('B')
    f = defconst('f', pi(A, A >> Bool))

    a = const('a', m1)
    
    print a.type._value
    print
    t, ty, g = elaborate(abst([A, B, a], f(B, a)), None, None, None)
    print t, ":", ty
    print
    print g
    
    print a.type._value
    print
    print ", ".join(map(str, a.type.pending))

    a = const('a', m2)

    print
    print a.type._value
    print
    t, ty, g = elaborate(abst([A, a, B], f(B, a)), None, None, None)
    print t, ":", ty
    print
    print g
    
    print a.type._value
    print
    print ", ".join(map(str, a.type.pending))

    a = const('a', m3)

    b = B('b')
    print
    t, ty, g = elaborate(abst([A, a], a) == abst([B, b], b), None, None, None)
