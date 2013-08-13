################################################################################
#
# z3_examples.py
#
# Authors:
# Jeremy Avigad
#
################################################################################

import operator

from boole.elab.terms import *
from boole.interfaces.z3_interface import *

if __name__ == '__main__':

    x, y, z = Real('x, y, z')
    i, j, k = Int('i j k')
    p = Bool('p')
    q = Bool('q')
    r = Bool('r')
    f = (Real >> Real)('f')
    
    T1 = Boole_to_Z3()
    T2 = Z3_to_Boole()
    
    def test(expr):
        e1 = T1(expr)
        e2 = T2(e1)
        print 'Boole expression:', expr
        print 'Translated to Z3:', e1
        print 'Translated back:', e2
        print
        
    test(p)
    test(And(p,q))
    test(And(p, q, Not(r)))
    test(x + y)
    test(x + y + 3)
    test(f(x + y) + f(f(x)))
    test((x + y) * (i + j))
    test(And((x + y) <= f(x), Not(y < z)))
    test(Forall(x, x == x))
    test(Forall([x, y], Exists(z, x + z == y)))
    test(Implies([p, q], Or(r, (x == 7))))   
    
    S = Z3_Solver()
    S.add(Implies([p, q], Or(r, (x == 7))))
    S.add(And(p, q))
    S.add(Not(r))
    if (S.check()):
        print S.z3_model()
        
