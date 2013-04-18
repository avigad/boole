################################################################################
#
# sage_examples.py
#
# These are meant to be called from Sage.
#
################################################################################

from boole.interfaces.sage_interface import * 
        
def test_symbolic_expression_converter():
    
    L = Language()
    set_default_language(L)
    
    Real('x y z')
    (Real * Real >> Real)('f')
    
    x, y, z = var('x y z')
    f = function('f')
    
    C1 = Sage_to_Boole()
    C2 = Boole_to_Sage()
    
    def check(e):
        print 'Sage expression:', e
        be = C1(e)
        print 'Boole translation:', be
        print 'Translation back:', C2(be)
        print
        
    check(f(x, y) * y ** 2 + 3 * f(2, z))
    check(x ** 2 == 3 + y)
    
# other direction
def test_symbolic_expression_converter2():
    
    L = Language()
    set_default_language(L)
    
    x, y, z = Real('x y z')
    f = (Real * Real >> Real)('f')

    C1 = Sage_to_Boole()
    C2 = Boole_to_Sage()
        
    def check(e):
        print 'Boole expression:', e
        se = C2(e)
        print 'Sage translation:', se
        print 'Translation back:', C1(se)
        print
        
    check(f(x, y) * y ** ii(2) + rr(3) * f(ii(2), z))
    check(x ** rr(2) == rr(3) + y)
    
def sage_examples():
    
    test_symbolic_expression_converter()
    test_symbolic_expression_converter2()

