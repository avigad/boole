################################################################################
#
# z3_examples.py
#
################################################################################

from boole.core.model import *
from boole.interfaces.z3_interface import * 
        
def test_z3_translations():
    
    # make a language    
    L = Language()
    set_default_language(L)
    x, y, z, w = Int('x y z w')
    p, q, r, s = Bool('p q r s')
    Bird = BasicType('Bird')
    pigeon = Bird('pigeon')
    Flies = Const('Flies', Bird >> Bool)
    f = (Int * Int >> Int)('f')

    L.show()
    
    # make z3 language
    boole_to_z3 = Boole_to_Z3()
    z3_to_boole = Z3_to_Boole(L)

    def check(t):
        print "Term: ", t
        zt = boole_to_z3(t)
        print "Z3 translation:", zt
        print "Translation back:", z3_to_boole(zt)
        print
            
    print "z3 sorts constructed: ", boole_to_z3.sort_dict.keys()
    print "z3 symbols constructed: ", boole_to_z3.symbol_dict.keys()
    print
    
    check(ii(1))
    check(x)
    check(x + y)
    check(rr(5.1))
    check(f(x, y) + z)
    check(x == y)
    check(x > rr(1.2))
    check((x == y) & (x > rr(1.2)))
    check((x + rr(5.1)) * (y - z))
    check(Sum(x,y,Product(f(x, y),y)))
    check(Sum(rr(5.1), rr(3.2)))
    check(Product(x, y, Sum(x, y, rr(1.2), w)))
    check(Sum(x, y * z, rr(1.5678), w))

    check((x == y) == (y == x))

    check(pigeon)    
    check(Flies(pigeon))
    
    check(Forall(x, x == x))
    check(Forall([x, y, z], x + y + z == z + y + x))
    check(Forall([x, y], Exists(z, x + z > y)))
    check(Forall([x, w], Exists(y, Forall(z, y + z > x +w))))
    check(Forall([x,w], 
        Exists([y,z], z == y + w) & Exists(y, y == x)))


def test1():
    
    L = Language()
    set_default_language(L)
    
    p, q, r, s, t, u = Bool('p q r s t u')
    x, y, z = Real('x y z')
    
    formula = ~(And(p, Or(q, ~r)) >> And(p, q, ~r, x == y))
    print 'Formula: ', formula
    
    s = Z3_Solver()
    s.add(formula)
    print 'Check: ', s.check()
    M = s.model()
    print 'Model:'
    print
    M.show()
    print
    print 'Evaluation of formula in model: ', val_non_strict(formula, M)
    
    
def test2():
    
    L = Language()
    set_default_language(L)
    
    Men = EnumType('Men', ('Alex', 'Bill', 'Charles'))
    Alex, Bill, Charles = Men.make_constants()
        
    Likes = (Men * Men >> Bool)('likes')
    x, y, z = Men('x y z')
    
    s = Z3_Solver()
    s.add(Likes(x, Bill))
    s.check()
        
#    can't translate relations
#    M = s.model()
#    M.show()

    print s.solver.model()
    
    
# reasoning with polynomials
def test3():

    L = Language()
    set_default_language(L)

    x = Real('x')
    # TODO: old z3 bug if replace 1.01 by 1.00
    p = x ** ii(2) + rr(1.01)
    q = rr(0.1) * x ** ii(3)
    print p
    print q

    s = Z3_Solver(L)
    s.add(q > p)
    print s.check()
    M = s.model()
    M.show()
    

# tall, dark, and handsome puzzle
def test4():
    
    L = Language()
    set_default_language(L)
    
    Men = EnumType('Men', ('Alec', 'Bill', 'Carl', 'Dave'))
    Alec, Bill, Carl, Dave = Men.make_constants()
    tall, dark, handsome = (Men >> Int)('tall, dark, handsome')
    ideal = Men('ideal')
    x = Men('x')
    
    s = Z3_Solver(L)
    s.add(Forall(x, Or(tall(x) == ii(0), tall(x) == ii(1))))
    s.add(Forall(x, Or(dark(x) == ii(0), dark(x) == ii(1))))
    s.add(Forall(x, Or(handsome(x) == ii(0), handsome(x) == ii(1))))
    s.add(tall(Alec) + tall(Bill) + tall(Carl) + tall(Dave) == ii(3))
    s.add(dark(Alec) + dark(Bill) + dark(Carl) + dark(Dave) == ii(2))
    s.add(handsome(Alec) + handsome(Bill) + handsome(Carl) + handsome(Dave) == \
          ii(1))
    s.add(Forall(x, Or(tall(x) == ii(1), dark(x) == ii(1), handsome(x) == ii(1))))
    s.add(dark(Alec) == dark(Dave))   
    s.add(tall(Bill) == tall(Carl))
    s.add(tall(Carl) != tall(Dave))
    s.add(And(tall(ideal) == ii(1), dark(ideal) == ii(1), \
              handsome(ideal) == ii(1)))
    
    print s.check()
    print s.solver.model()
    
# again, need to read functions
#    M = s.model()
#    M.show()


if __name__ == '__main__':

    test_z3_translations()
    print
    
    test1()
    print
 
    test2()
    print   
 
    test3()
    print   
 
    test4()
    print   
 
 
