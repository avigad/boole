################################################################################
#
# z3_examples.py
#
# Author:
# Jeremy Avigad
#
################################################################################

from boole import *
from boole.interfaces.z3_interface import *
from boole.interfaces.polya_interface import *
from boole.semantics.value import *

set_verbose()

x, y, z = Real('x, y, z')
i, j, k = Int('i, j, k')
p = Bool('p')

## A little fun with subtyping
Rational = deftype('Rational')

q = Rational('q')

defsub('int_sub_rat', Int <= Rational)
defsub('rat_sub_real', Rational <= Real)

# conf.set_implicit(False)
defexpr('_', (2 + x) * q)

add_rat = defconst('add_rat', Rational >> (Rational >> Rational))

definstance('Add_rat', Add(Rational, add_rat), triv())

defexpr('_', (2 + q) * x)

## We can evaluate expressions, if the expression uses only built-in types,
# or if a model is defined
p1, p2, p3 = Bool('p1, p2, p3')

e = exists([p1, p2, p3], And(implies(p1, And(p2,p3)), Not(implies(p3, And(p1, p2)))))
check(e)
print "e = ", eval_expr(e)
print

A little real arithmetic for fun!
push_ctxt('real_arith')

defhyp("x_pos", x > 0.0)
defhyp("y_pos", y > 0.0)
defhyp("x_leq_1", x < 1.0)
defhyp("y_leq_1", y < 1.0)

defthm("arith_geom", x + y > x * y)

goal = current_ctxt().next_goal()

goal.interact(polya_tac)


## The Tall, Dark and Handsome puzzle
Men, (Alec, Bill, Carl, Dave) = \
    defenum('Men', ('Alec', 'Bill', 'Carl', 'Dave'))
tall, dark, handsome = (Men >> Int)('tall, dark, handsome')
ideal = Men('ideal')
x = Men('x')

s = Z3_Solver()
s.add(forall(x, Or(tall(x) == 0, tall(x) == 1)))
s.add(forall(x, Or(dark(x) == 0, dark(x) == 1)))
s.add(forall(x, Or(handsome(x) == 0, handsome(x) == 1)))
s.add(tall(Alec) + tall(Bill) + tall(Carl) + tall(Dave) == 3)
s.add(dark(Alec) + dark(Bill) + dark(Carl) + dark(Dave) == 2)
s.add(handsome(Alec) + handsome(Bill) + handsome(Carl) + handsome(Dave) == 1)
s.add(forall(x, Or(tall(x) == 1, dark(x) == 1, handsome(x) == 1)))
s.add(dark(Alec) == dark(Dave))   
s.add(tall(Bill) == tall(Carl))
s.add(tall(Carl) != tall(Dave))
s.add(And(tall(ideal) == 1, dark(ideal) == 1, handsome(ideal) == 1))

print 'Check:', s.check()
print 'Model: ', s.z3_model()

## A classic
Person, (Knight, Knave) = defenum('Person', ('Knight', 'Knave'))
Liar = defconst('Liar', Person >> Bool)
Says = defconst('Says', Person >> (Bool >> Bool))
x = Person('x')
p = Bool('p')
lies = forall([x, p], implies([Liar(x), Says(x, p)], Not(p)))
truth = forall([x, p], implies([Not(Liar(x)), Says(x, p)], p))
# paradox = Says(Knave, Liar(Knave))
s = Z3_Solver()
s.add(lies)
s.add(truth)
# s.add(paradox)

puzzle = Says(Knight, Says(Knave, Liar(Knight)))
s.add(puzzle)
s.add(Not(Liar(Knight)))

print 'Check:', s.check()
print 'Model: ', s.z3_model()

B = Z3_to_Boole()
b_mod = B.model(s.z3_model())

print b_mod
