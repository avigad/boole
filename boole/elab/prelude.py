# -*- coding: utf-8 -*-

###############################################################################
#
# prelude.py
#
# description: A module containing basic definitions to be included
# by default.
#
#
# Authors:
# Cody Roux
# Jeremy Avigad
#
###############################################################################

from terms import *

###############################################################################
#
# Basic operations on the integers and reals
#
###############################################################################

# binary operations on the reals

add_real = defconst('add_real', Real >> (Real >> Real), value=v.add_real_val)
mul_real = defconst('mul_real', Real >> (Real >> Real), value=v.mul_real_val)
minus_real = defconst('minus_real', Real >> (Real >> Real), \
                      value=v.minus_real_val)
divide_real = defconst('divide_real', Real >> (Real >> Real), \
                       value=v.divide_real_val)

# unary operations on the reals

uminus_real = defconst('uminus_real', Real >> Real, value=v.uminus_real_val)
abs_real = defconst('abs_real', Real >> Real, value=v.abs_real_val)

# binary predicates on the reals

lt_real = defconst('lt_real', Real >> (Real >> Bool), value=v.lt_real_val)
le_real = defconst('le_real', Real >> (Real >> Bool), value=v.le_real_val)

# integers

int_sub_real = defsub('int_sub_real', Int <= Real)

# binary operations on the integers

add_int = defconst('add_int', Int >> (Int >> Int), value=v.add_int_val)
mul_int = defconst('mul_int', Int >> (Int >> Int), value=v.mul_int_val)
minus_int = defconst('minus_int', Int >> (Int >> Int), value=v.minus_int_val)
divide_int = defconst('divide_int', Int >> (Int >> Int), \
                      value=v.divide_int_val)

# unary operations on the integers

uminus_int = defconst('uminus_int', Int >> Int, value=v.uminus_int_val)
abs_int = defconst('abs_int', Int >> Int, value=v.abs_int_val)

# binary predicates on the integers

lt_int = defconst('lt_int', Int >> (Int >> Bool), value=v.lt_int_val)
le_int = defconst('le_int', Int >> (Int >> Bool), value=v.le_int_val)


###############################################################################
#
# Type classe instances for Int and Real
#
###############################################################################

# allow input syntax mul(e1, e2, ..., en)
definstance('Mul_real', Mul(Real, mul_real), triv())
definstance('Mul_int', Mul(Int, mul_int), triv())

# allow input synatx add(e1, e2, ..., en)
definstance('Add_real', Add(Real, add_real), triv())
definstance('Add_int', Add(Int, add_int), triv())

definstance('Minus_real', Minus(Real, minus_real), triv())
definstance('Minus_int', Minus(Int, minus_int), triv())

definstance('Div_real', Div(Real, divide_real), triv())
definstance('Div_int', Div(Int, divide_int), triv())

definstance('Uminus_real', Uminus(Real, uminus_real), triv())
definstance('Uminus_int', Uminus(Int, uminus_int), triv())

definstance('Abs_real', Abs(Real, abs_real), triv())
definstance('Abs_int', Abs(Int, abs_int), triv())

definstance('Lt_real', Lt(Real, lt_real), triv())
definstance('Lt_int', Lt(Int, lt_int), triv())

definstance('Le_real', Le(Real, lt_real), triv())
definstance('Le_int', Le(Int, le_int), triv())
