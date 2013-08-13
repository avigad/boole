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


if __name__ == '__main__':

    set_verbose()
    x = Int('x')
    y = Int('y')
    
    check(x + y)
    print x + y
    print(check(x + y))

