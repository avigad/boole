##################################################
#
# Tests for info.py
#
#
#
#
#
#
#
#
#
#
#
##################################################

from boole.core.expr import *
from boole.core.info import *
from nose.tools import *


T = Const('T', Type())

x = Const('x', T)

y = Const('y', T)

def test_set_info():
    assert_equal(x.info.name, 'default')
    x.info['test'] = True
    assert(x.info.test)
    assert(not x.info.test2)

    z = Const('z', T, test=True)
    assert(z.info.test)

def test_same_info():
    x.info['test'] = True

    @same_info
    def constant_y(_, expr):
        return y

    constant_y(None, x)

    assert(y.info.test)
    assert(not y.info.test2)


def test_with_info():

    test_info = ExprInfo('test_info', {})

    @with_info(test_info)
    def ident(expr):
        return expr

    ident(x)
    assert_equal(x.info.name, 'test_info')
