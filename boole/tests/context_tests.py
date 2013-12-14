##################################################
#
# Tests for context.py
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

from boole.core.context import *
from nose.tools import *

f = CtxtField()

c = Context('c')
c1 = Context('c1')
c2 = Context('c2')

f['a'] = 1
f['b'] = 2
f['c'] = 2

class MockExpr(object):
    """Mock expression object
    """
    
    def __init__(self, name):
        """
        
        Arguments:
        - `name`:
        """
        self.name = name
        


def test_ctxt_field():
    assert_equal(f['a'], 1)
    assert(f.mem(2))
    del f['a']
    del f['b']
    assert(f.mem(2))
    assert(not f.mem(1))
    
def test_context():
    e = MockExpr('e')
    c.add_const(e)
    assert_equal(c.decls['e'], e)
    assert(c.mem(e, 'decls'))
    c.pop('decls')
    assert(not c.mem(e, 'decls'))
    c.add_to_field('a', 1, 'hyps')
    assert_equal(c.to_list('hyps'), [1])
    c1.add_to_field(c.name, c, 'parent')
    c2.add_to_field(c1.name, c1, 'parent')
    c.add_const(e)
    assert_equal(c2.get_rec('e', 'decls'), e)

    

