##################################################
#
# Tests for config.py
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

import boole.elaboration.config as conf
from nose.tools import *


def test_verbose():
    assert(not conf.verbose)
    conf.set_verbose(True)
    assert(conf.verbose)


def test_implicit():
    assert(conf.implicit)
    conf.set_implicit(False)
    assert(not conf.implicit)


def test_unicode():
    assert(conf.print_unicode)
    conf.set_unicode(False)
    assert(not conf.print_unicode)


def test_current_ctxt():
    assert_equal(conf.current_ctxt().name, "default_ctxt")
    c = conf.current_ctxt()
    conf.push_ctxt()
    assert(conf.current_ctxt().mem(c, 'parent'))



    




