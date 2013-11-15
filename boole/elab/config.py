###############################################################################
#
# prelude.py
#
# description: A module containing configuration variables and setter functions.
#
#
# Authors:
# Cody Roux
#
###############################################################################

from boole.core.context import Context


###############################################################################
#
# Global variables for printing purposes
#
###############################################################################

verbose = False


def set_verbose(setting=True):
    """Sets the verbose flag:
    This flag gives more information about the output of each command.
    """
    global verbose
    verbose = setting

implicit = False


def set_implicit(setting=True):
    """Sets the print implicit flag:
    This flag makes the implicit arguments
    visible upon printing.
    """
    global implicit
    implicit = setting

print_unicode = True


def set_unicode(setting=True):
    """Print the unicode name of constants
    """
    global print_unicode
    print_unicode = setting


in_sage = False


def set_in_sage(setting=True):
    global in_sage
    in_sage = setting

###############################################################################
#
# Global variables for managing the context
#
###############################################################################

###############################################################################
#
# Create a default context for the user
#
###############################################################################

current_ctxt = Context("default_ctxt")


def get_current_ctxt():
    return current_ctxt


def set_current_ctxt(ctxt):
    global current_ctxt
    current_ctxt = ctxt


def push_ctxt(name):
    """Create a new context and give it a name,
    make it a child of the current context
    
    Arguments:
    - `name`:
    """
    new_ctxt = Context(name)
    new_ctxt.add_to_field(get_current_ctxt().name, \
                          get_current_ctxt(), 'parent')
    set_current_ctxt(new_ctxt)
    
