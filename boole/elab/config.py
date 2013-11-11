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

p_implicit = False


def print_implicit(setting=True):
    """Sets the print implicit flag:
    This flag makes the implicit arguments
    visible upon printing.
    """
    global p_implicit
    p_implicit = setting


###############################################################################
#
# Global variables for printing purposes
#
###############################################################################

in_sage = False

def in_sage(setting=True):
    global in_sage
    in_sage = setting

