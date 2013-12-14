###############################################################################
#
# config.py
#
# description: A module performing initial configuration for the system and
#              external provers
#
#
# Authors:
# Cody Roux
#
###############################################################################

import os.path as path
import os

###############################################################################
#
# Global variables for hard-coded paths of binaries
#
###############################################################################

sage_bin = path.expanduser("~/prog/python/sage-5.6/sage")

z3_bin = "/usr/bin/z3"

coq_bin = "/usr/bin/coqtop"

ladr_bin = "/home/croux/prog/C/LADR-2009-11A/bin/"


###############################################################################
#
# Global variables for the path of python interfaces
#
###############################################################################

z3_py = path.expanduser("~/prog/Cpp/z3/src/api/python")



###############################################################################
#
# Sage-specific variables
#
###############################################################################

in_sage = False


def set_in_sage(setting=True):
    global in_sage
    in_sage = setting

