#############################################################################
#
# vargen.py
#
# description: Fresh variable generation
#
#
# Authors:
# Cody Roux
#
#
##############################################################################


def inc_name(name, counts):
    if name in counts:
        counts[name] = counts[name] + 1
    else:
        counts[name] = 0


#TODO: make names fresh with respect to a set of free variables,
# typically those in the sub-expression that we are opening.
# Pass those variables when calling open_bound_fresh
class VarGen(object):
    """Generate a fresh name according to a dictionary
    sending names to a counter. These should never be reset.
    """

    def __init__(self):
        """Initialize the index to dictionary.
        """
        self.default = '_Boole'
        self._name_index = {}

    def get_name(self, name=None):
        """Return an unused name
        """
        if name != None:
            pad = name
        else:
            pad = self.default
        inc_name(pad, self._name_index)
        i = self._name_index[pad]
        if i == 0:
            fresh = pad
        else:
            fresh = "{0!s}_{1!s}".format(pad, i)
        return fresh
