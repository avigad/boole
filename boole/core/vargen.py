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


class VarGen(object):
    """Generate a fresh name according to a dictionary
    sending names to a counter. These should never be reset.
    """

    def __init__(self):
        """Create a dictionary which associates an index to a name.
        free_vars is a function which returns the list of free variables
        of a term.
        """
        self.default = '_Boole'
        self._name_index = {}

    def get_name(self, name=None, free_in=None):
        """Return an unused name:
        - if `name` is defined, returns a name with that
        prefix.
        - if `free_in` is defined to be a list of variables,
        return a name which is free wrt the variables in
        that list: e.g. if name = 'x' and free_in=[x, x_1, y],
        get_name returns x_2.
        """
        if name != None:
            pad = name
        else:
            pad = self.default

        if free_in is None:
            inc_name(pad, self._name_index)
            i = self._name_index[pad]
            if i == 0:
                return pad                
            else:
                return "{0!s}_{1!s}".format(pad, i)
        else:
            if not (pad in free_in):
                return pad
            else:
                i = 0
                fresh = "{0!s}_{1!s}".format(pad, i)
                while fresh in free_in:
                    i += 1
                    fresh = "{0!s}_{1!s}".format(pad, i)
                return fresh
