#############################################################################
#
# info.py
#
# description: a container type for information which may be attached to
# expressions.
#
#
# Authors:
# Cody Roux
#
#
#
##############################################################################

class ExprInfo(object):
    """Container for the information dictionary
    attached to expressions
    """
    
    def __init__(self, info):
        """
        
        Arguments:
        - `info`: a python dictionary from strings
        to functions from expressions to objects.
        """
        self.info = info
        
    def __getitem__(self, key):
        """
        
        Arguments:
        - `key`: a string
        """
        return self.info.__getitem__(key)

    def __setitem__(self, key, elt):
        """
        
        Arguments:
        - `key`: a string
        - `elt`: a python object
        """
        self.info.__setitem__(key, elt)
        
    def __delitem__(self, key):
        """
        
        Arguments:
        - `key`: a string
        """
        return self.info.__delitem__(key)

###############################################################################
#
# The default information class:
# This class specifies the default behavior of expressions
# with respect to pretty-printing, behavior as a callable function, etc.
#
###############################################################################


def default_str(expr):
    """The default printer for expressions.
    Simply call the to_string method.
    
    Arguments:
    - `expr`: an expression
    """
    return expr.to_string()


class DefaultInfo(ExprInfo):
    """The default expression information.
    """
    
    def __init__(self):
        ExprInfo.__init__(self, {})
        self.info['__str__'] = lambda x: x.to_string()


###############################################################################
#
# Decorators for adding information to terms.
#
###############################################################################

class infobox(object):
    """Dark magic required to dynamically update info on
    statically created objects.
    """
    
    def __init__(self, info):
        """
        
        Arguments:
        - `info`:
        """
        self._info = info

    def info(self):
        """
        """
        return self._info




#TODO: make this more elegant
def with_info(infobx):
    """Returns the function which calls a function on
    arguments, and update the info field of the result.
    
    Arguments:
    - `info`: an ExprInfo
    """
    def appl(f):
        def call_f(*args, **kwargs):
            e = f(*args, **kwargs)
            e.info = infobx.info()
            for k in kwargs:
                e.info[k] = kwargs[k]
            return e
        return call_f
    return appl
    

def same_info(f):
    """Decorator that keeps the same information as the second argument
    of f
    """
    def call_f(obj, expr, *args, **kwargs):
        e = f(obj, expr, *args, **kwargs)
        e.info = expr.info
        return e
    return call_f
