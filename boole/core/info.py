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
    
    def __init__(self, name, info):
        """
        
        Arguments:
        - `name`: the name of the info instance
        - `info`: a python dictionary from strings
        to functions from expressions to objects.
        """
        self.name = name
        self.info = info
        
    def __getitem__(self, key):
        """
        
        Arguments:
        - `key`: a string
        """
        return self.info.__getitem__(key)

    def __getattr__(self, name):
        """
        return field contained in info
        
        Arguments:
        - `name`: the name of the attribute.
        """
        try:
            return self.info[name]
        except KeyError:
            #TODO: is this the right thing?
            # raise Exception\
            #       ("Could not find attribute {0!s} in {1!s}"\
            #        .format(name, self))
            return None

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

    def __str__(self):
        return self.name

    def update(self, info):
        """Add the new fields in info to self
        
        Arguments:
        - `info`:
        """
        for k in info.info:
            self.info[k] = info.info[k]


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
        ExprInfo.__init__(self, 'default', {})
        self.info['__str__'] = lambda x: x.to_string()
        self.info['checked'] = False

###############################################################################
#
# Decorators for adding information to terms.
#
###############################################################################

#class infobox(object):
#    """Dark magic required to dynamically update info on
#    statically created objects.
#    """
#    
#    def __init__(self, info):
#        """
#        
#        Arguments:
#        - `info`:
#        """
#        self._info = info
#
#    def info(self):
#        """instantiates and returns the _info field when requested
#        """
#        return self._info()
#
#
##TODO: make this more elegant
#def with_info(infobx):
#    """Returns the function which calls a function on
#    arguments, and update the info field of the result.
#    
#    Arguments:
#    - `info`: an ExprInfo
#    """
#    def appl(f):
#        def call_f(*args, **kwargs):
#            e = f(*args, **kwargs)
#            e.info.update(infobx.info())
#            e.info.name = infobx.info().name
#            for k in kwargs:
#                e.info[k] = kwargs[k]
#            return e
#        return call_f
#    return appl
    

def same_info(f):
    """Decorator that keeps the same information as the second argument
    of f
    """
    def call_f(obj, expr, *args, **kwargs):
        e = f(obj, expr, *args, **kwargs)
        #if expr is a de Bruijn index, then it
        # contains no interesting information, and it
        # is most likely substituted by the e, which
        # should keep its own info.
        if expr.is_db():
            pass
        else:
            e.info = expr.info
        return e
    return call_f
