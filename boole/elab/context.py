#############################################################################
#
# context.py
#
# description: the type containing the local context.
#
#
# Authors:
# Cody Roux
#
#
#
##############################################################################

def init_context():
    """Return a dictionary with initial context information.

    - `decls`: declarations, a name corresponds to a constant.
    - `hyps`:  declerations of constants of type Bool
    - `defs`:  declarations of defined constants
    - `def_rules`: declarations of equalities between a defined constant
    and its definition.
    - `rew_rules`: declarations of equalities to be treated as reduction
    rules.
    - `coercions`: declarations of functions representing implicit casts.
    - `classes`: declarations of constants of type Type -> Type, represening
    type classes, paired with a list of constants representing the methods
    to those classes.
    - `class_def`: the definitions of the classes in terms of sigma-types,
    and the definitions of each method as a projection.
    - `class_instances`: the definitions of the instance constants, which
    may depend on further instances, and the defining equations for the
    instances themselves.
    - `parent_contexts`: a dictionary sending names to contexts possibly
    containing the current one.
    """
    ctxt = {
        'decls'           :{},\
        'hyps'            :{},\
        'defs'            :{},\
        'def_rules'       :{},\
        'rew_rules'       :{},\
        'coercions'       :{},\
        'classes'         :{},\
        'class_def'       :{},\
        'class_instances' :{},\
        'parent_contexts' :{}
        }
    return ctxt


class ContextErr(Exception):
    """Exceptions raised by the context.
    """
    
    def __init__(self, mess, ctxt):
        """
        
        Arguments:
        - `mess`:
        - `ctxt`:
        """
        Exception.__init__(self, mess)
        self.mess = mess
        self.ctxt = ctxt
        



class Context(object):
    """A context is a dictionary of
    dictionaries containing contextual information.
    """
    
    def __init__(self, name, context=None):
        """
        
        Arguments:
        - `name`: a string
        - `context`: a dictionary of dicts containing
        contextual information
        """
        self.name = name
        if context == None:
            self._context = init_context()
        else:
            self._context = context
        

    def __getattr__(self, attr):
        """Return the constant defined in the decls
        field of the context.
        
        Arguments:
        - `attr`:
        """
        try:
            return self._context['decls'][attr]
        except KeyError:
            mess = "Constant {0!s} not found in context {1!s}"\
                   .format(attr, self.name)
            raise ContextErr(mess, self)

    def add_const(self, expr):
        """Add a constant to the declarations
        
        Arguments:
        - `expr`:
        """
        if expr.is_const():
            self._context['decls'][expr.name] = expr
        else:
            mess = "The expression {0!s} is not a constant."\
                   .format(expr)
            raise ContextErr(mess, self)
        

    #TODO: should this be __setitem__?
    def add_to_field(self, name, expr, field):
        """Add the expression expr to the field
        under the key name.
        
        Arguments:
        - `expr`: an expression
        - `field`: the name of a field
        """
        if field in self._context:
            self._context[field][name] = expr
        else:
            mess = "Field {0!s} not found in context {1!s}"\
                   .format(field, self.name)
            raise ContextErr(mess, self)
        

