
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
    - `hyps`:  declarations of constants of type Bool
    - `defs`: sends the name of a defined constant to its definition.
    - `defs`: declarations of inequalities to be treated as subtype assertions
    - `rew_rules`: declarations of equalities to be treated as reduction
    rules.
    - `classes`: declarations of constants of type Type -> Type, representing
    type classes, paired with a list of constants representing the methods
    to those classes.
    - `class_def`: the definitions of the classes in terms of sigma-types,
    and the definitions of each method as a projection.
    - `class_instances`: the definitions of the instance constants, which
    may depend on further instances, and the defining equations for the
    instances themselves.
    - `unsolved_goals`: a list of unsolved goal lists.
    - `parent_contexts`: a dictionary sending names to contexts possibly
    containing the current one.
    """
    ctxt = {
        'decls'           :{},\
        'hyps'            :{},\
        'defs'            :{},\
        'sub'             :{},\
        'rew_rules'       :{},\
        'classes'         :{},\
        'class_def'       :{},\
        'class_instances' :{},\
        'goals'           :{},\
        'parent'          :{}
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
        """Return the dictionary with name attr
        from the context.
        
        Arguments:
        - `attr`:
        """
        try:
            return self._context[attr]
        except KeyError:
            mess = "Field {0!s} not found in context {1!s}"\
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

    def next_goal(self):
        """Gets the next unsolved goal list in the context.
        Return None if there is none.
        """
        try:
            return self._context['goals'].popitem()[1]
        except KeyError:
            return None

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

    def get_from_field(self, name, field):
        """Get the object associated to name in the
        field.
        
        Arguments:
        - `name`: a string
        - `field`: the name of a field
        """
        if field in self._context:
            return self._context[field][name]
        else:
            mess = "Field {0!s} not found in context {1!s}"\
                   .format(field, self.name)
            raise ContextErr(mess, self)

    def show(self, dicts=None):
        """Show various definitions in the context.
        
        Arguments:
        - `dicts`: a list of context fields
        """
        if dicts == None:
            d = ['decls', 'defs', 'hyps']
        else:
            d = dicts

        for f in d:
            field = self._context[f]
            print f + ':'
            print
            for k in field:
                if f == 'decls':
                    print "  " + k + " : " + str(field[k].type)
                else:
                    print "  " + k + " : " + str(field[k])
            print

    def __str__(self):
        return self.name
