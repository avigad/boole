
#############################################################################
#
# context.py
#
# description: the type containing the local context.
# the local context contains a number of fields, each of which is a pair
# (dict, set), and the set contains the co-domain of the dictionary.
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
        'decls'           :({}, set()),\
        'hyps'            :({}, set()),\
        'defs'            :({}, set()),\
        'sub'             :({}, set()),\
        'rew_rules'       :({}, set()),\
        'classes'         :({}, set()),\
        'class_def'       :({}, set()),\
        'class_instances' :({}, set()),\
        'goals'           :({}, set()),\
        'parent'          :({}, set())
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


class SetElt(object):
    """A wrapper for elements of a set. The reason
    for this type is our overloading of the __eq__
    function for other needs than comparison. We take
    __eq__ to be hash equality for elements of a SetElt
    """
    
    def __init__(self, obj):
        """a SetElt contains a single python object
        
        Arguments:
        - `obj`:
        """
        self.obj = obj

    def __eq__(self, s_elt):
        """hash-equality
        
        Arguments:
        - `obj`:
        """
        return hash(self.obj) == hash(s_elt.obj)

    def __hash__(self):
        return hash(self.obj)


        
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
            return self._context[attr][0]
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
            self.add_to_field(expr.name, expr, 'decls')
        else:
            mess = "The expression {0!s} is not a constant."\
                   .format(expr)
            raise ContextErr(mess, self)

    def pop(self, field):
        """Pop an element from a given field in the dictionary
        
        Arguments:
        - `field`: a field name
        """
        try:
            elt = self._context[field][0].popitem()[1]
            try:
                self._context[field][1].remove(SetElt(elt))
            except KeyError:
                assert(false)
            return elt
        except KeyError:
            return None

    def next_goal(self):
        """Gets the next unsolved goal list in the context.
        Return None if there is none.
        """
        return self.pop('goals')

    #TODO: should this be __setitem__?
    def add_to_field(self, name, expr, field):
        """Add the expression expr to the field
        under the key name.
        
        Arguments:
        - `expr`: an expression
        - `field`: the name of a field
        """
        if field in self._context:
            self._context[field][0][name] = expr
            self._context[field][1].add(SetElt(expr))
            assert(self.get_from_field(name, field) is expr)
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
            return self._context[field][0][name]
        else:
            mess = "Field {0!s} not found in context {1!s}"\
                   .format(field, self.name)
            raise ContextErr(mess, self)

    def mem(self, expr, field):
        """Check if expr is an element in field
        
        Arguments:
        - `expr`:
        - `field`:
        """
        return (SetElt(expr) in self._context[field][1])

    def show(self, dicts=None):
        """Show various definitions in the context.
        
        Arguments:
        - `dicts`: a list of context fields
        """
        if dicts == None:
            d = ['decls', 'defs', 'hyps']
        else:
            d = dicts

        print "In context {0!s}".format(self.name)
        print

        for f in d:
            field = self._context[f][0]
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
