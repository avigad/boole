
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

from collections import MutableMapping, Counter, OrderedDict


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


class CtxtField(MutableMapping):
    """The type of a context field. It maintains
    both a dictionary from names to objects and
    a set of objects for fast membership testing
    """
    
    def __init__(self):
        """
        
        Arguments:
        - `name`:
        """
        self.dict = OrderedDict()
        self.set = Counter()

    def __getitem__(self, key):
        return self.dict[key]

    def __setitem__(self, key, value):
        if key in self.dict:
            #check that the existing value is in the set
            cur_val = SetElt(self.dict[key])
            assert(self.set[cur_val])
            self.set.subtract([cur_val])
        self.dict[key] = value
        self.set.update([SetElt(value)])

    def __delitem__(self, key):
        val = SetElt(self.dict[key])
        del self.dict[key]
        self.set.subtract([val])

    def __iter__(self):
        return iter(self.dict)

    def __len__(self):
        return len(self.dict)

    def mem(self, value):
        """Return 1 if value is in the set, 0 otherwise
        
        Arguments:
        - `value`:
        """
        return self.set[SetElt(value)]


class Context(object):
    """A context is a dictionary of
    dictionaries containing contextual information.
    """
    
    def __init__(self, name):
        """
        
        Arguments:
        - `name`: a string identifying the context
        - `decls`: declarations, a name corresponds to a constant.
        - `hyps`:  declarations of constants of type Bool
        - `defs`: sends the name of a defined constant to its definition.
        - `sub`: declarations of inequalities to be treated as subtype
        assertions
        - `rew_rules`: declarations of equalities to be treated as reduction
        rules.
        - `classes`: declarations of constants of type Type -> Type,
        representing type classes, paired with a list of constants
        representing the methods to those classes.
        - `class_def`: the definitions of the classes,
        and the definitions of each method as a projection.
        - `class_instances`: the definitions of the instance constants, which
        may depend on further instances, and the defining equations for the
        instances themselves.
        - `goals`: a dictionary of unsolved goal lists.
        - `parent`: a dictionary sending names to contexts
        containing the current one.
        """
        self.name = name
        self.decls = CtxtField()
        self.hyps = CtxtField()
        self.defs = CtxtField()
        self.sub = CtxtField()
        self.rew_rules = CtxtField()
        self.classes = CtxtField()
        self.class_def = CtxtField()
        self.class_instances = CtxtField()
        self.goals = CtxtField()
        self.parent = CtxtField()

    def add_const(self, expr):
        """Add a constant to the declarations
        
        Arguments:
        - `expr`:
        """
        self.decls[expr.name] = expr

    def pop(self, field):
        """Pop an element from a given field in the dictionary
        
        Arguments:
        - `field`: a field name
        """
        return self.__dict__[field].popitem()[1]

    def next_goal(self):
        """Gets the next unsolved goal list in the context.
        Return None if there is none.
        """
        return self.pop('goals')

    def add_to_field(self, name, expr, field):
        """Add the expression expr to the field
        under the key name.
        
        Arguments:
        - `name`: a string associated to expr
        - `expr`: an expression
        - `field`: the name of a field
        """
        self.__dict__[field][name] = expr

    def mem(self, expr, field):
        """Check if expr is an element in field
        
        Arguments:
        - `expr`:
        - `field`:
        """
        return self.__dict__[field].mem(expr)

    def mem_rec(self, expr, field):
        """Recursively check to see if expr is in the field,
        or any of the parent fields
        
        Arguments:
        - `expr`:
        - `field`:
        """
        if self.__dict__[field].mem(expr):
            return True
        else:
            for p in self.parent.itervalues():
                if p.mem_rec(expr, field):
                    return True
            return False

    def get_rec(self, key, field):
        """Recursively try to find a value associated to
        key in the field, using a search in the context, then in the
        parent contexts
        
        Arguments:
        - `key`:
        - `field`:
        """
        try:
            return self.__dict__[field][key]
        except KeyError:
            for p in self.parent.itervalues():
                try:
                    return p.get_rec(key, field)
                except KeyError:
                    pass
            raise KeyError(key)

    def to_list(self, field):
        """Return the list of elements of
        that field
        
        Arguments:
        - `field`:
        """
        return list(self.__dict__[field].itervalues())

    def to_list_rec(self, field):
        """As above, but for self and all parent
        contexts
        
        Arguments:
        - `field`:
        """
        field_vals = self.to_list(field)
        for p in self.parent.itervalues():
            field_vals += p.to_list_rec(field)
        return field_vals

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
            field = self.__dict__[f]
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
