################################################################################
#
# models.py
#
# description: models and evalauation in Boole
#
#
# Authors:
# Jeremy Avigad
# Cody Roux
#
#
################################################################################

import random
import itertools as it
from expr import *
from logic import *

################################################################################
#
# Domains
#
################################################################################


class DomainInfinite(Exception):
    """Raised if some domain is infinite
    by an operation that iterates over the domain
    """
    def __init__(self, name):
        Exception.__init__(self)
        self.name = name


class Domain(object):
    """Domains represent a finite or infinite set which interprets
    a base sort in Boole
    """
    def __init__(self, name, values, mem = None, from_name = None,
                 is_finite = False, rand_elem = None):
        """
        
        Arguments:
        - `name`: a string that represents the name of the domain
        - `values`: a function of no arguments, which returns a generator for the elements of the domain.
        - `mem`: takes a python object and returns a boolean
        indicating whether that object is in the domain.
        - `from_name`: a function which returns an object in the domain
        when given a name, i.e. a string.
        - `is_finite`: a boolean which indicates weather the domain is
        finite or not (this allows support for some decision procedures).
        - `rand_elem`: a function which takes an optional seed, an optional size
        and returns a random element in the domain of that size
        (this allows limited support for testing).
        """
        self.name = name
        self._values = values
        self._mem = mem
        self._from_name = from_name
        self.is_finite = is_finite
        self._rand_elem = rand_elem

    def values(self):
        """Returns a generator which enumerates the elements in the domain.
        """
        return self._values()
        
    def mem(self, val):
        """
        
        Arguments:
        - `val`: a python object
        """
        if self._mem != None:
            return self._mem(val)
        else:
            return (val in self.values())

    def from_name(self, key):
        """
        
        Arguments:
        - `key`: a string
        """
        if self._from_name != None:
            return self._from_name(key)
        else:
            for v in self.values():
                if str(v) == key:
                    return v
            raise LookupError('Name {0!s} not found'.format(str(v)))
            

    def rand_elem(self, seed = None, size = None):
        """If there is a _rand_elem function,
        call that. Otherwise, if the domain is finite or if
        size is not None return a random element.
        
        Arguments:
        - `seed`: an integer, used to seed the generator.
        - `size`: an integer, deontes the size of the result
        (by some arbitrary standard).
        """
        if self._rand_elem != None:
            return self._rand_elem(seed = seed, size = size)
        elif size != None:
            if seed != None:
                random.seed(seed)
            return random.choice(it.islice(self.values(), size))
        elif self.is_finite:
            if seed != None:
                random.seed(seed)
            return random.choice(self.values())
        else:
            raise DomainInfinite(self.name)

    def __str__(self):
        return self.name


def dom_range(n, m):
    return Domain("range("+str(n)+","+str(m)+")", lambda : xrange(n, m), 
                  from_name = int,
                  is_finite = True)


class product(object):
    """An iterator which enumerates
    the product of a sequence of generators, given in the form
    of functions from the unit type to an iterator.
    This is done lazily/on-demand.
    Does not `dovetail`.
    """
    
    def __init__(self, *gens):
        """
        
        Arguments:
        - `gens`: a list of functions from unit to iterable
        """
        self.gens = gens
        self.len = len(gens)
        self.index = 0
        self.iters = [None] * self.len
        self.init(0)
        self.tuple = [None] * self.len
        
    def __iter__(self):
        return self

    # Initialize all the iterators in iters
    # from index i to the end.
    def init(self, i):
        for j in range(i, self.len):
            self.iters[j] = iter(self.gens[j]())

    # Initialize iterators from index i+1
    # and increment all iterators from index i to the
    # end, put the new values in tuple.
    # Set the index to the last element of the iters list.
    def incr_tuple(self, i):
        if i < self.len - 1:
            self.init(i+1)
        for j in range(i, self.len):
            self.tuple[j] = self.iters[j].next()
        self.index = self.len - 1

    # Increment the tuple after position i, and return it
    # The index jumps to the final position.
    # If the current iterater is finished, jump back a step
    # and continue. If the beginning of the tuple is reached,
    # stop.
    def next(self):
        try:
            self.incr_tuple(self.index)
            return tuple(self.tuple)
        except StopIteration:
            self.index -= 1
            if self.index >= 0:
                return self.next()
            else:
                raise StopIteration

################################################################################
#
# The class of models: these give the information necessary to interpret
# expressions which do not have a default value.
#
################################################################################

# TODO: rethink decision to use name as key always
# TODO: use separate dictionaries for types and constants?
#       (compare to languages)

class Model:
    """A model stores interpretations for constants and types.
    If given a constant, return a Python object for its value. 
    If given a type, return an instance of the Domain class.
    """
    
    def __init__(self, *args):
        """Initialize the model using the overriden assignment.
        -`*args`: an iterable of pairs (key, value)
        """
        self.symbol_dict = {}
        if len(args) == 0:
            pass
        elif len(args) == 1:
            for e, v in args[0]:
                self.symbol_dict[e.name] = v
        else:
            raise NotImplementedError()

    def __getitem__(self, elt):
        """
        
        Arguments:
        - `elt`: an etype or an expr
        """
        return self.symbol_dict[elt.name]

    def __setitem__(self, elt, val):
        """
        
        Arguments:
        - `elt`: an etype or an expr
        - `val`: a python object
        """
        self.symbol_dict[elt.name] = val

    def __delitem__(self, elt):
        """
        
        Arguments:
        - `elt`: an etype or an expr
        """
        del self.symbol_dict[elt.name]

    def __contains__(self, elt):
        """
        
        Arguments:
        - `elt`: an etype or an expr
        """
        return elt.name in self.symbol_dict
    
    def show(self):
        for name in self.symbol_dict.keys():
            print name, '->', self.symbol_dict[name]
            

################################################################################
#
# An instance of the visitor classes, for evaluating an expression in a model.
#
################################################################################



class TypeValue(TypeVisitor):
    """Compute the value of a type in a
    class of models
    """
    
    def __init__(self):
        """Do nothing.
        """
        TypeVisitor.__init__(self)
        
    def visit_basic(self, etype, *models):
        """If there is a default value, return it, otherwise
        search for the key in each model and return the first match.
        
        Arguments:
        - `etype`: an etype
        - `*models`: a list of models.
        """
        if etype.value != None:
            return etype.value
        else:
            for m in models:
                try:
                    return m[etype]
                except KeyError:
                    pass
        raise NoValue(etype)

    def visit_enum(self, etype, *models):
        """Return the enumeration of the values of each element.
        
        Arguments:
        - `etype`: an etype
        - `*models`: a list of models
        """
        return Domain(etype.name, lambda : etype.elts, mem = None,
                      from_name = lambda x: x, is_finite = True)




    def visit_prod(self, etype, *models):
        """The value of a product type is a list of tuples.

        Arguments:
        - `etype`: an etype
        - `*models`: a list of models
        """
        dom_factors = map(lambda e : self.visit(e, *models), etype.factors)

        is_finite = True
        name = []
        for d in dom_factors:
            is_finite = is_finite & d.is_finite
            name.append(d.name)

        def values():
            return product(* map(lambda d: d.values, dom_factors))

        return Domain(name, values, is_finite = is_finite)

    def visit_fun(self, etype, *models):
        """
        
        Arguments:
        - `etype`: an etype
        - `*models`: a list of models
        """
        # enumerating functions works as follows: take the
        # interpretation of the domain and codomain if they exist
        # raise FunTypeError otherwise. If A and B are the
        # interpretations of the domain and codomain,
        # then each function corresponds to a number n from
        # 0 to |B|^|A|-1 in the following way:
        # write n in |B|-ary representation.
        # this is a sequence of digits d1,....,dk
        # of length -exactly- |A|. Send an element a:A
        # to b:B if the (first) index of a in list(A) is i and
        # that of b in list(B) is di.
        # There is redundancy if A has repeated elements.

        # Raise an exception if either A or B is infinite.
        def digit_to_fun(l, A, B):
            """Convert a list of digits to a function.
            
            Arguments:
            - `l`: a list of ints.
            - `a`: a list of elements.
            - `b`: a list of element.
            """
            # l changes during execution, we must make a copy!
            d = list(l)
            return (lambda a: B[ d[A.index(a)] ])

        def incr(digits, base):
            """Increment a finite list of digits.
            
            Arguments:
            - `digits`: a list of digits
            - `base`: an integer
            """
            digits[0] = digits[0] + 1
            for i, d in enumerate(digits):
                if d >= base:
                    if i+1 < len(digits):
                        digits[i+1] = digits[i+1] + 1
                    digits[i] = 0
            
        if etype.dom == None or etype.codom == None:
            raise FunTypeError("Can't enumerate a polymorphic type")
        else:
            A = self.visit(etype.dom, *models)
            B = self.visit(etype.codom, *models)
            if (not A.is_finite):
                raise DomainInfinite(A.name)
            if (not B.is_finite):
                raise DomainInfinite(B.name)

            name = "(" + A.name + ")" + "=>" + B.name

            vA = list(A.values())
            vB = list(B.values())

            def funs():
                digits = [0] * len(vA)
                for _ in range(0, pow(len(vB), len(vA))):
                    incr(digits, len(vB))
                    yield digit_to_fun(digits, vA, vB)

            return Domain(name, funs, is_finite = True)


class ExprValue(ExprVisitor):
    """Compute the value of an expression
    in a class of models.
    """
    
    def __init__(self):
        """Do nothing.
        """
        ExprVisitor.__init__(self)

    def visit_const(self, expr, strict, *models):
        """If there is a default value, return that value, otherwise
        search for the expression in each model, and return the first
        value found.
        
        Arguments:
        - `*models`: a list of models
        """
        if expr.value != None:
            return expr.value
        else:
            for m in models:
                try:
                    return m[expr]
                except KeyError:
                    pass
        if strict:
            raise NoValue(expr)
        else:
            return None

    def visit_app(self, expr, strict, *models):
        """
                
        Arguments:
        - `*models`: a list of models
        """
        v = map(lambda expr: self.visit(expr, strict, *models), expr.args)
        f = self.visit(expr.fun, strict, *models)
        if strict:
            return f(*v)
        else:
            return bottom_lift(f, v)

    def visit_abs(self, expr, strict, *models):
        """
        
        Arguments:
        - `*models`: a list of models
        """
        def lam(*vals):
            """Returns a function which takes a list of vars,
            checks that it has the same length as vars
            and returns the expr interpreted in the model
            extended with the mapping vars -> vals
            
          Arguments:
            - `vals`: a list of values
            """
            if len(vals) != len(expr.vars):
                raise ValueError("Bad number of arguments")
            val_model = Model(zip(expr.vars, vals))
            return self.visit(expr.body, strict, *(list(models) + [val_model]) )

        return lam
        
    def visit_forall(self, expr, strict, *models):
        """Return the value of a universal statement:
        raise DomainInfinite if any variable has an infinite domain,
        otherwise try evaluation over every element of the domain
        return True if it is true, False otherwise, and update
        counterexample accordingly.
        
        Arguments:
        - `*models`: a sequence of models
        """
        dom_type = ProdType( *map(lambda e: e.etype(), expr.vars) )
        # TODO: make enumeration of the values of a domain LAZY:
        # the values should be produced on call rather than at the call
        # of TypeValue().visit.
        domain = TypeValue().visit(dom_type, *models)

        def value_fun(val):
            if len(expr.vars) != len(val):
                raise ValueError("Bad number of arguments")
            val_model = Model(zip(expr.vars, list(val)))
            return self.visit(expr.body, strict,\
                              *(list(models) + [val_model]) )

        if strict:
            t, e = strict_forall(domain.values(), value_fun)
            if not t:
                expr.counterexample.append((e, models))
            return t
        else:
            t, e = non_strict_forall(domain.values(), value_fun)
            if not t:
                expr.counterexample.append((e, models))
            return t

    def visit_exists(self, expr, strict, *models):
        """Return the value of an existential statement:
        raise DomainInfinite if any variable has an infinite domain,
        otherwise try evaluation over every element of the domain
        return True if it is true, False otherwise, and update
        witness accordingly.
        
        Arguments:
        - `*models`: a sequence of models
        """
        dom_type = ProdType( *map(lambda e: e.etype(), expr.vars) )
        domain = TypeValue().visit(dom_type, *models)

        def value_fun(val):
            if len(expr.vars) != len(val):
                raise ValueError("Bad number of arguments")
            val_model = Model(zip(expr.vars, list(val)))
            return self.visit(expr.body, strict,\
                              *(list(models) + [val_model]) )

        if strict:
            t, e = strict_exists(domain.values(), value_fun)
            if t:
                expr.witness.append((e, models))
            return t
        else:
            t, e = non_strict_exists(domain.values(), value_fun)
            if t:
                expr.witness.append((e, models))
            return t
 
        
def value(expr, strict, *models):
    """Return the value of an expr
    
    Arguments:
    - `expr`: an expression
    - `strict`: a boolean
    - `*models`: a list of models
    """
    if strict:
        logic_mod = built_in_strict
    else:
        logic_mod = built_in_non_strict
    models_all = list(models) + [built_in_all, logic_mod]
    return ExprValue().visit(expr, strict, *models_all)

def val_strict(expr, *models):
    return value(expr, True, *models)

def val_non_strict(expr, *models):
    return value(expr, False, *models)


################################################################################
#
# built-in models
#
################################################################################

built_in_all = Model()

def val_plus(a, b):
    return a + b

def val_times(a, b):
    return a * b

built_in_all[plus]         = val_plus
built_in_all[Sum]          = lambda *args: reduce(val_plus, args, 0)
built_in_all[times]        = val_times
built_in_all[Product]      = lambda *args: reduce(val_times, args, 1)
built_in_all[sub]          = lambda a, b: a - b
built_in_all[div]          = lambda a, b: a/b
built_in_all[power]        = pow
built_in_all[neg]          = lambda a: -a
built_in_all[absf]         = abs
built_in_all[Min]          = min
built_in_all[Max]          = max
built_in_all[less_than]    = lambda a, b: a < b
built_in_all[less_eq]      = lambda a, b: a <= b
built_in_all[greater_than] = lambda a, b: a > b
built_in_all[greater_eq]   = lambda a, b: a >= b

built_in_all[Bool] = Domain('Bool', lambda : (True, False), mem = None,
                            from_name = bool, is_finite = True)

built_in_strict = Model()

built_in_strict[equals]     = strict_eq
built_in_strict[not_equals] = strict_neq
built_in_strict[true]       = strict_true()
built_in_strict[false]      = strict_false()
built_in_strict[conj]       = strict_conj
built_in_strict[disj]       = strict_disj
built_in_strict[implies]    = strict_impl
built_in_strict[bneg]       = strict_neg
built_in_strict[And]        = strict_and
built_in_strict[Or]         = strict_or


built_in_non_strict = Model()

built_in_non_strict[equals]     = non_strict_eq
built_in_non_strict[not_equals] = non_strict_neq
built_in_non_strict[true]       = non_strict_true()
built_in_non_strict[false]      = non_strict_false()
built_in_non_strict[conj]       = non_strict_conj
built_in_non_strict[disj]       = non_strict_disj
built_in_non_strict[implies]    = non_strict_impl
built_in_non_strict[bneg]       = non_strict_neg
built_in_non_strict[And]        = non_strict_and
built_in_non_strict[Or]         = non_strict_or




