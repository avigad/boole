################################################################################
#
# expr.py
#
# description: basic types and expressions in Boole
#
#
# Authors:
# Jeremy Avigad
# Cody Roux
#
#
################################################################################

from language import Language, built_in_language, get_language, \
  null_language, global_language, set_default_language


################################################################################
#
# Miscellaneous useful procedures
#
################################################################################

# this used for functions that take either a single argument or a list
def _mk_list(l):
    if isinstance(l, list):
        return l
    else:
        return [l]
    
# this is used for a function that returns either a single elements or a tuple
def _unmk_list(l):
    if len(l) == 1:
        return l[0]
    else:
        return tuple(l)
        
# this is used for functions that take a string, consisting either of
# a single name, or a list of names, e.g.
#
#   Int('x')
#   Int('x y z')
#   Int('x,y,z')
#
# It is modeled after Sage's SR.var
def _str_to_list(s):
    if ',' in s:
        return [item.strip() for item in s.split(',')]
    elif ' ' in s:
        return [item.strip() for item in s.split()]
    else:
        return [s]


################################################################################
#
# Exceptions associated with Types
#
################################################################################

class TypeError(Exception):
    """Class of all possible type errors
    """
    
    def __init__(self, mess):
        """
        Arguments:
        -`mess`: a string that represents the error message
        """
        Exception.__init__(self, mess)

        
class NonFunType(TypeError):
    """Raised when trying to treat a non-functional type
    as a functional type
    """
    
    def __init__(self, etype):
        """
        
        Arguments:
        - `etype`: the etype that raised the error
        """
        TypeError.__init__(self, "Non functional type error.")
        self.etype = etype

        
class TypeMismatch(TypeError):
    """Raised when making a bad application"""

    def __init__(self, actual, expected):
        """
        
        Arguments:
        - `actual`: the actual type of the expr
        - `expected`: the expected type of the expression
        """
        mess = "Bad application: actual=" + str(actual) + " expected=" + \
            str(expected)
        TypeError.__init__(self, mess)
        self.actual = actual
        self.expected = expected


class FunTypeError(TypeError):
    """Raised when performing an illegal operation
    on a functional type.
    """
    def __init__(self, mess):
        """
        
        Arguments:
        - `mess`:
        """
        TypeError.__init__(self, mess)



################################################################################
#
# The class of types that an expression can have
#
################################################################################

class Type(object):
    """Parent class for types of expressions
    """
    
    def __init__(self):
        pass


    def __eq__(self, etype):
        return hash(self) == hash(etype)

    def __call__(self, s, language = None, **kwargs):
        """Creates a new constant of that type
        
        Arguments:
        - `s`: A list of variable names, such as 'x', 'x y z', or 'x, y, z'
        - `language`: A language to associate them with
        """
        
        language = get_language(language)
        args = _str_to_list(s)
        consts = ()
        for a in args:
            consts += (Const(a, self, language = language),)
        return _unmk_list(consts)

    def __mul__(self, t):
        """Return the product type self * t
        """
        return prodType(self, t)

    def __rshift__(self, t):
        """Return the arrow type self >> t
        """
        return FunType(dom = self, codom = t)

    def iomap(self, type):
        """Raises NonFunType(self)
        by default, overriden by FunType.
        
        Arguments:
        - `type`: an arbitrary type
        """
        raise NonFunType(self)


class BasicType(Type):
    """User-declared basic types
    """
    
    def __init__(self, name, value = None, language = None, supertypes = []):
        """
        
        Arguments:
        - `name`: a string that represents the name of the type
        - `value`: a domain that interprets the base type
        - `language`: the language to associate it with
        - `supertypes`: a list of supertypes of this type
        """
        Type.__init__(self)
        self.name = name
        self.value = value
        self.supertypes = supertypes + [self]
        language = get_language(language)
        language.add_type(self)


    def __eq__(self, etype):
        """Equality of base types is by -name- only.
        
        Arguments:
        - `etype`: An arbitrary etype
        """
        if isinstance(etype, BasicType):
            return self.name == etype.name
        else:
            return False



    def __str__(self):
        return self.name

    def is_super(self, type):
        """Check if type is a supertype of self.
        
        Arguments:
        - `etype`: an etype
        """
        if isinstance(type, Star):
            type = Star.factor
        # TODO: check that equality is well-implemented for types
        return type in self.supertypes

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_basic(self, *args, **kwargs)


class EnumType(Type):
    """An enumerated type is simply a list of strings with a name.
    """
    
    def __init__(self, name, elts, language = None):
        """
        
        Arguments:
        - `name`: String representing Name of the enumerated type
        - `elts`: a list of strings
        - `language`: the language to associate it with
        """
        Type.__init__(self)
        self.name = name
        language = get_language(language)
        language.add_type(self)
        self.elts = elts
        
    def make_constants(self, language = None):
        """
        Create a tuple of constants denoting the elements. So,
        for example, a constant named 'Alice' denotes the element 'Alice'.
        
        Arguments:
        - `language`: the language to associate it with
        """        
        constants = []
        for name in self.elts:
            constants.append(Const(name, self, value = name, 
                              language = language))
        return tuple(constants)
       
    def __str__(self):
        return self.name

    # TODO: allow structural subtyping here?
    def is_super(self, type):
        """Returns true if and only if self == type
        
        Arguments:
        - `type`: a type
        """
        return self == type

    # TODO: revisit; is this needed?
    def mem(self, s):
        """Returns True if s is in elts and False otherwise.
        
        Arguments:
        - `x`: an expr
        """
        return s in self.elts

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_enum(self, *args, **kwargs)


class ProdType(Type):
    """A finite product of types: is used to give
    a type to any (finite) enumeration of well-typed
    exprs
    """
    
    def __init__(self, *factors):
        """
        
        Arguments:
        - `*factors`: a finite enumeration of types
        """
        Type.__init__(self)
        self.factors = list(factors)

    def __str__(self):
        """
        """
        return ' * '.join(map(str, self.factors))

    def is_super(self, type):
        """Returns true if type is a supertype
        of self. Product types are compared
        componentwise.
        
        Arguments:
        - `type`: an arbitrary type
        """
        i = len(self.factors)
        if isinstance(type, Star):
            for k in range(i):
                if not self.factors[k].is_super(type.factor):
                    return False
            return True
        elif isinstance(type, ProdType):
            for k in range(i):
                if not self.factors[k].is_super(type.factors[k]):
                    return False
            return True
        else:
            return False

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_prod(self, *args, **kwargs)


def prodType(t1, t2):
    """Takes a pair of types and returns the product of those
    two types, while "flattening" the first type if it is
    already a product.
    
    Arguments:
    - `t1`: a type
    - `t2`: a type
    """
    if isinstance(t1, ProdType):
        return ProdType(*(t1.factors + [t2]))
    else:
        return ProdType(t1, t2)


class Star(Type):
    """A finite product of types: is used to give
    a type to any (finite) enumeration of well-typed
    exprs
    """
    
    def __init__(self, factor):
        """
        
        Arguments:
        - `factors`: a type
        """
        Type.__init__(self)
        # TODO: check factor is not itself a star type or product type?
        self.factor = factor

    def __str__(self):
        """
        """
        return 'Star(' + str(self.factor) + ')'

    def is_super(self, type):
        """Returns true if type is a supertype
        of self.
        
        Arguments:
        - `type`: an arbitrary type
        """
        if not isinstance(type, Star):
            return False
        else:
            return self.factor.is_super(type.factor)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_star(self, *args, **kwargs)


class FunType(Type):
    """The type of functions: to be more flexible,
    the output type can be parametrized by the input type: this
    allows ad-hoc polymorphism.
    """
    
    def __init__(self, dom = None, codom = None, iomap = None):
        """
        
        Arguments:
        - `dom`: The input type
        - `codom`: The output type
        - `iomap`: A function which takes an input type and
        returns an output type, or raises an error if there is none
        """
        Type.__init__(self)
        self.dom = dom
        self.codom = codom
        self.iomap = self._init_io(dom, codom, iomap)

    def _init_io(self, dom, codom, iomap):
        """Returns
        - iomap if it is not None
        - otherwise returns a function which tests a
        given type for being a subtype of dom,
        and returns codom if it is, and raises
        TypeMismatch(type, dom) otherwise.
        """
        if iomap != None:
            return iomap
        elif (dom != None) and (codom != None):
            def check_app(type):
                if type.is_super(dom):
                    return codom
                else:
                    raise TypeMismatch(type, dom)

            return check_app
        else:
            raise FunTypeError("Underspecified arrow type")
        
    def __str__(self, ):
        """Print a functional type as dom -> codom
        or <poly> if it is ad-hoc polymorphic
        """
        if (self.dom != None) and (self.codom != None):
            return str(self.dom) + ' >> ' + str(self.codom)
        elif self.iomap != None:
            return "<polymorphic>"
        else:
            raise FunTypeError("Underspecified arrow type")

    def is_super(self, type):
        """Returns true if type is a supertype of self.
        Comparisons are contravariant in the domain
        and covariant in the codomain.
        
        Arguments:
        - `type`: any type
        """
        if not isinstance(type, FunType):
            return False
        elif (self.dom != None and self.codom != None and
            type.dom != None  and type.codom != None):
            return (type.dom.is_super(self.dom) and
                    self.codom.is_super(type.codom))
        else:
            raise FunTypeError("Can't compare polymorphic types")

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_fun(self, *args, **kwargs)


################################################################################
#
# Exceptions associated with expressions
#
################################################################################

class ExprError(Exception):
    """Errors for expressions
    """
    def __init__(self, expr):
        Exception.__init__(self)
        self.expr = expr


class NoValue(ExprError):
    """Raised if the constant or base type has no value
    """
    def __init__(self, expr):
        """
        
        Arguments:
        - `expr`:
        """
        Exception.__init__(self, "The constant "+str(expr)+" has no value.")
        self.expr = expr
        

class NoType(TypeError):
    """Raised if the expression has no type
    """

    def __init__(self, expr):
        """Raised if the constant has no default type.
        
        Arguments:
        - `expr`:
        """
        Exception.__init__(self, "The constant "+str(expr)+" has no type.")
        self.expr = expr


class BadApp(TypeError):
    """Raised if there is a type mismatch in an application
    """
    
    def __init__(self, actual, expected, expr):
        """
        
        Arguments:
        - `actual`: the type of the arguments
        - `expected`: the domain of the function
        - `expr`: the application
        """
        mess = ("Bad application in {0!s}: actual type = {1!s}, "
            "expected = {2!s}").format(expr, actual, expected)
        TypeError.__init__(self, mess)
        self.actual = actual
        self.expected = expected
        self.expr = expr

        
class NonFunTypeApp(TypeError):
    """Raised if there is an application to an expression
    of non functional type.
    """

    def __init__(self, expr, type):
        """
        
        Arguments:
        - `expr`: the expression being applied
        """
        mess = "The expression: {0!s}\
        is of type {1!s} which is non-functional.".format(expr, type)
        TypeError.__init__(self, mess)
        self.expr = expr
        self.type = type

       
class EnumError(ExprError):
    """Raised if a name n is not found in the
    enumeration type e.
    """
    
    def __init__(self, enum, name):
        """
        
        Arguments:
        - `enum`: an enumeration type
        - `name`: a string
        """
        self.enum = enum
        self.name = name
        

################################################################################
#
# The general class for expressions, which include terms and
# formulas (expressions of type bool)
#
################################################################################

def to_expr(e):
    """Takes a python object and coerces it to an
    expression if possible, does nothing otherwise.
    
    Arguments:
    - `e`: a python object
    """
    if isinstance(e, Expr):
        return e
    elif isinstance(e, int):
        return ii(e)
    elif isinstance(e, float):
        return rr(e)
    else:
        raise TypeError('Expected an object of type Expr')


class Expr(object):
    """Class of general expressions
    """
    
    def __init__(self):
        """Initialize an Expr
        """
        pass

    def __str__(self):
        """Give the string representation of an expression
        """
        return "<abstr>"

    def __call__(self, *exprs):
        """Calling an expression on arguments creates the expression
        that is an application with arguments expr_list
        
        Arguments:
        - `*expr_list`: a tuple of python objects. They are coerced
        to Expr.
        """
        args = map(to_expr, list(exprs))
        return App(self, args)
    
    def etype(self):
        """Return the type of the expression
        """
        raise NoType(self)

    def has_type(self):
        """Return True if self is well-typed and
        false otherwise.
        """
        try:
            self.etype()
            return True
        except TypeError:
            return False

    def accept(self, visitor, *args, **kwargs):
        """The accept method takes a visitor as argument
        and calls the appropriate method of visitor on self.
        
        Arguments:
        - `visitor`: The visitor obeject with methods
        visit_const, visit_app, etc
        - `*args`: arguments to the visitor
        - `**kwargs`: named args to the visitor
        """
        raise NotImplementedError()

    # The rest of the class translates Python syntax to built in functions
    # and predicates defined below
    
    def __eq__(self, expr):
        return equals(self, to_expr(expr))
    
    def __ne__(self, expr):
        return not_equals(self, to_expr(expr))
    
    def __and__(self, expr):
        return conj(self, expr)

    def __or__(self, expr):
        return disj(self, expr)
    
    def __rshift__(self, expr):     # used for implication
        return implies(self, expr)

    def __invert__(self):           # used for boolean negation
        return bneg(self)
    
    def __add__(self, expr):
        return plus(self, to_expr(expr))
  
    def __mul__(self, expr):
        return times(self, to_expr(expr))

    def __sub__(self, expr):
        return sub(self, to_expr(expr))

    def __div__(self, expr):
        return div(self, to_expr(expr))

    def __pow__(self, expr):
        return power(self, to_expr(expr))

    def __neg__(self):
        return neg(self)
        
    def __abs__(self):
        return absf(self)
        
    def __lt__(self, expr):
        return less_than(self, to_expr(expr))
        
    def __le__(self, expr):
        return less_eq(self, to_expr(expr))
        
    def __gt__(self, expr):
        return greater_than(self, to_expr(expr))
    
    def __ge__(self, expr):
        return greater_eq(self, to_expr(expr))

    def __radd__(self, expr):
        return plus(to_expr(expr), self)

    def __rmul__(self, expr):
        return times(to_expr(expr), self)

    def __rsub__(self, expr):
        return sub(to_expr(expr), self)

    def __rdiv__(self, expr):
        return div(to_expr(expr), self)

    def __rpow__(self, expr):
        return power(to_expr(expr), self)


class Const(Expr):
    """Constants and variables
    """
    
    def __init__(self, name, type = None, value = None, 
                 language = None, **kwargs):
        """Initialize a constant
        
        Arguments:
        - `name`: string
        - `value`: any python object representing the value of the constant;
        this overrides the value that may be given by a model.
        - `language`: the language to associate it with
        - `etype` : an optional Etype
        - `infix` : a boolean that is true if the constant is an
        infix function symbol.
        """
        language = get_language(language)
        Expr.__init__(self)
        self.name = name
        self.value = value
        self.type_ = type
        self.attributes = kwargs
        language.add_const(self)

    def __str__(self):
        """String representation of a constant
        """
        return self.name
 
    def etype(self):
        """Return the type of the constant
        """
        if self.type_ != None:
            return self.type_
        else:
            raise NoType(self)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_const(self, *args, **kwargs)


class App(Expr):
    """Applications
    """
    
    def __init__(self, fun, args, **kwargs):
        """
        
        Arguments:
        - `term`: An expression
        - `args`: A list of expressions
        """
        Expr.__init__(self, **kwargs)
        self.fun = fun
        self.args = args
        
    def __str__(self):
        """String representation of an application
        """
        def par(expr):
            """Return the string representation of an expr,
            add parentheses if needed.
            
            Arguments:
            - `expr`: an expression
            """
            if isinstance(expr, Const):
                return str(expr)
            else:
                return "(" + str(expr) + ")"

        # special printing for infix symbols
        if isinstance(self.fun, Const) and len(self.args) == 2 and \
                'infix' in self.fun.attributes.keys():
            infix = self.fun.attributes['infix']
            return par(self.args[0]) + " " + infix + " " + \
                par(self.args[1])
        # special printing for prefix symbols
        elif isinstance(self.fun, Const) and len(self.args) == 1 and \
                'prefix' in self.fun.attributes.keys():
            prefix = self.fun.attributes['prefix']
            return prefix + par(self.args[0])
        else:
            return str(self.fun) + '(' + ", ".join(map(str, self.args)) + ')' 

    def etype(self):
        """
        Compute the type of the arguments: as a product type if the
        number of arguments is different than 1, the type of the
        single argument otherwise. Return the output of iomap
        of fun applied to this type.
        """
        fun_type = self.fun.etype()
        if len(self.args) == 1:
            arg_type = self.args[0].etype()
        else:
            arg_type = ProdType(*map(lambda expr: expr.etype(), self.args))
        try:
            return fun_type.iomap(arg_type)
        except TypeMismatch, e:
            raise BadApp(e.actual, e.expected, self)
        except NonFunType, e:
            raise NonFunTypeApp(self.fun, fun_type)
        
        
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_app(self, *args, **kwargs)


class Abs(Expr):
    """The abstraction of an expression over a list of variables.
    """
    
    def __init__(self, vars, body, **kwargs):
        """
        
        Arguments:
        - `vars`: a list of constants; no constant should have a value!
        - `body`: the expression that is to be abstracted over
        """
        Expr.__init__(self, **kwargs)
        self.vars = vars
        self.body = body
        
    def __str__(self):
        """String representation of an abstraction
        """
        if len(self.vars) == 1:
            var_str = str(self.vars[0])
        else:
            var_str = "[" + ", ".join(map(str, self.vars)) + "]"
        return ("Abs(" + var_str + ",  " + str(self.body) + ")")

    def etype(self):
        """
        """
        dom_type = ProdType( *map(lambda expr: expr.etype(), self.vars))
        return dom_type >> self.body.etype()

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_abs(self, *args, **kwargs)

        
class Forall(Expr):
    """The universal quantification of a formula over
    a list of variables.
    """
    
    def __init__(self, vars, body, **kwargs):
        """
        
        Arguments:
        - `vars`: a constant or a list of constants: no constant should have a value!
        - `body`: an expression, preferably of type Bool.
        counterexample contains a list of pairs of counterexamples and models.
        """
        Expr.__init__(self, **kwargs)
        if isinstance(vars, Const):
            self.vars = [vars]
        else:
            self.vars = vars
        self.body = body
        self.counterexample = []

    def __str__(self):
        """
        """
        if len(self.vars) == 1:
            var_str = str(self.vars[0])
        else:
            var_str = "[" + ", ".join(map(str, self.vars)) + "]"
        return ("Forall(" + var_str + ", " + str(self.body) + ")")

    def etype(self):
        """Return the type of a forall statement:
        simply compute the type of the body, and if it
        is boolean (and well typed) then return Bool
        """
        # Note that we do not check if a variable
        # with name 'x' has same type in body and
        # vars
        if Bool.is_super(self.body.etype()):
            return Bool
        else:
            raise TypeMismatch(self.body.etype(), Bool)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_forall(self, *args, **kwargs)
    

class Exists(Expr):
    """The Existential quantification of a formula over
    a list of variables.
    """
    
    def __init__(self, vars, body, **kwargs):
        """
        
        Arguments:
        - `vars`: a list of constants: no constant should have a value!
        - `body`: an expression, preferably of type Bool.
        witness contains a list of pairs of counterexamples and models.
        """
        Expr.__init__(self, **kwargs)
        if isinstance(vars, Const):
            self.vars = [vars]
        else:
            self.vars = vars
        self.body = body
        self.witness = []

    def __str__(self):
        """
        """
        if len(self.vars) == 1:
            var_str = str(self.vars[0])
        else:
            var_str = "[" + ", ".join(map(str, self.vars)) + "]"
        return ("Exists(" + var_str + ", " + str(self.body) + ")")

    def etype(self):
        """Return the type of an exists statement:
        simply compute the type of the body, and if it
        is boolean (and well typed) then return Bool
        """
        # Note that we do not check if a variable
        # with name 'x' has same type in body and
        # vars
        if Bool.is_super(self.body.etype()):
            return Bool
        else:
            raise TypeMismatch(self.body.etype(), Bool)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_exists(self, *args, **kwargs)


################################################################################
#
# The visitor classes for Expr and Type
#
################################################################################

class TypeVisitor(object):
    """Dispatch appropriate methods for each
    subclass of Type.
    """
    
    def __init__(self):
        """Do nothing by default.
        """
        pass

    def visit_basic(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_enum(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_prod(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_star(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_fun(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit(self, t, *args, **kwargs):
        """Visit a type
        
        Arguments:
        - `t`:
        - `*args`:
        - `**kwargs`:
        """
        return t.accept(self, *args, **kwargs)


class ExprVisitor(object):
    """Visit an expression.
    """
    
    def __init__(self):
        """Do nothing by default.
        """
        pass

    def visit_const(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_app(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_abs(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_forall(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit_exists(self, *args, **kwargs):
        """
        """
        raise NotImplementedError()

    def visit(self, expr, *args, **kwargs):
        """
        
        Arguments:
        - `expr`: an expression
        """
        return expr.accept(self, *args, **kwargs)


################################################################################
#
# Built-in types and expressions
#
################################################################################

Real = BasicType('Real', language = built_in_language)
Int = BasicType('Int', language = built_in_language, supertypes = [Real])
Bool = BasicType('Bool', language = built_in_language)


#
# Equality and disequality. Note that these are polymorphic.
#

def poly_bin_pred(dom):
    """From a product of types, check
    if one type is a subtype of the other
    and return the largest.
    
    Arguments:
    - `dom`: A product type with two factors
    """
    a = dom.factors[0]
    b = dom.factors[1]

    if not (a.is_super(b) | b.is_super(a)):
        raise FunTypeError(
            'Cannot compare elements of {0!s} and {1!s}'.format(a,b))
    return Bool
    
equals = Const('equals', 
               FunType(codom = Bool, iomap = poly_bin_pred),
               # value = (lambda a, b: a == b),
               language = built_in_language, 
               infix = '==')

not_equals = Const('not_equals', 
               FunType(codom = Bool, iomap = poly_bin_pred),
               # value = (lambda a, b: a != b),
               language = built_in_language, 
               infix = '!=')


#
# Boolean constants and operations
#

true =    Const('true', 
              Bool, 
              # value = True, 
              language = built_in_language)

false =   Const('false', 
              Bool, 
              # value = False, 
              language = built_in_language) 

conj =    Const('conj', 
              Bool * Bool >> Bool, 
              # value = (lambda a, b: a & b), 
              language = built_in_language, 
              infix = '&')

disj =    Const('disj', 
              Bool * Bool >> Bool, 
              # value = (lambda a, b: a | b), 
              language = built_in_language, 
              infix = '|')

implies = Const('implies', 
              Bool * Bool >> Bool, 
              # value = (lambda a, b: (not a) or b), 
              language = built_in_language, 
              infix = '>>')

bneg =    Const('bneg',
              Bool >> Bool,
              # value = (lambda a: not a),
              language = built_in_language,
              prefix = "~")

And =     Const('And',
              Star(Bool) >> Bool,
              # value = lambda *args: reduce(lambda x, y: x & y, args, True),
              language = built_in_language)

Or =      Const('Or',
              Star(Bool) >> Bool,
              # value = lambda *args: reduce(lambda x, y: x | y, args, False),
              language = built_in_language)


#
# Numeric operations and predicates.
#
# These require a special form of polymorphism, since an Int can be 
# coerced to a Real.
#
# TODO: use a more general Numeric class instead of Real
#

def arith_un_pred(dom):
    if not dom.is_super(Real):
        raise FunTypeError('{0!s} is not a numeric type'.format(dom))
    return Bool

def arith_un_func(dom):
    if not dom.is_super(Real):
        raise FunTypeError('{0!s} is not a numeric type'.format(dom))
    return dom

def _is_arith_type_list(type_list):
    """
    Takes a list of types, and returns True if all are numeric types.
    """
    
    for t in type_list:
        if not t.is_super(Real):
            return False
    return True

def _max_arith_type_list(type_list):
    """
    Takes a list of types, assumed to be numeric types, and returns
    a type subsuming all of them.
    """
    
    def join(t1, t2):
        if t1.is_super(t2):
            return t2
        elif t2.is_super(t1):
            return t1
        else:
            return Real
        
    return reduce(join, type_list, Int)

def arith_bin_pred(dom):
    if len(dom.factors) != 2:
        raise FunTypeError('Two arguments expected.')
    elif not _is_arith_type_list(dom.factors):
        raise FunTypeError('Arguments must have numeric types.')
    else:
        return Bool
    
def arith_bin_func(dom):
    if len(dom.factors) != 2:
        raise FunTypeError('Two arguments expected.')
    elif not _is_arith_type_list(dom.factors):
        raise FunTypeError('Arguments must have numeric types.')
    else:
        return _max_arith_type_list(dom.factors)
    
def arith_star_pred(dom):
    if not _is_arith_type_list(dom.factors):
        raise FunTypeError('Arguments must have numeric types.')
    else:
        return Bool
    
def arith_star_func(dom):
    if not _is_arith_type_list(dom.factors):
        raise FunTypeError('Arguments must have numeric types.')
    else:
        return _max_arith_type_list(dom.factors)

ArithUnFunc = FunType(dom = Real, codom = Real, iomap = arith_un_func)
ArithBinFunc = FunType(dom = Real * Real, codom = Real, iomap = arith_bin_func)
ArithStarFunc = FunType(dom = Star(Real), codom = Real, iomap = arith_star_func)
ArithUnPred = FunType(dom = Real, codom = Bool, iomap = arith_un_pred)
ArithBinPred = FunType(dom = Real * Real, codom = Bool, iomap = arith_bin_pred)
ArithStarPred = FunType(dom = Star(Real), codom = Bool, iomap = arith_star_pred)

# TODO: do we really want both binary plus and sum?
# simiarly for max and min

plus =    Const('plus', 
              ArithBinFunc,
              language = built_in_language, 
              infix = '+')

Sum =     Const('Sum',
             ArithStarFunc,
             language = built_in_language)

times =   Const('times', 
             ArithBinFunc,
             language = built_in_language, 
             infix = '*')

Product = Const('Product',
             ArithStarFunc,
             language = built_in_language)

sub =     Const('sub',
             ArithBinFunc,
             language = built_in_language,
             infix = '-')

div =     Const('div',
             ArithBinFunc,
             language = built_in_language,
             infix = '/')

power =   Const('power',
             ArithBinFunc,
             language = built_in_language,
             infix = '**')

neg =     Const('neg',
             ArithUnFunc,
             language = built_in_language,
             prefix = '-')

absf =    Const('abs',
             ArithUnFunc,
             language = built_in_language)

Min =     Const('min',
             ArithStarFunc,
             language = built_in_language)

Max =     Const('max',
             ArithStarFunc,
             language = built_in_language)

less_than =    Const('less_than', 
                    ArithBinPred,
                    language = built_in_language, 
                    infix = '<')

less_eq =      Const('less_eq', 
                    ArithBinPred,
                    language = built_in_language, 
                    infix = '<=')

greater_than = Const('greater_than', 
                    ArithBinPred,
                    language = built_in_language, 
                    infix = '>')

greater_eq =   Const('greater_eq', 
                    ArithBinPred,
                    language = built_in_language, 
                    infix = '>=')


# create a constant from a Python object
def const(c, type = None):
    """Define a constant with a fixed given value
    
    Arguments:
    - `c`: any python object
    """
    if type == None:
        s = 'const({0!s})'.format(c)
    else:
        s = 'const({0!s},{1!s})'.format(c,type)
    return Const(s, type, value = c, language = null_language)

# create an integer constant
def ii(n):
    return Const('ii({0!s})'.format(n), Int, int(n), null_language)

# create a real constant
def rr(x, language = null_language):
    return Const('rr({0!s})'.format(x), Real, float(x), null_language)


