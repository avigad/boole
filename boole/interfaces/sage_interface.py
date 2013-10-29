###############################################################################
#
# sage_interface.py
#
# description: interface between Boole and Sage
#
# Converts Boole expressions to Sage symbolic expressions and back.
#
# In the forward direction, the user specifies the symbolic ring, by
# default the_SymbolicRing().
#
# Note: this is meant to be called from Sage.
#
# TODO: associate domain information with sage constants?
# TODO: define function with arity?
# TODO: need to better understand symbolic functions
# TODO: "x^2" prints as "(x ** 2)"
# TODO: 2 is parsed as Integer(2), rather than the constant value\
# TODO: set domain when translating to Sage?
#
###############################################################################

from boole.elab.prelude import *
from boole.core.expr import open_bound_fresh_consts, ExprVisitor
import boole.core.typing as ty
import boole.core.tactics as tac

import sage.all

from sage.symbolic.expression_conversions import Converter
from sage.symbolic.ring import the_SymbolicRing
from sage.symbolic.function_factory import function_factory
import operator as _operator


###############################################################################
#
# These dictionaries gives the Sage translations of the built-in symbols,
# built-in sorts, and Sage functions for building constants of the built-in
# sorts.
#
###############################################################################

_built_in_sage_funs = {
    eq.name: (lambda args: args[0] == args[1]),
#    not_equals.name: (lambda args: args[0] != args[1]),
    add.name: (lambda args: args[0] + args[1]),
    mul.name: (lambda args: args[0] * args[1]),
    minus.name: (lambda args: args[0] - args[1]),
    div.name: (lambda args: args[0] / args[1]),
    power.name: (lambda args: pow(args[0], args[1])),
    uminus.name: (lambda args: -args[0]),
    absf.name: (lambda args: abs(args[0])),
    lt.name: (lambda args: args[0] < args[1]),
    le.name: (lambda args: args[0] <= args[1])
}

# TODO: use these to set the domain
#
#_built_in_sage_sorts = {
#    Int.name: z3.IntSort,
#    Real.name: z3.RealSort,
#    Bool.name: z3.BoolSort
#}

_built_in_sage_sort_values = {
    Int.name: (lambda val: sage.rings.integer.Integer(val)),
    Real.name: (lambda val: val),
    'Bool': (lambda val: val)
#    Bool.name: (lambda val: val)
}


###############################################################################
#
# Exceptions associated with the Sage interface
#
###############################################################################

class Sage_Interface_Error(Exception):
    """Class of all possible type errors
    """
    
    def __init__(self, mess=''):
        """
        Arguments:
        -`mess`: a string that represents the error message
        """
        Exception.__init__(self, mess)


class Sage_Unexpected_Type(Sage_Interface_Error):
    """Raised when trying to translate an unexpected type
    """
    pass


class Sage_Unexpected_Expression(Sage_Interface_Error):
    """Raised when there is a problem translating an expression
    """
    
    pass


###############################################################################
#
# Convert Sage expressions to Boole expressions
#
###############################################################################

# for now, put symbolic expressions in the global name space; later, allow
# user to specify any ring
# also, check global name space before creating these?

class _Expr_Trans(ExprVisitor):
    """Visitor class for translating an expression from Boole
    to Sage.
    """

    def __init__(self, translator):
        """
        Initialize with calling instance of Boole_to_Sage.
        """
        self.trans = translator
        
    def visit_const(self, expr):
        return self.trans.get_sage_var(expr)
    
    def visit_app(self, expr):
        fun, args = root_app_implicit(expr)
        args = [self.visit(arg) for arg in args]
        return self.trans.handle_function(fun, args)
    
    def visit_abs(self, expr):
        raise Sage_Unexpected_Expression(str(expr))
        
    def visit_bound(self, expr):
        raise Sage_Unexpected_Expression(str(expr))
    
    # TODO: what to do here?
    def visit_box(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_type(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_kind(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_bool(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_pair(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_fst(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_snd(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_ev(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_sub(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))

    def visit_mvar(self, expr, *args, **kwargs):
        raise Sage_Unexpected_Expression(str(expr))


class Boole_to_Sage(object):
    """
    Translates Boole expressions to a Sage symbolic expression ring,
    creating symbols as necessary.

    For example:

    C = Boole_to_Sage()
    print C(x + y)
    print C(f(x))
    
    The call of C(x + y) creates Sage variables for x and y.
    The call of C(f(x)) creates a Sage function variable for f,
    but uses the previous x.
    
    Note: do not use the same name for symbols of different type!
    """
    def __init__(self, target=None):
        if target == None:
            target = the_SymbolicRing()
        self.target = target
        self.symbol_dict = {}      # constant and function symbols
        self.expr_trans = _Expr_Trans(self).visit
        
    def reset(self, target=None):
        if target == None:
            target = the_SymbolicRing()
        self.target = target
        self.symbol_dict = {}      # constant and function symbols
    
    def make_sage_var(self, etype, name):
        # TODO: what to do with constants of type EnumType?
        # TODO: use domain
        sage_var = self.target.var(name)
        self.symbol_dict[name] = sage_var
        return sage_var
        
    def get_sage_var(self, c):
        if c.name in self.symbol_dict.keys():
            # defined constant
            return self.symbol_dict[c.name]
        elif c.value != None:
            # interpreted constant
            etype = c.type
            # TODO: this assumes that the type is a constant
            if etype.name in _built_in_sage_sort_values:
                val_trans = _built_in_sage_sort_values[etype.name]
                return val_trans(c.value.pyval)
            else:
                raise Sage_Unexpected_Expression(\
                    'Unrecognized value:' + str(c))
        else:
            # new constant
            return self.make_sage_var(c.type, c.name)

    def handle_function(self, fun, args):
        """
        fun: Boole function symbol to apply
        args: Sage expressions, already translated
        """
        if fun.name in self.symbol_dict.keys():
            # defined function symbol
            sage_fun = self.symbol_dict[fun.name]
            return sage_fun(*args)
        elif fun.name in _built_in_sage_funs.keys():
            # built-in function symbol
            sage_fun = _built_in_sage_funs[fun.name]
            return sage_fun(args)
        else:
            # new function symbol
            sage_fun = function_factory(fun.name)
            self.symbol_dict[fun.name] = sage_fun
            return sage_fun(*args)
       
    def __call__(self, expr):
        return self.expr_trans(elab(expr))


###############################################################################
#
# Convert Sage expressions to Boole expressions
#
###############################################################################

# TODO: use the context
class Sage_to_Boole(Converter):
    
    def __init__(self, context=None, use_fake_div=False):
#        language = get_language(language)
        self.context = context
        self.use_fake_div = use_fake_div
        
    def pyobject(self, ex, obj):
        # TODO: is there any reasonable way to assign a type
        # to this constant?
        if ex.is_integer():
            return ii(obj)
        elif ex.is_real():
            return rr(obj)
        # TODO: what to do here?           
        return const(repr(ex), type=None, value=Value(obj))

    def symbol(self, ex):
        # TODO: this is a hack!
        if ex.is_integer():
            return Int(repr(ex))
        elif ex.is_real():
            return Real(repr(ex))
        else:
            return Real(repr(ex))
#             raise Sage_Unexpected_Expression('symbol: ' + str(ex))
#         if repr(ex) in self.language.const_dict.keys():
#             return self.language.const_dict[repr(ex)]
#         else:
#             raise Sage_Unexpected_Expression('symbol: ' + str(ex))

    def relation(self, ex, operator):
        if operator == _operator.eq:
            return equals(self(ex.lhs()), self(ex.rhs()))
        elif operator == _operator.lt:
            return self(ex.lhs()) < self(ex.rhs())
        elif operator == _operator.gt:
            return self(ex.lhs()) > self(ex.rhs())
        elif operator == _operator.ne:
            return self(ex.lhs()) != self(ex.rhs())
        elif operator == _operator.le:
            return self(ex.lhs()) <= self(ex.rhs())
        elif operator == _operator.ge:
            return self(ex.lhs()) <= self(ex.rhs())
        else:
            raise Sage_Unexpected_Expression('relation: ' + str(ex))

    def arithmetic(self, ex, operator):
        if operator == _operator.add:
            return self(ex.operands()[0]) + self(ex.operands()[1])
        elif operator == _operator.sub:
            return self(ex.operands()[0]) - self(ex.operands()[1])
        elif operator == _operator.mul:
            return self(ex.operands()[0]) * self(ex.operands()[1])
        elif operator == _operator.div:
            return self(ex.operands()[0]) / self(ex.operands()[1])
        elif operator == _operator.pow:
            return power(self(ex.operands()[0]), self(ex.operands()[1]))
        else:
            raise Sage_Unexpected_Expression('arithmetic: ' + str(ex))

    def composition(self, ex, operator):
        op = str(operator)
        if str(op) in self.language.const_dict.keys():
            f = self.language.const_dict[op]
            args = map(self, ex.operands())
            return f(*args)
        else:
            raise Sage_Unexpected_Expression('composition: ' + str(ex))


if __name__ == '__main__':

    x = Real('x')

    e = x*x + x + 2

    C = Boole_to_Sage()

    C.make_sage_var(Real, "x")

    print C(e)

    # e_prime = sage.all.diff(C(e), x)
