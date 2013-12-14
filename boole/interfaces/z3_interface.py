###############################################################################
#
# z3_interface.py
#
# description: interface between Boole and Z3
#
###############################################################################

import operator

from boole.elaboration.prelude import *
from boole.elaboration.terms import *
from boole.core.expr import open_bound_fresh_consts
import boole.core.typing as ty
import boole.core.tactics as tac
import boole.core.conv as conv
import boole.semantics.value as value
from boole.semantics.value import Value, eval_expr

import z3

from fractions import Fraction

# TODO: what is the right way to test whether a type is a basic type, i.e.
# Real, Int, Bool, or a user-defined constant?

# TODO: in translation back to Boole, right now constants and variables
# are created anew. Instead, we should use constants and variables in the
# context.

# TODO: in the translation back to Boole, enumerated types are not
# handled correctly. (We just make a new type.)

###############################################################################
#
# Exceptions associated with Z3 interface
#
###############################################################################


class Z3_Interface_Error(Exception):
    """Class of all possible type errors
    """
    
    def __init__(self, mess=''):
        """
        Arguments:
        -`mess`: a string that represents the error message
        """
        Exception.__init__(self, mess)


class Z3_Unexpected_Type(Z3_Interface_Error):
    """Raised when trying to translate an unexpected type
    """
    def __init__(self):
        Z3_Interface_Error.__init__(self)


class Z3_Unexpected_Expression(Z3_Interface_Error):
    """Raised when there is a problem translating an expression
    """
    def __init__(self, expr):
        mess = 'Unexpected expression: {0!s}'.format(expr)
        Z3_Interface_Error.__init__(self, mess)




################################################################################
#
# These dictionaries gives the Z3 translations of the built-in symbols,
# built-in sorts, and Z3 functions for building constants of the built-in
# sorts.
#
################################################################################

_built_in_z3_funs = {
    eq.name: (lambda args, context: args[0] == args[1]),
    And.name: (lambda args, context: z3.And(args)),
    Or.name: (lambda args, context: z3.Or(args)),
    implies.name: 
        (lambda args, context: z3.Implies(args[0], args[1], context)),
    Not.name: (lambda args, context: z3.Not(args[0], context)),
    add.name: (lambda args, context: args[0] + args[1]),
    mul.name: (lambda args, context: args[0] * args[1]),
    minus.name: (lambda args, context: args[0] - args[1]),
    div.name: (lambda args, context: args[0] / args[1]),
    power.name: (lambda args, context: pow(args[0], args[1])),
    uminus.name: (lambda args, context: -args[0]),
    absf.name: (lambda args, context: abs(args[0])),
    lt.name: (lambda args, context: args[0] < args[1]),
    le.name: (lambda args, context: args[0] <= args[1])
# these are not used
#    ne.name: (lambda args, context: args[0] != args[1]),
#    Sum.name: (lambda args, context: z3.Sum(args)),
#    Product.name: (lambda args, context: z3.Product(args)),
#    gt.name: (lambda args, context: args[0] > args[1]),
#    ge.name: (lambda args, context: args[0] >= args[1])
}

_built_in_z3_sorts = {
    Int.name: z3.IntSort,
    Real.name: z3.RealSort,
    Bool.name: z3.BoolSort
}

_built_in_z3_sort_values = {
    Int.name: (lambda s, ctxt: z3.IntVal(int(s), ctxt)),
    Real.name: (lambda s, ctxt: z3.RealVal(float(s), ctxt)),
    Bool.name: (lambda s, ctxt: z3.BoolVal(bool(s), ctxt))
}


###############################################################################
#
# Convert Boole expressions to Z3 expressions
#
###############################################################################

def z3_to_fun(z3_expr):
    """Takes a FuncInterp instance, and returns
    the function which takes as input the value of
    a z3 expression and returns the value of the
    corresponding expression.

    Mutually recursive with z3_to_val
    
    Arguments:
    - `z3_expr`: an instance of FuncInterp
    """
    fun_list = z3_expr.as_list()
    other_val = z3_to_val(fun_list.pop())
    fun_list_val = [(z3_to_val(p[0]), z3_to_val(p[1]))\
                    for p in fun_list]
    fun_dict = dict(fun_list_val)
    def fun(a):
        try:
            return fun_dict[a]
        except KeyError:
            return other_val

    return fun


def z3_to_val(z3_expr):
    """Send a z3 expression to it's value
    as a python expression, if it has one,
    otherwise return the expresson itself.
    
    Arguments:
    - `z3_expr`: a z3 AST
    """
    if z3.is_int_value(z3_expr):
        return z3_expr.as_long()
    if z3.is_rational_value(z3_expr):
        return Fraction(z3_expr.numerator_as_long(), \
                        z3_expr.denominator_as_long())
    elif z3.is_true(z3_expr):
        return True
    elif z3.is_false(z3_expr):
        return False
    elif isinstance(z3_expr, z3.FuncInterp):
        return z3_to_fun(z3_expr)
    else:
        return z3_expr


class Boole_to_Z3(object):
    """
    Creates a Z3 context, and translates Boole expressions to that
    context, creating symbols as necessary.

    For example:

    C = Boole_to_Z3()
    print C(x + y)
    print C(f(x))
    
    The call of C(x + y) creates Z3 symbols for x and y.
    The call of C(f(x)) creates a Z3 symbol for f, but uses the previous x.
    
    Note: do not use the same name for symbols of different type!
    """
    
    def __init__(self, context=None):
        self.sort_dict = None
        self.symbol_dict = None
        self.context = None
        self.reset(context)

    def reset(self, context=None):
        if context != None:
            self.context = context
        else:
            self.context = z3.Context()
        self.sort_dict = {}        # sorts
        self.symbol_dict = {}      # constant and function symbols
        
    def make_z3_sort(self, name):
        z3_sort = z3.DeclareSort(name, self.context)
        self.sort_dict[name] = z3_sort
        return z3_sort
        
    def make_z3_enumerated_sort(self, name, elts):
        z3_sort, z3_elts = z3.EnumSort(name, elts, ctx=self.context)
        self.sort_dict[name] = z3_sort
        for e in z3_elts:
            self.symbol_dict[str(e)] = e
        return z3_sort

    def get_z3_sort(self, s):
        if s.is_bool():
            return _built_in_z3_sorts[Bool.name](self.context)
        elif not s.is_const():
            raise Z3_Unexpected_Type
        if s.name in self.sort_dict.keys():
            return self.sort_dict[s.name]
        elif s.name in _built_in_z3_sorts.keys():
            return _built_in_z3_sorts[s.name](self.context)
        elif s.value and s.value.desc == "enumtype_val":
            return self.make_z3_enumerated_sort(s.name, s.value.pyval)
        else:
            return self.make_z3_sort(s.name)

    def get_z3_fun_type(self, t):
        codom, dom_list = root_pi(t)
        arg_sorts = [self.get_z3_sort(t1) for t1 in dom_list]
        return_sort = self.get_z3_sort(codom)
        return (arg_sorts, return_sort)
        
    def get_z3_const(self, c):
        if c.name in self.symbol_dict.keys():
            # defined constant
            return self.symbol_dict[c.name]
        elif c.value != None:    # interpreted constant
            etype = c.type
            if etype.name in _built_in_z3_sort_values.keys():
                val_trans = _built_in_z3_sort_values[etype.name]
                return val_trans(c.value.pyval, self.context)
            elif etype.value and etype.value.desc == "enumtype_val":
                self.get_z3_sort(etype)  # creates the enum type if not there
                return self.symbol_dict[c.value.pyval]
            else:
                raise Z3_Unexpected_Expression(c)
        else:
            # new constant
            etype, _ = ty.infer(c)
            return self.make_z3_const(etype, c.name)
        
    def make_z3_const(self, etype, name):
        if etype.equals(Bool) or etype.is_const():
            z3_sort = self.get_z3_sort(etype)
            z3_const = z3.Const(name, z3_sort)
            self.symbol_dict[name] = z3_const
            return z3_const
        elif etype.is_bound() and etype.binder.is_pi():
            arg_sorts, return_sort = self.get_z3_fun_type(etype)
            z3_func = z3.Function(name, *(arg_sorts + [return_sort]))
            self.symbol_dict[name] = z3_func
            return z3_func
        else:
            raise Z3_Unexpected_Type('Cannot handle polymorphism')
        
    def handle_function(self, fun, args):
        """
        fun: Boole function symbol to apply
        args: z3 expressions, already translated
        """
        # note the different calling conventions
        if fun.name in self.symbol_dict.keys():
            # defined function symbol
            z3_fun = self.symbol_dict[fun.name]
            return z3_fun(*args)
        elif fun.name in _built_in_z3_funs.keys():
            # built-in function symbol
            z3_fun = _built_in_z3_funs[fun.name]
            return z3_fun(args, self.context)
        else:
            # new function symbol
            etype, _ = ty.infer(fun)
            z3_fun = self.make_z3_const(etype, fun.name)
            return z3_fun(*args)
       
    def __call__(self, expr):
        val = elab(expr)
        if val.is_const():
            return self.get_z3_const(val)
        elif val.is_app():
            fun, args = root_app_implicit(val)
            args = [self.__call__(a) for a in args]
            return self.handle_function(fun, args)
        elif val.is_forall():
            vlist, body = open_bound_fresh_consts(val)
            z3_vars = [self(v) for v in vlist]
            z3_body = self(body)
            return z3.ForAll(z3_vars, z3_body)
        elif val.is_exists():
            vlist, body = open_bound_fresh_consts(val)
            z3_vars = [self(v) for v in vlist]
            z3_body = self(body)
            return z3.Exists(z3_vars, z3_body)
        else:
            raise Z3_Unexpected_Expression(val)


###############################################################################
#
# Convert Z3 expressions to Boole expressions
#
# Because Z3 uses de Bruijn indices for bound variables, we have to
# gather the list of variable names as we traverse the formula. When we
# finally get to the bottom, bound_variables has all the variables indexed
# in reverse order.
#
###############################################################################

# TODO: relative this to a Boole context. Right now, we just
# create constants anew.
class Z3_to_Boole(object):
    
    def __init__(self, context=current_ctxt()):
        self.context = context
    
    def mk_sort(self, s):
        if s.name() == 'Int':
            return Int
        elif s.name() == 'Real':
            return Real
        elif s.name() == 'Bool':
            return Bool
        else:
            return self.context.decls[str(s)]
        ### return mktype(s.name())
        
    def mk_const(self, c):
        if z3.is_int_value(c):
            return ii(c.as_long())
        if z3.is_rational_value(c):
            # TODO: what should we convert a rational to?
            return rr(Fraction(c.numerator_as_long(), \
                               c.denominator_as_long()))
        elif z3.is_true(c):
            return true
        elif z3.is_false(c):
            return false
        else:
            try:
                return self.context.decls[str(c)]
            except KeyError:
                #Constant is not found in the context
                typ = self.mk_sort(c.sort())
                return const(str(c), typ)

    # WARNING: f.name() and str(f) are not identical!
    def mk_fun(self, f):
        try:
            return self.context.decls[str(f)]
        except KeyError:
            dom_types = [self.mk_sort(f.domain(i))\
                         for i in range(0, f.arity())]
            cod_type = self.mk_sort(f.range())
            dom_types.reverse()
            fun_type = reduce((lambda X, Y: type_arrow(Y, X)), \
                              dom_types, cod_type)
            return const(str(f), fun_type)

    def mk_app(self, f, args):
        if z3.is_eq(f):
            return args[0] == args[1]
        elif z3.is_and(f):
            return And(*args)
        elif z3.is_or(f):
            return Or(*args)
        elif z3.is_not(f):
            return Not(*args)
        elif z3.is_add(f):
            return reduce(operator.add, args[1:], args[0])
        elif z3.is_mul(f):
            return reduce(operator.mul, args[1:], args[0])
        elif z3.is_sub(f):
            return args[0] - args[1]
        elif z3.is_div(f):
            return args[0] / args[1]
        elif z3.is_lt(f):
            return args[0] < args[1]
        elif z3.is_le(f):
            return args[0] <= args[1]
        elif z3.is_gt(f):
            return args[0] > args[1]
        elif z3.is_ge(f):
            return args[0] >= args[1]
        elif z3.is_to_real(f):    # TODO: ignore coercions?
            return args[0]
        elif z3.is_to_int(f):
            return args[0]
        elif f.name() == '=>':
            return implies(args[0], args[1])
        else:
            dom_types = [self.mk_sort(f.domain(i))\
                         for i in range(0, f.arity())]
            cod_type = self.mk_sort(f.range())
            dom_types.reverse()
            fun_type = reduce((lambda X, Y: type_arrow(Y, X)), \
                              dom_types, cod_type)
            func = self.mk_fun(f)
            return func(*args)

    def __call__(self, expr):
        return elab(self.translate(expr))

    #TODO: remove mutable default value
    def translate(self, expr, bound_variables=[]):
        if z3.is_const(expr):
            return self.mk_const(expr)
#                raise Z3_Unexpected_Expression('Unrecognized constant')
        elif z3.is_var(expr):    # a de Bruijn indexed bound variable
            bv_length = len(bound_variables)
            return bound_variables[bv_length - z3.get_var_index(expr) - 1]
        elif z3.is_app(expr):
            args = [self.translate(expr.arg(i), bound_variables)
                for i in range(expr.num_args())]
            return self.mk_fun(expr.decl())(*args)

#            else:
#                raise Z3_Unexpected_Expression(expr)
        elif z3.is_quantifier(expr):
            num_vars = expr.num_vars()
#            vars = [language.const_dict[expr.var_name(i)]
#                for i in range(num_vars)]
            vars = [const(expr.var_name(i), self.mk_sort(expr.var_sort(i))) \
                for i in range(num_vars)]
            new_bound_variables = bound_variables + vars
            body = self.translate(expr.body(), new_bound_variables)
            if expr.is_forall():
                return forall(vars, body)
            else:
                return exists(vars, body)

        elif z3.is_func_decl(expr):
            return self.mk_fun(expr)
        else:
            print expr.kind
            raise Z3_Unexpected_Expression(expr)

    def model(self, m):
        """Takes a Z3 model and returns the corresponding
        Boole model.
        
        Arguments:
        - `m`: an instance of z3.ModelRef
        """
        eqs = {}
        vals = {}
        for d in m:
            if isinstance(m[d], z3.FuncInterp):
                interp = m[d].as_list()[:-1]
                interp = [[self.translate(p) for p in r] for r in interp]
                d_eqs = interp_to_eqns(self.translate(d), interp)
                for i, e in enumerate(d_eqs):
                    eqs[str(d) + 'def' + str(i)] = e
                vals[str(d)] = Value(z3_to_val(m[d]))
            else:
                eqs[str(d) + 'def'] = \
                             self.translate(d()) == self.translate(m[d])
                vals[str(d)] = Value(z3_to_val(m[d]))
        return value.Model(eqs, vals)
            

def interp_to_eqns(f, vals):
    """
    
    Arguments:
    - `f`: a function constant
    - `vals`: a list of lists of length `arity of f` + 1
    """
    eqns = []
    for v in vals:
        res = v.pop()
        eqns.append(f(*v) == res)
    return eqns


###############################################################################
#
# A class interface to the Z3 solver
#
###############################################################################

# TODO: relativize this to a Boole context?

class Z3_Solver(object):
    
    def __init__(self):
        self.boole_to_z3 = Boole_to_Z3()
        # self.z3_to_boole = Z3_to_Boole(get_language(language))
        self.solver = z3.Solver(ctx=self.boole_to_z3.context)
        
    def add(self, formula):
        z3_formula = self.boole_to_z3(elab(formula))
        return self.solver.add(z3_formula)
        
    def check(self):
        return self.solver.check()
       
    # returns the z3 model
    def z3_model(self):
        return self.solver.model()
        
    # converts it to a Boole model
    def model(self):
        raise NotImplementedError()
        # return self.z3_to_boole.model(self.z3_model())
        

if __name__ == '__main__':


    a, b, c = Int('a b c')

    #Puzzles taken from http://eclipseclp.org/examples/index.html

    #xkcd waiter puzzle:

    d, e = Int('d e')

    f = (Int >> Int)('f')

    xkcd = elab(a*215 + b*275 + c*335 + d*355 + e*420 + f(a)*580 == 1505)

    S = Z3_Solver()

    S.add(xkcd)

    positive = (And(a >= 0, b >= 0, c >= 0, d >= 0, e >= 0, f(a) >= 0))

    S.add(positive)

    print S.check()

    m = S.z3_model()

    print m

    f_val =  m[m[5]]

    print f_val.entry(0).arg_value(0)

    print f_val.as_list()

    # Causes segfault!
    # print m.eval(m[2])

    B = Z3_to_Boole()

    b_mod = B.model(m)

    # print b_mod.vals

    print eval_expr(a == d, b_mod)
    print eval_expr(a == b, b_mod)
    print eval_expr(elab(a*215 + b*275 + c*335 + d*355 + e*420 + f(a)*580), b_mod)
    print eval_expr(elab(xkcd), b_mod)


    print eval_expr(elab(positive), b_mod)
