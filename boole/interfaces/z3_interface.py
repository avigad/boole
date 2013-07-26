################################################################################
#
# z3_interface.py
#
# description: interface between Boole and Z3
#
################################################################################

from boole.elab.terms import *
import boole.core.typing as ty
import boole.core.tactics as tac
import boole.interfaces.ineq_interface as ineq

import z3

from fractions import Fraction

# TODO: what is the right way to test whether a type is a basic type, i.e.
# Real, Int, Bool, or a user-defined constant?

################################################################################
#
# Exceptions associated with Z3 interface
#
################################################################################

class Z3_Interface_Error(Exception):
    """Class of all possible type errors
    """
    
    def __init__(self, mess = ''):
        """
        Arguments:
        -`mess`: a string that represents the error message
        """
        Exception.__init__(self, mess)
        
class Z3_Unexpected_Type(Z3_Interface_Error):
    """Raised when trying to translate an unexpected type
    """
    pass

        
class Z3_Unexpected_Expression(Z3_Interface_Error):
    """Raised when there is a problem translating an expression
    """
    
    pass


################################################################################
#
# These dictionaries gives the Z3 translations of the built-in symbols,
# built-in sorts, and Z3 functions for building constants of the built-in
# sorts.
#
################################################################################

_built_in_z3_funs = {
    eq.name: (lambda args, context: args[0] == args[1]),
#    ne.name: (lambda args, context: args[0] != args[1]),
    conj.name: (lambda args, context: z3.And(args)),
#    And.name: (lambda args, context: z3.And(args)),
    disj.name: (lambda args, context: z3.Or(args)),
#    Or.name: (lambda args, context: z3.Or(args)),
    implies.name: 
        (lambda args, context: z3.Implies(args[0], args[1], context)),
    neg.name: (lambda args, context: z3.Not(args[0], context)),
    add.name: (lambda args, context: args[0] + args[1]),
#    Sum.name: (lambda args, context: z3.Sum(args)),
    mul.name: (lambda args, context: args[0] * args[1]),
#    Product.name: (lambda args, context: z3.Product(args)),
    minus.name: (lambda args, context: args[0] - args[1]),
    div.name: (lambda args, context: args[0] / args[1]),
    power.name: (lambda args, context: pow(args[0], args[1])),
    uminus.name: (lambda args, context: -args[0]),
    absf.name: (lambda args, context: abs(args[0])),
    lt.name: (lambda args, context: args[0] < args[1]),
    le.name: (lambda args, context: args[0] <= args[1]),
#    gt.name: (lambda args, context: args[0] > args[1]),
#    ge.name: (lambda args, context: args[0] >= args[1])
}

_built_in_z3_sorts = {
    Int.name: z3.IntSort,
    Real.name: z3.RealSort,
#    Bool.name: z3.BoolSort
    'Bool': z3.BoolSort
}

_built_in_z3_sort_values = {
    Int.name: (lambda s, ctxt: z3.IntVal(int(s), ctxt)),
    Real.name: (lambda s, ctxt: z3.RealVal(float(s), ctxt)),
    'Bool': (lambda s, ctxt: z3.BoolVal(bool(s), ctxt))
}


################################################################################
#
# Convert Boole expressions to Z3 expressions
#
################################################################################
       
        
class Boole_to_Z3:
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
    
    def __init__(self, context = None):
        self.reset(context)
        
    def reset(self, context = None):
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
        if s.equals(Bool):
            return _built_in_z3_sorts['Bool'](self.context)
        elif not s.is_const():
            raise Z3_Unexpected_Type
        if s.name in self.sort_dict.keys():
            return self.sort_dict[s.name] 
        elif s.name in _built_in_z3_sorts.keys():
            return _built_in_z3_sorts[s.name](self.context)              
#        else if s is an enumerated type:
            return self.make_z3_enumerated_sort(s.name, s.elts)
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
        elif c.info.is_const:
            # interpreted constant
            etype, _ = ty.infer(c)
            if etype.name in _built_in_z3_sort_values.keys():
                val_trans = _built_in_z3_sort_values[etype.name]
                return val_trans(c.name, self.context)
            else:
                raise Z3_Unexpected_Expression('Unrecognized value:' + str(c))                   
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
        if expr.is_const():
            return self.get_z3_const(expr)
        elif expr.is_app():
            fun, args = root_app_implicit(expr)
            args = [self.__call__(a) for a in args]
            return self.handle_function(fun, args)
        # elif is a forall or exists...
        else:
            raise Z3_Unexpected_Expression

            
            
################################################################################
#
# Convert Z3 expressions to Boole expressions
#
# Because Z3 uses de Bruijn indices for bound variables, we have to 
# gather the list of variable names as we traverse the formula. When we
# finally get to the bottom, bound_variables has all the variables indexed
# in reverse order.
#
################################################################################

#class Z3_to_Boole:
#    
#    def __init__(self, language = None):
#        self.language = get_language(language)
#        
#    def __call__(self, expr, bound_variables = []):    
#        language = self.language
#        if z3.is_const(expr):
#            if z3.is_rational_value(expr):
#                # TODO: think about this
#                return rr(Fraction(expr.numerator_as_long(), \
#                                   expr.denominator_as_long()))  
#            if z3.is_int_value(expr):
#                # TODO: cast to int?
#                return ii(expr.as_long())
#            elif str(expr) in language.const_dict.keys():
#                return language.const_dict[str(expr)]
#            elif z3.is_true(expr):
#                return true
#            elif z3.is_false(expr):
#                return false
#            else:
#                raise Z3_Unexpected_Expression('Unrecognized constant')
#        elif z3.is_var(expr):    # a de Bruijn indexed bound variable
#            bv_length = len(bound_variables)
#            return bound_variables[bv_length - z3.get_var_index(expr) - 1]
#        elif z3.is_app(expr):
#            args = [self(expr.arg(i), bound_variables) 
#                for i in range(expr.num_args())]
#            if expr.decl().name() in language.const_dict.keys():
#                func = language.const_dict[expr.decl().name()]
#                return apply(func, args)
#            elif z3.is_eq(expr):
#                return args[0] == args[1]
#            elif z3.is_and(expr):
#                return apply(conj, args)
#            elif z3.is_or(expr):
#                return apply(disj, args)
#            elif z3.is_not(expr):
#                return apply(bneg, args)       
#            elif z3.is_add(expr):
#                # TODO: use plus in binary case?    
#                return apply(Sum, args)
#            elif z3.is_mul(expr):
#                return apply(Product, args)
#            elif z3.is_sub(expr):
#                return args[0] - args[1]
#            elif z3.is_div(expr):
#                return args[0] / args[1]
#            elif z3.is_lt(expr):
#                return args[0] < args[1]
#            elif z3.is_le(expr):
#                return args[0] <= args[1]
#            elif z3.is_gt(expr):
#                return args[0] > args[1]
#            elif z3.is_ge(expr):
#                return args[0] >= args[1]
#            elif z3.is_to_real(expr):    # TODO: ignore coercions?
#                return args[0]
#            elif z3.is_to_int(expr):
#                return args[0]
#            else:
#                raise Z3_Unexpected_Expression('Unrecognized application: ' + \
#                                               str(expr))          
#        elif z3.is_quantifier(expr):
#            num_vars = expr.num_vars()
#            vars = [language.const_dict[expr.var_name(i)] 
#                for i in range(num_vars)]
#            new_bound_variables = bound_variables + vars
#            body = self(expr.body(), new_bound_variables)
#            if expr.is_forall():
#                return Forall(vars, body)
#            else:
#                return Exists(vars, body)
#            
#        else:
#            raise Z3_Unexpected_Expression         
#
#    def value(self, z3_val):    
#        if z3.is_true(z3_val):
#            return True
#        elif z3.is_false(z3_val):
#            return False
#        elif z3.is_int_value(z3_val):
#            return z3_val.as_long()
#        elif z3.is_rational_value(z3_val):
#            return Fraction(z3_val.numerator().as_long(), 
#                            z3_val.denominator().as_long())
#        elif z3.is_expr(z3_val):
#            return str(z3_val)
#        else:
#            print "Error: unrecognized z3 value", z3_val
#
#    def model(self, z3_model):
#        M = Model()
#        M.show()
#        for symbol in z3_model.decls():
#            if symbol.name() in self.language.const_dict.keys():
#                c = self.language.const_dict[symbol.name()]
#                M[c] = self.value(z3_model[symbol])        
#        return M


################################################################################
#
# A class interface to the Z3 solver
#
################################################################################

class Z3_Solver():
    
    def __init__(self, language = None):
        self.boole_to_z3 = Boole_to_Z3()
#        self.z3_to_boole = Z3_to_Boole(get_language(language))
        self.solver = z3.Solver(ctx = self.boole_to_z3.context)
        
    def add(self, formula):
        z3_formula = self.boole_to_z3(formula)
        return self.solver.add(z3_formula)
        
    def check(self):
        return self.solver.check()
       
    # returns the z3 model
    def z3_model(self):
        return self.solver.model()
        
    # converts it to a python dictionary
    def model(self):
        return self.z3_to_boole.model(self.z3_model())

################################################################################
#
# Test these out
#
################################################################################

if __name__ == '__main__':

    x = Real('x')
    y = Real('y')
    z = Real('z')
    i = Int('i')
    j = Int('j')
    k = Int('k')
    p = Bool('p')
    q = Bool('q')
    r = Bool('r')
    f = (Real >> Real)('f')
    
    T = Boole_to_Z3()
    print (T(p))
    print (T(p & q))
    print (T(p & q & ~r))
    print (T(x + y))
    print (T(x + y + 3))
    print (T(f(x + y) + f(f(x))))
    print (T((x + y) * (i + j)))
    print (T(((x + y) <= f(x)) & ~(y < z)))

    