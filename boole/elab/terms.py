#############################################################################
#
# simp_terms.py
#
# description: an info type describing how to build terms if they are simply
# typed.
#
#
# Authors:
# Cody Roux
#
#
#
##############################################################################

from boole.core.info import *
from boole.core.expr import *
from boole.core.context import *
import boole.core.typing as typing
import boole.core.goals as goals
import boole.core.expr as expr
import boole.core.conv as conv
import elab


def print_app(expr):
    """Takes an application and prints it in the following manner:
    if the application is of the form (..(f a1)... an), print
    f(a1,...,an)
    
    Arguments:
    - `expr`: an application
    """
    if expr.fun.is_app() and expr.fun.fun.info.infix:
        lhs = expr.fun.arg
        rhs = expr.arg
        fun = expr.fun.fun
        return  "({0!s} {1!s} {2!s})".format(lhs, fun, rhs)
    else:
        rem_tm = expr
        args = []
        while rem_tm.is_app():
            args.append(rem_tm.arg)
            rem_tm = rem_tm.fun
        #The arguments were collected in reverse order
        args.reverse()
        args_str = map(str, args)
        args_str = ", ".join(args_str)
        return "{0!s}({1!s})".format(rem_tm, args_str)

    
def print_pair(expr):
    """
    
    Arguments:
    - `expr`: a pair
    """
    return "pair({0!s}, {1!s})".format(expr.fst, expr.snd)


def print_fst(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "fst({0!s})".format(expr.expr)


def print_snd(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "snd({0!s})".format(expr.expr)


def print_box(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "Box({0!s})".format(expr)


def print_pi(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "({0!s})>>{1!s}".format(expr.dom, expr.body)

def print_sig(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "{0!s}*{1!s}".format(expr.dom, expr.body)

    
def print_sub(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "{0!s} <= {1!s}".format(expr.lhs, expr.rhs)

def print_eq(expr):
    return "{0!s} == {1!s}".format(expr.lhs, expr.rhs)

def print_bool(expr):
    return "Bool"

def print_type(expr):
    return "Type"

def str_typ(expr):
    if expr.is_app():
        return print_app(expr)
    elif expr.is_bound() and expr.binder.is_pi():
        return print_pi(expr)
    elif expr.is_bound() and expr.binder.is_sig():
        return print_sig(expr)
    elif expr.is_sub():
        return print_sub(expr)
    elif expr.is_bool():
        return print_bool(expr)
    elif expr.is_type():
        return print_type(expr)
    else:
        return expr.to_string()


def str_tm(expr):
    if expr.is_app():
        return print_app(expr)
    elif expr.is_pair():
        return print_pair(expr)
    elif expr.is_fst():
        return print_fst(expr)
    elif expr.is_snd():
        return print_snd(expr)
    elif expr.is_sub():
        return print_eq(expr)
    else:
        return expr.to_string()


class StExpr(ExprInfo):
    """The information for forming and printing
    simply typed terms.
    """
    
    def __init__(self):
        """
        """
        ExprInfo.__init__(self, {})


st_term = infobox(None)

st_typ = infobox(None)


def nullctxt():
    return Tele([], [])


def unit():
    return Const('unit', Type)


def dummy():
    return Const('_', unit())


def trivial():
    return Ev(nullctxt())


@with_info(st_term)
def pair(expr1, expr2):
    """Turn a pair of simply typed arguments
    into a Pair.
    
    Arguments:
    - `args`: a list of expressions.
    """
    ty1 = typing.infer(expr1)[0]
    ty2 = typing.infer(expr2)[0]
    return Pair(expr1, expr2, typ_mul(ty1, ty2))


@with_info(st_term)
def tm_call(fun, *args):
    """
    
    Arguments:
    - `fun`:
    - `arg`:
    """
    fun_typ = typing.infer(fun)[0]
    conv = [trivial()]*len(args)
    return elab.app_expr(fun, fun_typ, conv, args)
    


@with_info(st_term)
def add_tm(expr, arg):
    return plus(expr, arg)


@with_info(st_term)
def mul_tm(expr, arg):
    return mult(expr, arg)


#TODO: make this more clever
@with_info(st_term)
def get_pair(expr, index):
    """Get the field of an expression using python syntax
    
    Arguments:
    - `expr`: an expression
    - `index`: an integer equal to 0 or 1
    """
    if index == 0:
        return Fst(expr)
    elif index == 1:
        return Snd(expr)
    else:
        raise Exception("Index applied to {0!s} must be 0 or 1"\
                        .format(expr))


#TODO: change this to a real equality
@with_info(st_term)
def eq_tm(expr1, expr2):
    return Sub(expr1, expr2)
    

class StTerm(StExpr):
    """The information associated to terms
    """
    
    def __init__(self):
        StExpr.__init__(self)
        self.info['__call__'] = tm_call
        self.info['__add__'] = add_tm
        self.info['__mul__'] = mul_tm
        self.info['__getitem__'] = get_pair
        self.info['__eq__'] = eq_tm
        self.info['__str__'] = str_tm

st_term._info = StTerm()


@with_info(st_term)
def const(name, type, infix=False):
    return Const(name, type)


def typ_call(type, name):
    return defconst(name, type)


@with_info(st_typ)
def typ_mul(type1, type2):
    return sig(dummy(), type1, type2)


@with_info(st_typ)
def type_arrow(type1, type2):
    return pi(dummy(), type1, type2)


@with_info(st_typ)
def le_typ(type1, type2):
    return Sub(type1, type2)


class StTyp(StExpr):
    """The information associated to types
    """
    
    def __init__(self):
        StExpr.__init__(self)
        self.info['__call__'] = typ_call
        self.info['__mul__'] = typ_mul
        self.info['__rshift__'] = type_arrow
        self.info['__str__'] = str_typ
        self.info['__le__'] = le_typ

st_typ._info = StTyp()


@with_info(st_typ)
def mktype(name):
    """
    
    Arguments:
    - `name`:
    """

    return Const(name, expr.Type())


###############################################################################
#
# Create a context for basic simply typed operations
# Give operations allowing the definition of constants and types
#
###############################################################################

st_context = Context("st_context")

def deftype(name, tactic=None):
    """Define a type constant, and add it
    to st_context.
    
    Arguments:
    - `name`:
    """
    c = mktype(name)
    ty, obl = typing.infer(c)
    if tactic == None:
        obl.solve_with(goals.trivial)
    else:
        obl.solve_with(tactic)
    st_context.add_const(c)
    if obl.is_solved():
        print "{0!s} : {1!s} is assumed.\n".format(c, ty)
    else:
        st_context.add_to_field(obl.name, obl, 'unsolved_goals')
        print "In the declaration:\n{0!s} : {1!s}".format(name, type)
        print "remaining type-checking constraints!"
        print obl
    return c

def defconst(name, type, infix=False, tactic=None):
    """Define a constant, add it to
    st_context and return it.
    
    Arguments:
    - `name`:
    - `type`:
    - `infix`:
    """
    c = const(name, type, infix=infix)
    _, obl = typing.infer(c)
    if tactic == None:
        obl.solve_with(goals.trivial)
    else:
        obl.solve_with(tactic)
    st_context.add_const(c)
    if obl.is_solved():
        print "{0!s} : {1!s} is assumed.\n".format(c, type)
    else:
        st_context.add_to_field(obl.name, obl, 'unsolved_goals')
        print "In the declaration:\n{0!s} : {1!s}".format(name, type)
        print "remaining type-checking constraints!"
        print obl
    return c


#TODO: clean this function!
#TODO: abstract over st_context
def defexpr(name, value, type=None, tactic=None):
    """Define an expression with a given type and value.
    Checks that the type of value is correct, and adds the defining
    equation to the context.
    
    Arguments:
    - `name`: a string
    - `type`: an expression
    - `value`: an expression
    """
    if type != None:
        ty, obl = typing.infer(value, type=type)
    else:
        ty, obl = typing.infer(value)

    if tactic == None:
        obl.solve_with(goals.trivial)
    else:
        obl.solve_with(tactic)

    c = const(name, ty)
    c.info['defined'] = True
    st_context.add_const(c)

    eq_c = (c == value)
    def_name = "{0!s}_def".format(name)
    c_def = const(def_name, eq_c)
    st_context.add_to_field(def_name, c_def, 'defs')
    st_context.add_const(c_def)

    if obl.is_solved():
        print "{0!s} : {1!s} is defined.\n".format(c, ty)
    else:
        st_context.add_to_field(obl.name, obl, 'unsolved_goals')
        print "In the definition\n  {0!s} = {1!s} : {2!s}".format(name, value, ty)
        print "remaining type-checking constraints!"
        print obl
    return c


#TODO: create a defhyp function, then check the hyps when calling trivial

###############################################################################
#
# Declarations for the simply typed theory.
#
###############################################################################


real = deftype('real')
plus = defconst('+', real >> (real >> real), infix=True)
mult = defconst('*', real >> (real >> real), infix=True)
zero = defconst('0', real)
one = defconst('1', real)

#create a single instance of Bool() and Type().
Bool = expr.Bool()
Bool.info.update(StTyp())

Type = expr.Type()
Type.info.update(StTyp())

#TODO: add methods allowing infix input
conj = defconst('&', Bool >> (Bool >> Bool), infix=True)
disj = defconst('|', Bool >> (Bool >> Bool), infix=True)
neg = defconst('neg', Bool >> Bool, infix=True)
#TODO: make Sub(p, q) print as p ==> q for terms of type bool
# impl = defconst('==>', Bool * Bool >> Bool, infix=True)

#This is equivalent to the constant returned by the
# true() function in expr.py, as constants are only compared
# by name. As a result, it is proven using the trivial tactic
true = defconst('true', Bool)

false = defconst('false', Bool)


#Implicit type declarations
Type_ = expr.Type()
Type_.info.update(StTyp())
Type_.info['implicit'] = True


if __name__ == '__main__':



    z = real('z')

    X = Type_('X')
    X.info.update(StTyp())


    poly = defconst('poly', pi(X, Type_, X >> X))

    poly_z = poly(z)

    #WARNING: calling poly(z) twice will produce
    #distinct meta-variables.
    poly_t = elab.mvar_infer(poly_z)

    print poly_z, ':', poly_t[0]
    print
    print 'with goals:\n', poly_t[1]
    

    # print dummy()

    # nat = deftype('nat')
    
    # not_bin_op = nat >> nat >> nat

    # nat_sub_real = (nat <= real)('nat_sub_real')

    # #TODO: should we add the hypothesis or the constant?
    # st_context.add_to_field('nat_sub_real', nat_sub_real.type, 'hyps')

    # print not_bin_op

    # x = nat('x')
    # y = nat('y')
    # z = (real * real)('z')
    # w = real('w')
    # t = real('t')

    # abs_plus = defexpr('abs_plus', abst(t, real, t + w))

    # print abs_plus

    # typing.check(abs_plus(x), context=st_context)
    
    # typing.check(pair(x, y))

    # typing.check(x + y, \
    #              context=st_context)

    # typing.check(z[0] * z[1] == z[1] * z[0])

    # typing.check(abst(z, real * real, pair(x, x)))

    # typing.check(forall(z, real * real, (z[0] + z[1]) == (z[1] + z[0])))

    # fa = forall(z, real * real, (z[0] + z[1]) == (z[1] + z[0]))

    # plus_commut_stmt = defexpr('plus_commut_stmt', fa, type=Bool)
    
    # typing.check(st_context.decls['real'])
    # print

    # def definition_of(expr):
    #     """Return the definition of a defined constant.
        
    #     Arguments:
    #     - `expr`:
    #     """
    #     if expr.is_const():
    #         if expr.info.defined:
    #             print st_context.get_from_field(expr.name+"_def", 'defs')\
    #                   .type
    #             print
    #         else:
    #             print expr, " is not defined!"
    #             print
    #     else:
    #         print expr, " is not a constant!"
    #         print

    # two = defexpr('two', one+one, real)

    # definition_of(plus_commut_stmt)

    # definition_of(two)

    # plus_commut = defexpr('plus_commut', trivial(), fa)

    # p = pair(x, y)

    # proj_x_y_0 = defexpr('proj_x_y_0', trivial(), p[0] == x, tactic=goals.simpl)

    # boolop = Bool * Bool >> Bool

    # typeop = Type * Type >> Type

    # typing.check(boolop)
    # print
    # typing.check(typeop)
    # print
    # typing.check(conj(true, disj(true, false)))
    # print
    # print p[1]
    # print conv.par_beta(p[0])
    # print conv.par_beta(p[1])
