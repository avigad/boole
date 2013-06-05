#############################################################################
#
# terms.py
#
# description: an info type describing how to build terms and types at the
# top level.
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
import elab
import unif

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
        root, args = root_app(expr)
        args_str = map(str, args)
        args_str = ", ".join(args_str)
        return "{0!s}({1!s})".format(root, args_str)

    
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
        ExprInfo.__init__(self, 'st_expr', {})


st_term = infobox(None)

st_typ = infobox(None)


@with_info(st_term)
def pair(expr1, expr2):
    """Turn a pair of simply typed arguments
    into a Pair.
    
    Arguments:
    - `args`: a list of expressions.
    """
    ty1 = typing.infer(expr1, ctxt=local_ctxt)[0]
    ty2 = typing.infer(expr2, ctxt=local_ctxt)[0]
    return Pair(expr1, expr2, typ_mul(ty1, ty2))


@with_info(st_term)
def tm_call(fun, *args):
    """Return the result of the application of
    fun to the arguments *args, using trivial
    conversion certificates.
    
    Arguments:
    - `fun`: an expression
    - `arg`: a list of expresstions
    """
    fun_typ, obl = typing.infer(fun, ctxt=local_ctxt)
    conv = [trivial()] * len(args)
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


#TODO: change this to a real equality?
@with_info(st_term)
def eq_tm(expr1, expr2):
    return Sub(expr1, expr2)


@with_info(st_typ)
def type_arrow(type1, type2):
    return pi(Const('_', type1), type2)


class StTerm(StExpr):
    """The information associated to terms
    """
    
    def __init__(self):
        StExpr.__init__(self)
        self.name = 'st_term'
        self.info['__call__'] = tm_call
        self.info['__add__'] = add_tm
        self.info['__mul__'] = mul_tm
        self.info['__rshift__'] = type_arrow
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
    return sig(Const('_', type1), type2)


@with_info(st_typ)
def le_typ(type1, type2):
    return Sub(type1, type2)


class StTyp(StExpr):
    """The information associated to types
    """
    
    def __init__(self):
        StExpr.__init__(self)
        self.name = 'st_typ'
        self.info['__call__'] = typ_call
        self.info['__mul__'] = typ_mul
        self.info['__rshift__'] = type_arrow
        self.info['__str__'] = str_typ
        self.info['__le__'] = le_typ

st_typ._info = StTyp()


@with_info(st_typ)
def mktype(name, implicit=None):
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

local_ctxt = Context("local_ctxt")


def deftype(name, implicit=None):
    """Define a type constant, and add it
    to local_ctxt.
    
    Arguments:
    - `name`:
    """
    if implicit is None:
        c = mktype(name)
    else:
        c = mktype(name, implicit=True)
    local_ctxt.add_const(c)
    print "{0!s} : {1!s} is assumed.\n".format(c, c.type)
    return c


def defconst(name, type, infix=None, tactic=None, implicit=None):
    """Define a constant, add it to
    local_ctxt and return it.
    
    Arguments:
    - `name`:
    - `type`:
    - `infix`:
    """
    c = const(name, type, infix=infix)
    
    #first try to solve the meta-vars in the type of c
    _, obl = elab.mvar_infer(c, ctxt=local_ctxt)
    obl.solve_with(unif.unify)
    #Now update the meta-variables of the type of c
    #fail if there are undefined meta-vars.
    c.type = unif.sub_mvar(type, undef=True)
    if implicit:
        c.type.info['implicit'] = True
    
    #Now type check the resulting term and try to solve the
    #TCCs
    _, obl = typing.infer(c, ctxt=local_ctxt)
    if tactic is None:
        obl.solve_with(goals.auto)
    else:
        obl.solve_with(tactic)
    local_ctxt.add_const(c)
    if obl.is_solved():
        print "{0!s} : {1!s} is assumed.\n".format(c, type)
    else:
        local_ctxt.add_to_field(obl.name, obl, 'goals')
        print "In the declaration:\n{0!s} : {1!s}".format(name, type)
        print "remaining type-checking constraints!"
        print obl
    return c


#TODO: clean this function!
#TODO: abstract over local_ctxt
def defexpr(name, value, type=None, tactic=None):
    """Define an expression with a given type and value.
    Checks that the type of value is correct, and adds the defining
    equation to the context.
    
    Arguments:
    - `name`: a string
    - `type`: an expression
    - `value`: an expression
    """
    if type is None:
        _, obl = elab.mvar_infer(value, ctxt=local_ctxt)
    else:
        _, obl = elab.mvar_infer(value, type=type, ctxt=local_ctxt)

    obl.solve_with(unif.unify)

    val = unif.sub_mvar(value, undef=True)

    if not (type is None):
        ty = unif.sub_mvar(type, undef=True)
    
    if type is None:
        ty, obl = typing.infer(val, ctxt=local_ctxt)
    else:
        ty, obl = typing.infer(val, type=ty, ctxt=local_ctxt)

    if tactic is None:
        obl.solve_with(goals.auto)
    else:
        obl.solve_with(tactic)

    c = const(name, ty)
    c.info['defined'] = True
    local_ctxt.add_const(c)

    eq_c = (c == val)
    def_name = "{0!s}_def".format(name)
    c_def = const(def_name, eq_c)
    local_ctxt.add_const(c_def)
    local_ctxt.add_to_field(name, val, 'defs')

    if obl.is_solved():
        print "{0!s} : {1!s} is defined.\n".format(c, ty)
    else:
        local_ctxt.add_to_field(obl.name, obl, 'goals')
        print "In the definition\n"
        " {0!s} = {1!s} : {2!s}".format(name, val, ty)
        print "remaining type-checking constraints!"
        print obl
    return c


def defhyp(name, prop):
    """Declare a constant of type bool, add it to the
    list of hypotheses.
    
    Arguments:
    - `name`: the name of the hypothesis
    - `prop`: the proposition
    """
    c = defconst(name, prop)
    typing.infer(c.type, type=Bool, ctxt=local_ctxt)
    local_ctxt.add_to_field(name, c.type, 'hyps')
    return c


def defsub(name, prop):
    """Declare a hypothesis of type A <= B
    
    Arguments:
    - `name`: the name of the hypothesis
    - `prop`: a proposition of the form A <= B
    """
    if prop.is_sub():
        c = defhyp(name, prop)
        local_ctxt.add_to_field(name, c.type, 'sub')
        return c
    else:
        raise Exception("Error in definition {0!s}:"\
                        "expected a proposition of the form A <= B"\
                        .format(name))


#TODO: give a definition as well.
def defclass(name, ty):
    """Define a type class with the given name and type
    
    Arguments:
    - `name`: a string
    - `ty`: an expression
    """
    c = defconst(name, ty)
    c.info['is_class'] = True
    local_ctxt.add_to_field(name, c.type, 'classes')
    return c


#TODO: give a definition as well.
#TODO: should an instance be a hypothesis?
def definstance(name, ty):
    """
    
    Arguments:
    - `name`: a string
    - `ty`: a type of the form ClassName(t1,...,tn)
    """
    c = defconst(name, ty)
    root, _ = root_app(ty)
    if root.info.is_class:
        local_ctxt.add_to_field(name, c.type, 'class_instances')
        local_ctxt.add_to_field(name, c.type, 'hyps')
        return c
    else:
        raise Exception("Error in definition of {0!s}:"\
                        "expected {1!s} to be a class name"\
                        .format(name, root))


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

conj = defconst('&', Bool >> (Bool >> Bool), infix=True)
disj = defconst('|', Bool >> (Bool >> Bool), infix=True)
neg = defconst('neg', Bool >> Bool)
#TODO: make Sub(p, q) print as p ==> q for terms of type bool
# impl = defconst('==>', Bool * Bool >> Bool, infix=True)

#This is equivalent to the constant returned by the
# true() function in expr.py, as constants are only compared
# by name. As a result, it is proven using the auto tactic
true = defconst('true', Bool)

false = defconst('false', Bool)


#Implicit type declarations
Type_ = expr.Type()
Type_.info.update(StTyp())
Type_.info['implicit'] = True


Bool_ = expr.Bool()
Bool_.info.update(StTyp())
Bool_.info['implicit'] = True
