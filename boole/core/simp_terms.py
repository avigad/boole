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

from info import *
from expr import *
import typing


def print_app(expr):
    """Takes an application and prints it in readable format.
    
    Arguments:
    - `expr`:
    """
    try:
        if expr.fun.infix:
            if expr.arg.is_tuple() and len(expr.arg) == 2:
                lhs = expr.arg.exprs[0]
                rhs = expr.arg.exprs[1]
                return "{0!s} {1!s} {2!s}".format(lhs, expr.fun, rhs)
            else:
                return "{0!s}({1!s})".format(expr.fun, expr.arg)
        else:
            return "{0!s}({1!s})".format(expr.fun, expr.arg)
    except AttributeError:
        return "{0!s}({1!s})".format(expr.fun, expr.arg)


    
def print_tuple(expr):
    """
    
    Arguments:
    - `expr`:
    """
    tups = map(str, expr.exprs)
    tups = ", ".join(tups)
    return "({0!s})".format(tups)


def print_proj(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "({0!s})[{1!s}]".format(expr.expr, expr.index)


def print_box(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return str(expr)


def print_pi(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "({0!s})>>{1!s}".format(expr.dom, expr.expr)

def print_sig(expr):
    """
    
    Arguments:
    - `expr`:
    """
    types = map(str, expr.telescope.types)
    return "*".join(types)
    

def st_str(expr):
    if expr.is_app():
        return print_app(expr)
    elif expr.is_tuple():
        return print_tuple(expr)
    elif expr.is_proj():
        return print_proj(expr)
    elif expr.is_bound() and expr.binder.is_pi():
        return print_pi(expr)
    elif expr.is_sig():
        return print_sig(expr)
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
        self.info['__str__'] = st_str




st_term = infobox(None)

st_typ = infobox(None)


def nullctxt():
    return Tele([], [])


def unit():
    return sig()


def dummy():
    return Const('_', unit)


def trivial():
    return Ev(nullctxt())


@with_info(st_term)
def mk_tuple(args):
    """Turn a list of simply typed arguments
    into a tuple
    
    Arguments:
    - `args`: a list of expressions.
    """
    types = [typing.infer(a)[0] for a in args]
    return Tuple(args, type_mul_list(types))
    
    


@with_info(st_term)
def tm_call(fun, *args):
    """
    
    Arguments:
    - `fun`:
    - `arg`:
    """
    return App(trivial(), fun, mk_tuple(args))


@with_info(st_term)
def add_tm(expr, arg):
    return plus(expr, arg)


class StTerm(StExpr):
    """The information associated to terms
    """
    
    def __init__(self):
        StExpr.__init__(self)
        self.info['__call__'] = tm_call
        self.info['__add__'] = add_tm

st_term._info = StTerm()

@with_info(st_term)
def const(name, type, infix=False):
    return Const(name, type)


def typ_call(type, name):
    return const(name, type)



@with_info(st_typ)
def typ_mul(type1, type2):
    if type1.is_sig():
        vars = type1.telescope.vars + [dummy()]
        types = type1.telescope.types + [type2]
        return Sig(Tele(vars, types))
    else:
        return sig((dummy(), type1), (dummy(), type2))



@with_info(st_typ)
def type_mul_list(types):
    vars = [dummy()]*len(types)
    return Sig(Tele(vars, types))


@with_info(st_typ)
def type_arrow(type1, type2):
    return pi(dummy(), type1, type2)


class StTyp(StExpr):
    """The information associated to types
    """
    
    def __init__(self):
        StExpr.__init__(self)
        self.info['__call__'] = typ_call
        self.info['__mul__'] = typ_mul
        self.info['__rshift__'] = type_arrow


print 'redefining st_typ!'
st_typ._info = StTyp()


@with_info(st_typ)
def mktype(name):
    """
    
    Arguments:
    - `name`:
    """

    return Const(name, Type())

nat = mktype('nat')
prod = nat * nat
plus = const('+', (nat*nat) >> nat, infix=True)
    

if __name__ == '__main__':

    nat = mktype('nat')
    prod = nat * nat * nat

    print prod

    x = nat('x')
    y = nat('y')
    z = (nat*nat)('z')
    typing.check(x)
    typing .check(z)
    
    typing.check(plus)
    typing.check(mk_tuple([x,y]))


    typing.check(x + y)
    
