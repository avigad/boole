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
from context import *
import boole.core.typing as typing
import boole.core.goals as goals


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
    
def print_eq(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return "{0!s} == {1!s}".format(expr.lhs, expr.rhs)



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
    elif expr.is_eq():
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
        self.info['__str__'] = st_str




st_term = infobox(None)

st_typ = infobox(None)


def nullctxt():
    return Tele([], [])


def unit():
    return sig()


def dummy():
    return Const('_', unit())


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


@with_info(st_term)
def mul_tm(expr, arg):
    return mult(expr, arg)


@with_info(st_term)
def get_tup(expr, index):
    """Get the field of an expression using python syntax
    
    Arguments:
    - `expr`:
    - `index`:
    """
    return Proj(index, expr)


@with_info(st_term)
def eq_tm(expr1, expr2):
    return Eq(expr1, expr2)
    

class StTerm(StExpr):
    """The information associated to terms
    """
    
    def __init__(self):
        StExpr.__init__(self)
        self.info['__call__'] = tm_call
        self.info['__add__'] = add_tm
        self.info['__mul__'] = mul_tm
        self.info['__getitem__'] = get_tup
        self.info['__eq__'] = eq_tm

st_term._info = StTerm()


@with_info(st_term)
def const(name, type, infix=False):
    return Const(name, type)


def typ_call(type, name):
    return defconst(name, type)



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
    vars = ['_'] * len(types)
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


st_typ._info = StTyp()


@with_info(st_typ)
def mktype(name):
    """
    
    Arguments:
    - `name`:
    """

    return Const(name, Type())


###############################################################################
#
# Create a context for basic simply typed operations
# Give operations allowing the definition of constants and types
#
###############################################################################

st_context = Context("st_context")

def deftype(name):
    """Define a type constant, and add it
    to st_context.
    
    Arguments:
    - `name`:
    """
    c = mktype(name)
    st_context.add_const(c)
    return c

def defconst(name, type, infix=False):
    """Define a constant, add it to
    st_context and return it.
    
    Arguments:
    - `name`:
    - `type`:
    - `infix`:
    """
    c = const(name, type, infix=infix)
    _, obl = typing.infer(c)
    obl.solve_with('trivial')
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
def defexpr(name, value, type=None):
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
    obl.solve_with('trivial')

    c = const(name, type)
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
        print "In the definition\n  {0!s} = {1!s}".format(name, value)
        print "remaining type-checking constraints!"
        print obl
    return c

###############################################################################
#
# Declarations for the simply typed theory.
#
###############################################################################


nat = deftype('nat')
plus = defconst('+', (nat * nat) >> nat, infix=True)
mult = defconst('*', (nat * nat) >> nat, infix=True)
zero = defconst('0', nat)
one = defconst('1', nat)



if __name__ == '__main__':


    print dummy()

    nat = mktype('nat')
    prod = nat * nat * nat

    print prod

    x = nat('x')
    y = nat('y')
    z = (nat * nat)('z')

    # typing.check(mk_tuple([x, y]))
    # typing.check(x + y)

    # typing.check(z[0] * z[1] == z[1] * z[0])

    # typing.check(abst(z, nat * nat, mk_tuple([x, x])))

    # typing.check(forall(z, nat * nat, (z[0] + z[1]) == (z[1] + z[0])))

    fa = forall(z, nat * nat, (z[0] + z[1]) == (z[1] + z[0]))

    plus_commut_stmt = defexpr('plus_commut_stmt', fa, Bool())

    typing.check(st_context.nat)


    def definition_of(expr):
        """Return the definition of a defined constant.
        
        Arguments:
        - `expr`:
        """
        if expr.is_const():
            if expr.defined:
                print st_context.get_from_field(expr.name+"_def", 'defs')\
                      .type
            else:
                print expr, " is not defined!"
        else:
            print expr, " is not a constant!"

    two = defexpr('two', one+one, nat)

    definition_of(plus_commut_stmt)

    definition_of(two)

    plus_commut = defexpr('plus_commut', trivial(), fa)
