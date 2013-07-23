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
from boole.core.context import *
from boole.core.expr import Const, Sub, Pair, Fst, Snd, Box, root_app, root_clause
import boole.core.expr as e
import boole.core.typing as typing
import elab
from elab import app_expr, mvar_infer, open_expr, sub_mvar, root_pi
import boole.core.tactics as tac
import boole.core.goals as goals
import unif as u

###############################################################################
#
# various utility functions on expressions
#
###############################################################################


def ii(n):
    return Const(str(n), Int, is_const=True)


def rr(n):
    return Const(str(n), Real, is_const=True)


def to_expr(expr):
    if isinstance(expr, int):
        return ii(expr)
    elif isinstance(expr, float):
        return rr(expr)
    else:
        return expr


def root_app_implicit(expr):
    """If a term is of the form
    (..(f a0).. an), return the pair
    (f, [ai,..., ak]) where the ai...ak are the
    non-implicit arguments of f.
    
    Arguments:
    - `expr`: an expression
    """
    r, args = root_app(expr)
    
    ty, _ = mvar_infer(r, ctxt=local_ctxt)

    non_implicit = []
    i = 0
    while ty.is_bound() and ty.binder.is_pi() and i < len(args):
        if not ty.info.implicit:
            non_implicit.append(args[i])
        i += 1
        ty = ty.body

    return (r, non_implicit)


def print_app(expr):
    """Takes an application and prints it in the following manner:
    if the application is of the form (..(f a0)... an), print
    f(a0,...,an), or (a0 f a1) if f is infix.
    
    Arguments:
    - `expr`: an expression
    """
    root, args = root_app_implicit(expr)
    if root.info.infix and len(args) == 2:
        return "({0!s} {1!s} {2!s})".format(args[0], root, args[1])
    else:
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
    return "cast({0!s}, {1!s})".format(expr.expr, expr.type)


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


def print_bool():
    return "Bool"


def print_type():
    return "Type"


def print_ev(expr):
    if len(expr.tele) == 0:
        return "triv()"
    else:
        return expr.to_string()


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
        return print_bool()
    elif expr.is_type():
        return print_type()
    else:
        return expr.to_string()


def print_bound(expr):
    var = expr.binder.var
    open_self = open_expr(var, expr.dom, expr.body)
    return "{0!s}({1!s},{2!s})".format(\
        expr.binder.name, expr.binder.var, open_self)


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
    elif expr.is_bound():
        return print_bound(expr)
    elif expr.is_ev():
        return print_ev(expr)
    elif expr.is_box():
        return print_box(expr)
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
    - `expr1`: an expression or int or float
    - `expr1`: an expression or int or float
    """
    e1 = to_expr(expr1)
    e2 = to_expr(expr2)
    ty1, _ = typing.infer(e1, ctxt=local_ctxt)
    ty2, _ = typing.infer(e2, ctxt=local_ctxt)
    return Pair(e1, e2, typ_mul(ty1, ty2))


@with_info(st_term)
def tm_call(fun, *args):
    """Return the result of the application of
    fun to the arguments *args, using trivial
    conversion certificates.
    
    Arguments:
    - `fun`: an expression
    - `arg`: a list of expresstions
    """
    fun_typ, _ = typing.infer(fun, ctxt=local_ctxt)
    conv = [triv()] * len(args)
    cast_args = map(to_expr, args)
    return app_expr(fun, fun_typ, conv, cast_args)
    

@with_info(st_term)
def add_tm(expr, arg):
    return add(expr, arg)


@with_info(st_term)
def mul_tm(expr, arg):
    return mul(expr, arg)


@with_info(st_term)
def r_add_tm(expr, arg):
    return add(arg, expr)


@with_info(st_term)
def r_mul_tm(expr, arg):
    return mul(arg, expr)


@with_info(st_term)
def lt_tm(expr, arg):
    return lt(expr, arg)


@with_info(st_term)
def gt_tm(expr, arg):
    return lt(arg, expr)


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


@with_info(st_term)
def eq_tm(expr1, expr2):
    return eq(expr1, expr2)


@with_info(st_term)
def impl_tm(expr1, expr2):
    return impl(expr1, expr2)


@with_info(st_term)
def and_tm(expr1, expr2):
    return conj(expr1, expr2)


@with_info(st_term)
def or_tm(expr1, expr2):
    return disj(expr1, expr2)


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
        self.info['__radd__'] = r_add_tm
        self.info['__rmul__'] = r_mul_tm
        self.info['__rshift__'] = type_arrow
        #TODO: find a better notation for implication
        self.info['__ge__'] = impl_tm
        self.info['__getitem__'] = get_pair
        self.info['__eq__'] = eq_tm
        self.info['__str__'] = str_tm
        self.info['__lt__'] = lt_tm
        self.info['__gt__'] = gt_tm
        self.info['__and__'] = and_tm
        self.info['__or__'] = or_tm

st_term._info = StTerm


@with_info(st_term)
def const(name, type, infix=None):
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

st_typ._info = StTyp


@with_info(st_typ)
def mktype(name):
    """
    
    Arguments:
    - `name`:
    """
    return Const(name, e.Type())

###############################################################################
#
# Alias the constructors so that they carry the appropriate info.
#
###############################################################################


@with_info(st_term)
def pi_base(var, codom, **kwargs):
    return elab.pi(var, codom, **kwargs)


def pi(var, codom, **kwargs):
    if isinstance(var, list):
        var.reverse()
        tm = codom
        for v in var:
            tm = pi_base(v, tm, **kwargs)
        return tm
    else:
        return pi_base(var, codom, **kwargs)


@with_info(st_term)
def abst_base(var, body):
    return elab.abst(var, body)


def abst(var, body):
    if isinstance(var, list):
        var.reverse()
        tm = body
        for v in var:
            tm = abst_base(v, tm)
        return tm
    else:
        return abst_base(var, body)


@with_info(st_term)
def forall_base(var, prop):
    return elab.forall(var, prop)


def forall(var, prop):
    if isinstance(var, list):
        var.reverse()
        tm = prop
        for v in var:
            tm = forall_base(v, tm)
        return tm
    else:
        return forall_base(var, prop)


@with_info(st_term)
def exists_base(var, prop):
    return elab.exists(var, prop)


def exists(var, prop):
    if isinstance(var, list):
        var.reverse()
        tm = prop
        for v in var:
            tm = exists_base(v, tm)
        return tm
    else:
        return exists_base(var, prop)


@with_info(st_term)
def sig_base(var, codom):
    return elab.sig(var, codom)


def sig(var, codom):
    if isinstance(var, list):
        var.reverse()
        tm = codom
        for v in var:
            tm = sig_base(v, tm)
        return tm
    else:
        return sig_base(var, codom)


@with_info(st_term)
def true():
    return elab.true()


@with_info(st_term)
def false():
    return elab.false()


@with_info(st_term)
def nullctxt():
    return elab.nullctxt()


@with_info(st_term)
def triv():
    return elab.trivial


@with_info(st_term)
def cast(expr, ty):
    """cast an expression to ty
    
    Arguments:
    - `expr`: an expression
    - `ty`: a type equal to the type of expr
    """
    return Box(triv(), expr, ty)


###############################################################################
#
# Create a context for basic simply typed operations
# Give operations allowing the definition of constants and types
#
###############################################################################

local_ctxt = Context("local_ctxt")

verbose = False

def deftype(name):
    """Define a type constant, and add it
    to local_ctxt.
    
    Arguments:
    - `name`:
    """
    c = mktype(name)
    local_ctxt.add_const(c)
    if verbose:
        print "{0!s} : {1!s} is assumed.\n".format(c, c.type)
    return c


elab_tac = tac.par(u.unify) >> tac.trytac(u.instances)
type_tac = tac.auto >> tac.trytac(u.instances)


def defconst(name, type, infix=None, tactic=None):
    """Define a constant, add it to
    local_ctxt and return it.
    
    Arguments:
    - `name`:
    - `type`:
    - `infix`:
    """
    c = const(name, type, infix=infix)
    
    #first try to solve the meta-vars in the type of c
    _, obl = mvar_infer(c, ctxt=local_ctxt)

    u.mvar_stack.clear()
    u.mvar_stack.new()
    obl.solve_with(elab_tac)

    #Now update the meta-variables of the type of c
    #fail if there are undefined meta-vars.
    c.type = sub_mvar(type, undef=True)

    #Now type check the resulting term and try to solve the
    #TCCs
    _, obl = typing.infer(c, ctxt=local_ctxt)

    if tactic is None:
        obl.solve_with(type_tac)
    else:
        obl.solve_with(tactic)

    c.info['checked'] = True
    local_ctxt.add_const(c)
    if obl.is_solved():
        if verbose:
            print "{0!s} : {1!s} is assumed.\n".format(c, c.type)
    else:
        local_ctxt.add_to_field(obl.name, obl, 'goals')
        print "In the declaration:\n{0!s} : {1!s}".format(name, c.type)
        print "remaining type-checking constraints!"
        print obl
    return c


def equals(e1, e2):
    return conj(Sub(e1, e2), Sub(e2, e1))


#TODO: clean this function!
#TODO: abstract over local_ctxt
def defexpr(name, value, type=None, infix=None, tactic=None):
    """Define an expression with a given type and value.
    Checks that the type of value is correct, and adds the defining
    equation to the context.
    
    Arguments:
    - `name`: a string
    - `type`: an expression
    - `value`: an expression
    """
    _, obl = mvar_infer(value, ctxt=local_ctxt)

    u.mvar_stack.clear()
    u.mvar_stack.new()
    obl.solve_with(elab_tac)

    val = sub_mvar(value, undef=True)

    if not (type is None):
        _, obl = mvar_infer(type, ctxt=local_ctxt)

        u.mvar_stack.clear()
        u.mvar_stack.new()
        obl.solve_with(elab_tac)

        ty = sub_mvar(type, undef=True)

    if type is None:
        ty, obl = typing.infer(val, ctxt=local_ctxt)
    else:
        ty, obl = typing.infer(val, type=ty, ctxt=local_ctxt)

    if tactic is None:
        obl.solve_with(type_tac)
    else:
        obl.solve_with(tactic)

    c = const(name, ty, infix=infix)
    c.info['defined'] = True
    c.info['checked'] = True
    local_ctxt.add_const(c)

    eq_c = equals(c, val)
    def_name = "{0!s}_def".format(name)
    c_def = const(def_name, eq_c)
    local_ctxt.add_const(c_def)
    local_ctxt.add_to_field(name, val, 'defs')

    if obl.is_solved():
        if verbose:
            print "{0!s} : {1!s} := {2!s} is defined.\n".format(c, ty, val)
    else:
        local_ctxt.add_to_field(obl.name, obl, 'goals')
        print "In the definition\n"\
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
    typing.infer(c.type, type=e.Bool(), ctxt=local_ctxt)
    local_ctxt.add_to_field(name, c.type, 'hyps')
    return c


def defthm(name, prop, tactic=None):
    """Declare a theorem and call a tactic to attempt to solve it.
    add it as a hypothesis regardless.
    
    """
    if tactic:
        c = defexpr(name, triv(), prop, tactic=tactic)
    else:
        c = defexpr(name, triv(), prop)
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


def defclass(name, ty, defn):
    """Define a type class with the given name and type
    
    Arguments:
    - `name`: a string
    - `ty`: an expression
    - `def`: the definition of the class
    """
    c = defexpr(name, defn, type=ty)
    c.info['is_class'] = True
    local_ctxt.add_to_field(name, c.type, 'classes')
    c_def = local_ctxt.defs[name]
    local_ctxt.add_to_field(name, c_def, 'class_def')
    return c


def definstance(name, ty, value):
    """
    
    Arguments:
    - `name`: a string
    - `ty`: a type of the form ClassName(t1,...,tn)
    """
    root, _ = root_app(root_clause(ty))
    if root.info.is_class:
        class_name = root.name
        class_tac = tac.par(tac.unfold(class_name)) >> tac.auto
        c = defexpr(name, value, type=ty, tactic=class_tac)
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
#create a single instance of Bool() and Type().
Bool = e.Bool()
Bool.info.update(StTyp())

Type = e.Type()
Type.info.update(StTyp())

Real = deftype('Real')
add_real = defconst('add_real', Real >> (Real >> Real))
mul_real = defconst('mul_real', Real >> (Real >> Real))
lt_real = defconst('lt_real', Real >> (Real >> Bool))

Int = deftype('Int')
int_sub_real = defsub('int_sub_real', Int <= Real)
add_int = defconst('add_int', Int >> (Int >> Int))
mul_int = defconst('mul_int', Int >> (Int >> Int))
lt_int = defconst('lt_int', Int >> (Int >> Bool))


conj = defconst('&', Bool >> (Bool >> Bool), infix=True)
disj = defconst('|', Bool >> (Bool >> Bool), infix=True)
neg = defconst('neg', Bool >> Bool)

p = Bool('p')
q = Bool('q')
impl = defexpr('>=', abst(p, abst(q, Sub(p, q))), \
               Bool >> (Bool >> Bool), infix=True)

#This is equivalent to the constant given as type to terms
# of the form Ev(tele), as constants are only compared
# by name. As a result, it is proven using the auto tactic
true = defconst('true', Bool)

false = defconst('false', Bool)

###############################################################################
#
# Equality and class instances for addition and multiplication
#
###############################################################################


X = deftype('X')

x = X('x')
y = X('y')

eq = defexpr('==', abst([X, x, y], conj(Sub(x, y), Sub(y, x))), \
             pi(X, X >> (X >> Bool), impl=True), infix=True)

op = defconst('op', X >> (X >> X))

Mul = defclass('Mul', pi([X, op], Bool), \
               abst([X, op], true))

mul_ev = Const('mul_ev', Mul(X, op))

mul = defexpr('*', abst([X, op, mul_ev], op), \
              pi([X, op, mul_ev], X >> (X >> X), impl=True), \
              infix=True)

Add = defclass('Add', pi([X, op], Bool), \
               abst([X, op], true))

add_ev = Const('add_ev', Add(X, op))

add = defexpr('+', abst([X, op, add_ev], op), \
              pi([X, op, add_ev], X >> (X >> X), impl=True), \
              infix=True)

pred = defconst('pred', X >> (X >> Bool))

Lt = defclass('Lt', pi([X, pred], Bool), \
              abst([X, pred], true))

lt_ev = Const('lt_ev', Lt(X, pred))

lt = defexpr('<', abst([X, pred, lt_ev], pred), \
             pi([X, pred, lt_ev], X >> (X >> Bool), impl=True), \
             infix=True)


definstance('Mul_real', Mul(Real, mul_real), triv())
definstance('Mul_int', Mul(Int, mul_int), triv())

definstance('Add_real', Add(Real, add_real), triv())
definstance('Add_int', Add(Int, add_int), triv())

definstance('Lt_real', Lt(Real, lt_real), triv())
definstance('Lt_int', Lt(Int, lt_int), triv())

verbose = True
