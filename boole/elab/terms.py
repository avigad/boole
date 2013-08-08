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
# Jeremy Avigad
#
#
# TODO: rename @with_info_new to @with_info, delete call commented lines
#  (and also in info.py)
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
    while ty.is_pi() and i < len(args):
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


def typ_str(expr):
    if expr.is_app():
        return print_app(expr)
    elif expr.is_pi():
        return print_pi(expr)
    elif expr.is_sig():
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


def tm_str(expr):
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


#class StExpr(ExprInfo):
#    """The information for forming and printing
#    simply typed terms.
#    """
#    
#    def __init__(self):
#        """
#        """
#        ExprInfo.__init__(self, 'st_expr', {})
#
#
#st_term = infobox(None)
#
#st_typ = infobox(None)

st_term = ExprInfo('term_info', {})
st_typ = ExprInfo('type_info', {})

def with_info_new(info):
    """Returns the function which calls a function on
    arguments, and update the info field of the result
    with the values in info.
    
    Note: because the function returns a closure, info
    is hardcoded in. But the *values* stored in info can 
    be changed.

    """
    def appl(f):
        def call_f(*args, **kwargs):
            e = f(*args, **kwargs)
            e.info.update(info)
            e.info.name = info.name
            for k in kwargs:
                e.info[k] = kwargs[k]
            return e
        return call_f
    return appl


@with_info_new(st_term)
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


@with_info_new(st_term)
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


# TODO: these can all be inlined in the assignment to the st_info structure
    
# @with_info_new(st_term)
def tm_eq(expr1, expr2):
    return eq(expr1, expr2)

# no decorator here. Or: make neq a primitive?
def tm_ne(expr1, expr2):
    return tm_invert(tm_eq(expr1, expr2))

# @with_info_new(st_term)
def tm_add(expr, arg):
    return add(expr, arg)

# @with_info_new(st_term)
def tm_radd(expr, arg):
    return add(arg, expr)

# @with_info_new(st_term)
def tm_mul(expr, arg):
    return mul(expr, arg)

# @with_info_new(st_term)
def tm_rmul(expr, arg):
    return mul(arg, expr)

# note: 'sub' is used for the subtype relation
# @with_info_new(st_term)
def tm_sub(expr, arg):
    return minus(expr, arg)

# @with_info_new(st_term)
def tm_rsub(expr, arg):
    return minus(arg, expr)

# @with_info_new(st_term)
def tm_div(expr, arg):
    return div(expr, arg)

# @with_info_new(st_term)
def tm_rdiv(expr, arg):
    return div(arg, expr)

# @with_info_new(st_term)
def tm_mod(expr, arg):
    return mod(expr, arg)

# @with_info_new(st_term)
def tm_rmod(expr, arg):
    return mod(arg, expr)

# @with_info_new(st_term)
def tm_pow(expr, arg):
    return power(expr, arg)

# @with_info_new(st_term)
def tm_rpow(expr, arg):
    return power(arg, expr)

# note: 'neg' is used for boolean negation
# @with_info_new(st_term)
def tm_neg(expr):
    return uminus(expr)

# @with_info_new(st_term)
def tm_abs(expr):
    return mod(expr)

# @with_info_new(st_term)
def tm_le(expr, arg):
    return le(expr, arg)

# @with_info_new(st_term)
def tm_lt(expr, arg):
    return lt(expr, arg)

# TODO: make ge separate?
# @with_info_new(st_term)
def tm_ge(expr, arg):
    return le(arg, expr)

# TODO: make gt separate?
# @with_info_new(st_term)
def tm_gt(expr, arg):
    return lt(arg, expr)

# @with_info_new(st_term)
def tm_and(expr1, expr2):
    return conj(expr1, expr2)

# @with_info_new(st_term)
def tm_rand(expr1, expr2):
    return conj(expr2, expr1)

# @with_info_new(st_term)
def tm_or(expr1, expr2):
    return disj(expr1, expr2)

# @with_info_new(st_term)
def tm_ror(expr1, expr2):
    return disj(expr2, expr1)

# @with_info_new(st_term)
def tm_invert(expr):
    return neg(expr)


# without the decorator, would have term info
@with_info_new(st_typ)
def type_arrow(type1, type2):
    return pi(Const('_', type1), type2)

#TODO: make this more clever
@with_info_new(st_term)
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


#
#class StTerm(StExpr):
#    """The information associated to terms
#    """
#    
#    def __init__(self):
#        StExpr.__init__(self)
#        self.name = 'st_term'
#        self.info['__str__'] = tm_str
#        self.info['__call__'] = tm_call
#        self.info['__getitem__'] = get_pair
#        self.info['__eq__'] = tm_eq
#        self.info['__ne__'] = tm_ne
#        self.info['__add__'] = tm_add
#        self.info['__radd__'] = tm_radd
#        self.info['__mul__'] = tm_mul
#        self.info['__rmul__'] = tm_rmul
#        self.info['__sub__'] = tm_sub
#        self.info['__rsub__'] = tm_rsub
#        self.info['__div__'] = tm_div
#        self.info['__rdiv__'] = tm_div
#        self.info['__mod__'] = tm_mod
#        self.info['__rmod__'] = tm_rmod
#        self.info['__pow__'] = tm_pow
#        self.info['__rpow__'] = tm_rpow
#        self.info['__rshift__'] = type_arrow
#        self.info['__le__'] = tm_le
#        self.info['__lt__'] = tm_lt
#        self.info['__ge__'] = tm_ge
#        self.info['__gt__'] = tm_gt       
#        self.info['__and__'] = tm_and
#        self.info['__rand__'] = tm_rand
#        self.info['__or__'] = tm_or
#        self.info['__ror__'] = tm_ror
#        self.info['__invert__'] = tm_invert
#
#st_term._info = StTerm


st_term['__str__'] = tm_str
st_term['__call__'] = tm_call
st_term['__getitem__'] = get_pair
st_term['__eq__'] = tm_eq
st_term['__ne__'] = tm_ne
st_term['__add__'] = tm_add
st_term['__radd__'] = tm_radd
st_term['__mul__'] = tm_mul
st_term['__rmul__'] = tm_rmul
st_term['__sub__'] = tm_sub
st_term['__rsub__'] = tm_rsub
st_term['__div__'] = tm_div
st_term['__rdiv__'] = tm_div
st_term['__mod__'] = tm_mod
st_term['__rmod__'] = tm_rmod
st_term['__pow__'] = tm_pow
st_term['__rpow__'] = tm_rpow
st_term['__rshift__'] = type_arrow
st_term['__le__'] = tm_le
st_term['__lt__'] = tm_lt
st_term['__ge__'] = tm_ge
st_term['__gt__'] = tm_gt       
st_term['__and__'] = tm_and
st_term['__rand__'] = tm_rand
st_term['__or__'] = tm_or
st_term['__ror__'] = tm_ror
st_term['__invert__'] = tm_invert


@with_info_new(st_term)
def const(name, type, infix=None):
    return Const(name, type)


def typ_call(type, name):
    return defconst(name, type)


@with_info_new(st_typ)
def typ_mul(type1, type2):
    return sig(Const('_', type1), type2)


@with_info_new(st_typ)
def typ_le(type1, type2):
    return Sub(type1, type2)


#class StTyp(StExpr):
#    """The information associated to types
#    """
#    
#    def __init__(self):
#        StExpr.__init__(self)
#        self.name = 'st_typ'
#        self.info['__call__'] = typ_call
#        self.info['__mul__'] = typ_mul
#        self.info['__rshift__'] = type_arrow
#        self.info['__str__'] = typ_str
#        self.info['__le__'] = typ_le
#
#st_typ._info = StTyp


st_typ['__call__'] = typ_call
st_typ['__mul__'] = typ_mul
st_typ['__rshift__'] = type_arrow
st_typ['__str__'] = typ_str
st_typ['__le__'] = typ_le


@with_info_new(st_typ)
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


#TODO: use built-in function?
def fold_over(base_op, var, tm, **kwargs):
    """
    Apply a base operation to a list of
    objects
    """
    if isinstance(var, list):
        var.reverse()
        res = tm
        for v in var:
            res = base_op(v, res, **kwargs)
        var.reverse()
        return res
    else:
        return base_op(var, tm, **kwargs)


@with_info_new(st_term)
def pi_base(var, codom, **kwargs):
    return elab.pi(var, codom, **kwargs)


def pi(var, codom, **kwargs):
    return fold_over(pi_base, var, codom, **kwargs)


@with_info_new(st_term)
def abst_base(var, body):
    return elab.abst(var, body)


def abst(var, body):
    return fold_over(abst_base, var, body)


@with_info_new(st_term)
def forall_base(var, prop):
    return elab.forall(var, prop)


def forall(var, prop):
    return fold_over(forall_base, var, prop)


@with_info_new(st_term)
def exists_base(var, prop):
    return elab.exists(var, prop)


def exists(var, prop):
    return fold_over(exists_base, var, prop)


@with_info_new(st_term)
def sig_base(var, codom):
    return elab.sig(var, codom)


def sig(var, codom):
    return fold_over(sig_base, var, codom)


@with_info_new(st_term)
def true():
    return elab.true()


@with_info_new(st_term)
def false():
    return elab.false()


@with_info_new(st_term)
def nullctxt():
    return elab.nullctxt()


@with_info_new(st_term)
def triv():
    return elab.trivial


@with_info_new(st_term)
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

elab_tac = tac.par(u.unify) >> tac.trytac(u.instances)
type_tac = tac.auto >> tac.trytac(u.instances)


# TODO: elab can be factored out of defexpr below (I think -- JA)
def elaborate(expr, type, elabtac, tactic):
    """Elaborate an expression and (optionally) its type.
    Returns the elaborated expression and its type, and any
    remaining obligations.
    It also marks the expression and its type as elaborated.
    
    Arguments:
    - `expr`: the expression to be elaborated
    - `type`: it's putative type
    - `elabtac`: a tactic to use in the elaboration
    - `tactic`: a tactic to use in the type-checking
    """
    if expr.info.elaborated and type is None:
        ty, obl = typing.infer(expr, ctxt=local_ctxt)
        if tactic is None:
            obl.solve_with(type_tac)
        else:
            obl.solve_with(tactic)
        return (expr, ty, obl)

    _, obl = mvar_infer(expr, ctxt=local_ctxt)

    u.mvar_stack.clear()
    u.mvar_stack.new()

    if elabtac is None:
        obl.solve_with(elab_tac)
    else:
        obl.solve_with(elabtac)

    val = sub_mvar(expr, undef=True)

    if not (type is None):
        _, obl = mvar_infer(type, ctxt=local_ctxt)

        u.mvar_stack.clear()
        u.mvar_stack.new()
        
        if elabtac is None:
            obl.solve_with(elab_tac)
        else:
            obl.solve_with(elabtac)

        ty = sub_mvar(type, undef=True)

    if type is None:
        ty, obl = typing.infer(val, ctxt=local_ctxt)
    else:
        ty, obl = typing.infer(val, type=ty, ctxt=local_ctxt)

    if tactic is None:
        obl.solve_with(type_tac)
    else:
        obl.solve_with(tactic)

    val.info['elaborated'] = True

    return (val, ty, obl)


def check(expr, type=None, tactic=None):
    """Elaborates the expression if necessary, and shows the type. Returns
    the elaborated expression
    
    Arguments:
    - `expr`: the expression to be checked
    - `type`: it's putative type
    - `tactic`: a tactic to use in the elaboration
    """

    val, ty, obl = elaborate(expr, type, None, tactic)
    if obl.is_solved():
        if verbose:
            print "{0!s} : {1!s}.\n".format(val, ty)
    else:
        local_ctxt.add_to_field(obl.name, obl, 'goals')
        print "In checking the expression\n"\
        "{0!s} : {1!s}".format(val, ty)
        print "remaining type-checking constraints!"
        print obl
    return val

# TODO: clean these functions!
# TODO: abstract over local_ctxt


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


def defconst(name, type, infix=None, tactic=None):
    """Define a constant, add it to
    local_ctxt and return it.
    
    Arguments:
    - `name`: the name of the constant
    - `type`: the type of the constant
    - `infix`: if the constant being defined is a function,
    infix specifies that it needs to be printed in infix style
    - `tactic`: specifies an optional tactic to solve the proof
    obligations
    """
    c = const(name, type, infix=infix)

    c, _, obl = elaborate(c, None, None, tactic)

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


def defexpr(name, value, type=None, infix=None, tactic=None):
    """Define an expression with a given type and value.
    Checks that the type of value is correct, and adds the defining
    equation to the context.
    
    Arguments:
    - `name`: a string
    - `type`: an expression
    - `value`: an expression
    """
    # _, obl = mvar_infer(value, ctxt=local_ctxt)

    # u.mvar_stack.clear()
    # u.mvar_stack.new()
    # obl.solve_with(elab_tac)

    # val = sub_mvar(value, undef=True)

    # if not (type is None):
    #     _, obl = mvar_infer(type, ctxt=local_ctxt)

    #     u.mvar_stack.clear()
    #     u.mvar_stack.new()
    #     obl.solve_with(elab_tac)

    #     ty = sub_mvar(type, undef=True)

    # if type is None:
    #     ty, obl = typing.infer(val, ctxt=local_ctxt)
    # else:
    #     ty, obl = typing.infer(val, type=ty, ctxt=local_ctxt)

    # if tactic is None:
    #     obl.solve_with(type_tac)
    # else:
    #     obl.solve_with(tactic)


    val, ty, obl = elaborate(value, type, None, tactic)

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


def defclass(name, params, defn):
    """Define a type class with the given name and type
    
    Arguments:
    - `name`: a string
    - `params`: a list of parameters
    - `def`: the definition of the class, which may depend on the parameters
    """
    class_ty = pi(params, Bool)
    class_def = abst(params, defn)
    
    c = defexpr(name, class_def, type=class_ty)
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
Bool.info.update(st_typ)
#Bool.info.update(StTyp())

Type = e.Type()
Type.info.update(st_typ)
#Type.info.update(StTyp())

# boolean connectives

conj = defconst('&', Bool >> (Bool >> Bool), infix=True)
disj = defconst('|', Bool >> (Bool >> Bool), infix=True)
neg = defconst('neg', Bool >> Bool)

p = Bool('p')
q = Bool('q')
implies = defexpr('implies', abst(p, abst(q, Sub(p, q))), \
               Bool >> (Bool >> Bool))

#This is equivalent to the constant given as type to terms
# of the form Ev(tele), as constants are only compared
# by name. As a result, it is proven using the auto tactic
true = defconst('true', Bool)

false = defconst('false', Bool)

# reals

Real = deftype('Real')

# binary operations on the reals

add_real = defconst('add_real', Real >> (Real >> Real))
mul_real = defconst('mul_real', Real >> (Real >> Real))
minus_real = defconst('minus_real', Real >> (Real >> Real))
divide_real = defconst('divide_real', Real >> (Real >> Real))
power = defconst('**', Real >> (Real >> Real), infix = True) 
# not overloaded for now

# unary operations on the reals

uminus_real = defconst('uminus_real', Real >> Real)
abs_real = defconst('abs_real', Real >> Real)

# binary predicates on the reals

lt_real = defconst('lt_real', Real >> (Real >> Bool))
# lt_real = defconst('gt_real', Real >> (Real >> Bool))
le_real = defconst('le_real', Real >> (Real >> Bool))
# ge_real = defconst('ge_real', Real >> (Real >> Bool))

# integers

Int = deftype('Int')
int_sub_real = defsub('int_sub_real', Int <= Real)

# binary operations on the integers

add_int = defconst('add_int', Int >> (Int >> Int))
mul_int = defconst('mul_int', Int >> (Int >> Int))
minus_int = defconst('minus_int', Int >> (Int >> Int))
divide_int = defconst('divide_int', Int >> (Int >> Int))
mod = defconst('%', Int >> (Int >> Int), infix = True)

# unary operations on the integers

uminus_int = defconst('uminus_int', Int >> Int)
abs_int = defconst('abs_int', Int >> Int)

# binary predicates on the integers

lt_int = defconst('lt_int', Int >> (Int >> Bool))
# for now, gt is defined in terms of lt
# gt_int = defconst('gt_int', Int >> (Int >> Bool))
le_int = defconst('le_int', Int >> (Int >> Bool))
# ditto
# ge_int = defconst('ge_int', Int >> (Int >> Bool))

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
uop = defconst('uop', X >> X)

Mul = defclass('Mul', [X, op], true)
mul_ev = Const('mul_ev', Mul(X, op))
mul = defexpr('*', abst([X, op, mul_ev], op), \
              pi([X, op, mul_ev], X >> (X >> X), impl=True), \
              infix=True)
definstance('Mul_real', Mul(Real, mul_real), triv())
definstance('Mul_int', Mul(Int, mul_int), triv())

Add = defclass('Add', [X, op], true)
add_ev = Const('add_ev', Add(X, op))
add = defexpr('+', abst([X, op, add_ev], op), \
              pi([X, op, add_ev], X >> (X >> X), impl=True), \
              infix=True)
definstance('Add_real', Add(Real, add_real), triv())
definstance('Add_int', Add(Int, add_int), triv())

Minus = defclass('Minus', [X, op], true)
minus_ev = Const('minus_ev', Minus(X, op))
minus = defexpr('-', abst([X, op, minus_ev], op), \
              pi([X, op, minus_ev], X >> (X >> X), impl=True), \
              infix=True)
definstance('Minus_real', Minus(Real, minus_real), triv())
definstance('Minus_int', Minus(Int, minus_int), triv())

Div = defclass('Div', [X, op], true)
div_ev = Const('div_ev', Div(X, op))
div = defexpr('/', abst([X, op, div_ev], op), \
              pi([X, op, div_ev], X >> (X >> X), impl=True), \
              infix=True)
definstance('Div_real', Div(Real, divide_real), triv())
definstance('Div_int', Div(Int, divide_int), triv())

Uminus = defclass('Uminus', [X, uop], true)
uminus_ev = Const('uminus_ev', Uminus(X, uop))
#TODO: can we use '-' for this as well?
uminus = defexpr('uminus', abst([X, uop, uminus_ev], uop), \
              pi([X, uop, uminus_ev], X >> X, impl=True), \
              infix=True)
definstance('Uminus_real', Uminus(Real, uminus_real), triv())
definstance('Uminus_int', Uminus(Int, uminus_int), triv())

Abs = defclass('Abs', [X, uop], true)
abs_ev = Const('abs_ev', Abs(X, uop))
# note: 'abs' is a built-in reserved symbol
absf = defexpr('abs', abst([X, uop, abs_ev], uop), \
              pi([X, uop, abs_ev], X >> X, impl=True), \
              infix=True)
definstance('Abs_real', Abs(Real, abs_real), triv())
definstance('Abs_int', Abs(Int, abs_int), triv())


pred = defconst('pred', X >> (X >> Bool))

Lt = defclass('Lt', [X, pred], true)
lt_ev = Const('lt_ev', Lt(X, pred))
lt = defexpr('<', abst([X, pred, lt_ev], pred), \
             pi([X, pred, lt_ev], X >> (X >> Bool), impl=True), \
             infix=True)
definstance('Lt_real', Lt(Real, lt_real), triv())
definstance('Lt_int', Lt(Int, lt_int), triv())

Le = defclass('Le', [X, pred], true)
le_ev = Const('le_ev', Le(X, pred))
le = defexpr('<=', abst([X, pred, le_ev], pred), \
             pi([X, pred, le_ev], X >> (X >> Bool), impl=True), \
             infix=True)
definstance('Le_real', Le(Real, lt_real), triv())
definstance('Le_int', Le(Int, le_int), triv())

verbose = True
