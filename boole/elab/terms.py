###############################################################################
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
###############################################################################

from boole.core.info import *
from boole.core.context import *
from boole.core.expr import Const, Sub, Pair, Fst, Snd, Box, root_app, \
  root_clause
import boole.core.expr as e
import boole.core.typing as typing
import elab
from elab import app_expr, mvar_infer, open_expr, sub_mvar, root_pi, subst_expr
import boole.core.tactics as tac
import boole.core.goals as goals
import unif as u
from boole.semantics.value import Value


###############################################################################
#
# Exceptions associated with expressions
#
###############################################################################

class Term_Error(Exception):
    """Errors for expressions
    """
    def __init__(self, mess):
        Exception.__init__(self, mess)


################################################################################
#
# String methods for terms 
#
###############################################################################

# TODO: wouldn't it be clearer to inline most of these in the definitions
# of term_str and typ_str?

# TODO: print_app uses info fields 'print_iterable' and 'print_Implies' to
# determine if special print methods are needed for application.
# Is that o.k.?

# TODO: right now the str method uses the name of the constant to print out
# a value. Should the value class instead determine how values are printed out?

def print_app(expr):
    """Takes an application and prints it in the following manner:
    if the application is of the form (..(f a0)... an), print
    f(a0,...,an), or (a0 f a1) if f is infix.
    
    Arguments:
    - `expr`: an expression
    """
    root, args = dest_app_implicit(expr)
    if root.is_const() and root.info.print_iterable_app:
        return print_iterable_app(expr, root)
    elif root.is_const() and root.info.print_Implies:
        return print_Implies(expr)
    elif root.info.infix and len(args) == 2:
        return "{0!s} {1!s} {2!s}".format(args[0], root, args[1])
    else:
        args_str = map(str, args)
        args_str = ", ".join(args_str)
        return "{0!s}({1!s})".format(root, args_str)
    
def print_iterable_app(expr, op):
    """Prints an expression of the form
    op(... op(op(e1, e2), e3) ..., en) as 'op(e1, ..., en)', or, if op
    is infix, as 'e1 op e2 op ... op en'
    """
    args = dest_binop_left(expr, op)
    args_str = map(str, args)
    if op.info.infix:
        return (' '+str(op)+' ').join(args_str)
    else:
        return "{0!s}({1!s})".format(op, ', '.join(args_str))

def print_Implies(expr):
    """Prints an implication Implies([h1, ..., hn], conc)
    """
    hyps, conc = dest_Implies(expr)
    if len(hyps) == 1:
        return "{0!s}({1!s}, {2!s})".format(Implies, hyps[0], conc)
    else:
        hyp_str = ", ".join(map(str, hyps))
        return "{0!s}([{1!s}], {2!s})".format(Implies, hyp_str, conc)
    
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

# TODO: it is confusing that there are to_string methods in expr.py, in 
# addition to these.

def print_bound(expr):
    b = expr.binder
    vars, body = dest_binder(expr)
    if len(vars) == 1:
        return "{0!s}({1!s}, {2!s})".format(b.name, vars[0], body)
    else:
        vars_str = ', '.join(map(str, vars))
        return "{0!s}([{1!s}], {2!s})".format(b.name, vars_str, body)
# old code:
#    var = expr.binder.var
#    open_self = open_expr(var, expr.dom, expr.body)
#    return "{0!s}({1!s}, {2!s})".format(\
#        expr.binder.name, expr.binder.var, open_self)

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


###############################################################################
#
# Constructors for terms and types
#
###############################################################################

# 'standard' information for terms and types.
# The fields are filled in below.

st_term = ExprInfo('term_info', {})
st_typ = ExprInfo('type_info', {})

def with__info(info):
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

# cast Python objects to appropriate expressions
def to_expr(expr):
    if isinstance(expr, int):
        return ii(expr)
    elif isinstance(expr, float):
        return rr(expr)
    else:
        return expr

@with__info(st_term)
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

@with__info(st_term)
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

@with__info(st_term)
def const(name, type, infix=None):
    return Const(name, type)

# Special call methods for 'And', 'Or', and 'Implies'. Allosw e.g.
# And(e1, e2, e3) and Implies([e1, e2, e3], e4), and specifies that the
# resulting expressions should print out this way.
# This also works for add and mul, so we can write e.g.
#   add(e1, e2, ...) and mul(e1, e2, ...)

def mk_iterative_app(op):
    """For example, mk_iterative_app(And) is a function that builds a binary
    'And' with the right __str__ method.
    """
    def f(e1, e2):
        return tm_call(op, e1, e2)
    return f

def iterative_app_call(op, *args):
    e = reduce(mk_iterative_app(op), args[1:], args[0])
    return e

# note: to use reduce, the arguments have to go in this order
def mk_Implies(conc, hyp):
    e = tm_call(Implies, hyp, conc)
#    e.info['__str__'] = print_Implies
    return e
    
# op here should be Implies. But this could be abstracted out as in the 
# last case to generalize this behavior
def Implies_call(op, hyps, conc):
    if isinstance(hyps, list):
        return reduce(mk_Implies, reversed(hyps), conc)
    else:
        return tm_call(Implies, hyps, conc)
    
#TODO: make this more clever
@with__info(st_term)
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
 
# without the decorator, would have term info
@with__info(st_typ)
def type_arrow(type1, type2):
    return pi(Const('_', type1), type2)

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
    
# a special call method for types - create a constant of that type       
def typ_call(type, name_str):
    names = _str_to_list(name_str)
    if len(names) == 1:
        return defconst(names[0], type)
    else:
        consts = ()
        for name in names:
            consts += (defconst(name, type),)
        return consts

@with__info(st_typ)
def typ_mul(type1, type2):
    return sig(Const('_', type1), type2)

@with__info(st_typ)
def typ_le(type1, type2):
    return Sub(type1, type2)

# TODO: Why not use Type instead of e.Type() here?
@with__info(st_typ)
def mktype(name):
    """
    
    Arguments:
    - `name`:
    """
    return Const(name, e.Type())


###############################################################################
#
# Set the appropriate syntactic operations for terms and types
#
###############################################################################

# operations for terms
st_term['__str__'] = tm_str
st_term['__call__'] = tm_call
st_term['__getitem__'] = get_pair
st_term['__eq__'] = (lambda expr1, expr2: eq(expr1, expr2)) 
st_term['__ne__'] = (lambda expr1, expr2: Not(eq(expr1, expr2)))
st_term['__add__'] = (lambda expr1, expr2: add(expr1, expr2))
st_term['__radd__'] = (lambda expr2, expr1: add(expr1, expr2))
st_term['__mul__'] = (lambda expr1, expr2: mul(expr1, expr2))
st_term['__rmul__'] = (lambda expr2, expr1: mul(expr1, expr2))
st_term['__sub__'] = (lambda expr1, expr2: minus(expr1, expr2))
st_term['__rsub__'] = (lambda expr2, expr1: minus(expr1, expr2))
st_term['__div__'] = (lambda expr1, expr2: div(expr1, expr2))
st_term['__rdiv__'] = (lambda expr2, expr1: div(expr1, expr2))
st_term['__mod__'] = (lambda expr1, expr2: mod(expr1, expr2))
st_term['__rmod__'] = (lambda expr2, expr1: mod(expr1, expr2))
st_term['__pow__'] = (lambda expr1, expr2: power(expr1, expr2))
st_term['__rpow__'] = (lambda expr2, expr1: power(expr1, expr2))
st_term['__rshift__'] = type_arrow
st_term['__le__'] = (lambda expr1, expr2: le(expr1, expr2))
st_term['__ge__'] = (lambda expr1, expr2: le(expr2, expr1))
st_term['__lt__'] = (lambda expr1, expr2: lt(expr1, expr2))
st_term['__gt__'] = (lambda expr1, expr2: lt(expr2, expr1))
st_term['__abs__'] = (lambda expr: absf(expr))
st_term['__neg__'] = (lambda expr: uminus(expr))

# operations for types
st_typ['__call__'] = typ_call
st_typ['__mul__'] = typ_mul
st_typ['__rshift__'] = type_arrow
st_typ['__str__'] = typ_str
st_typ['__le__'] = typ_le


###############################################################################
#
# More term and type constructors
#
# TODO: should Pi, Abst, and so on be capitalized like Forall and Exists?
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

@with__info(st_term)
def pi_base(var, codom, **kwargs):
    return elab.pi(var, codom, **kwargs)

def pi(var, codom, **kwargs):
    return fold_over(pi_base, var, codom, **kwargs)

@with__info(st_term)
def abst_base(var, body):
    return elab.abst(var, body)

def abst(var, body):
    return fold_over(abst_base, var, body)

@with__info(st_term)
def Forall_base(var, prop):
    return elab.forall(var, prop)

def Forall(var, prop):
    return fold_over(Forall_base, var, prop)

@with__info(st_term)
def Exists_base(var, prop):
    return elab.exists(var, prop)

def Exists(var, prop):
    return fold_over(Exists_base, var, prop)

@with__info(st_term)
def sig_base(var, codom):
    return elab.sig(var, codom)

def sig(var, codom):
    return fold_over(sig_base, var, codom)

# TODO: are these next two needed?
@with__info(st_term)
def true():
    return elab.true()

@with__info(st_term)
def false():
    return elab.false()

# TODO: what does this do?
@with__info(st_term)
def nullctxt():
    return elab.nullctxt()

@with__info(st_term)
def triv():
    return elab.trivial

@with__info(st_term)
def cast(expr, ty):
    """cast an expression to ty
    
    Arguments:
    - `expr`: an expression
    - `ty`: a type equal to the type of expr
    """
    return Box(triv(), expr, ty)


###############################################################################
#
# Destructors -- routines to unpack a forall, etc.
#
###############################################################################

# TODO: right now, open_expr in expr.py creates a constant without syntax.
#    attached. Should that be deprecated in favor of the functions below?

def dest_app_implicit(expr):
    """If a term is of the form (..(f a0).. an), return the pair
    (f, [ai,..., ak]) where the ai...ak are the non-implicit arguments of f.
    
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
     
# TODO: right now, the next two functions instantiate bound variables with 
#   the name originally provided by the user. But really we should generate
#   a fresh name close by.

# TODO: because we need the same routines for pi, sigma, and abstr as well,
#   it seemed to make sense to have a general "dest_binder". But it digs
#   into the fields of the classes; should this be abstracted more?

# TODO: annoyingly, these functions failed on expressions with metavariables,
#   because I was calling the wrong substitution (in core.expr, rather than 
#   elab.elab). This is confusing! Why note just make the metavariables
#   part of the core and eliminate the duplication? At least, the functions
#   should only be defined once.
 
def instantiate_bound_expr(e1, e2):
    """Takes an expression e1 of the form  'Binder dom, body', and returns 
    the result of substituting e2 in body.
    """
    if not e1.is_bound():
        raise Term_Error('instantiate_bound: {0!s} is not bound'.format(e1))
    return subst_expr([e2], e1.body)

def dest_one_binder(expr):
    """Returns the pair (v, b) where v is a variable, b is an expression,
    and expr is the result of binding v in b expr.binder.
    """
    if not expr.is_bound():
        raise Term_Error('dest_one_binder: {0!s} is not bound'.format(expr))
    vname = expr.binder.var
    dom = expr.dom
    v = const(vname, dom)    # change this -- see above
    b = instantiate_bound_expr(expr, v)
    return (v, b)

def dest_binder(expr):
    """Returns the pair (vlist, b) where vlist is a list of variables, 
    b is an expression, and expr is the result of iteratively binding 
    the variables in vlist in b, using the same binder.
    """
    if not expr.is_bound():
        raise Term_Error('dest_binder: {0!s} is not bound'.format(expr))
    binder_name = expr.binder.name
    b = expr
    vlist = []
    while b.is_bound() and b.binder.name == binder_name:
        v, b = dest_one_binder(b)         
        vlist.append(v)
    return (vlist, b)
   
def dest_one_Forall(expr):
    """Returns a pair (v, b) such that v is a variable, b is an expression, 
    and expr = Forall(v, b).
    """    
    if not expr.is_forall(): 
        raise Term_Error('dest_one_Forall: {0!s} is not a Forall'.format(expr))
    return dest_one_binder(expr)

def dest_Forall(expr):
    """Returns a pair (vlist, b) such that vlist is a list of variables, 
    b is an expression, and expr = Forall(vlist, b).
    """    
    if not expr.is_forall(): 
        raise Term_Error('dest_Forall: {0!s} is not a Forall'.format(expr))
    return dest_binder(expr)

def dest_one_Exists(expr):
    """Returns a pair (v, b) such that v is a variable, b is an expression, 
    and expr = Exists(v, b).
    """    
    if not expr.is_exists(): 
        raise Term_Error('dest_one_Exists: {0!s} is not a Exists'.format(expr))
    return dest_one_binder(expr)

def dest_Exists(expr):
    """Returns a pair (vlist, b) such that vlist is a list of variables, 
    b is an expression, and expr = Exists(vlist, b).
    """    
    if not expr.is_exists(): 
        raise Term_Error('dest_Exists: {0!s} is not a Exists'.format(expr))
    return dest_binder(expr)

def dest_one_pi(expr):
    """Returns a pair (v, b) such that v is a variable, b is an expression, 
    and expr = pi(v, b).
    """    
    if not expr.is_pi(): 
        raise Term_Error('dest_one_pi: {0!s} is not a pi'.format(expr))
    return dest_one_binder(expr)

def dest_pi(expr):
    """Returns a pair (vlist, b) such that vlist is a list of variables, 
    b is an expression, and expr = pi(vlist, b).
    """    
    if not expr.is_pi(): 
        raise Term_Error('dest_pi: {0!s} is not a pi'.format(expr))
    return dest_binder(expr)

def dest_one_sig(expr):
    """Returns a pair (v, b) such that v is a variable, b is an expression, 
    and expr = sig(v, b).
    """    
    if not expr.is_sig(): 
        raise Term_Error('dest_one_sig: {0!s} is not a sig'.format(expr))
    return dest_one_binder(expr)

def dest_sig(expr):
    """Returns a pair (vlist, b) such that vlist is a list of variables, 
    b is an expression, and expr = sig(vlist, b).
    """    
    if not expr.is_sig(): 
        raise Term_Error('dest_sig: {0!s} is not a sig'.format(expr))
    return dest_binder(expr)

def dest_one_abst(expr):
    """Returns a pair (v, b) such that v is a variable, b is an expression, 
    and expr = abst(v, b).
    """    
    if not expr.is_abst(): 
        raise Term_Error('dest_one_abst: {0!s} is not a abst'.format(expr))
    return dest_one_binder(expr)

def dest_abst(expr):
    """Returns a pair (vlist, b) such that vlist is a list of variables, 
    b is an expression, and expr = abst(vlist, b).
    """    
    if not expr.is_abst(): 
        raise Term_Error('dest_abst: {0!s} is not a abst'.format(expr))
    return dest_binder(expr)

def dest_binop_left(expr, op):   
    """Assuming 'op' is a binary operation, returns a list of expressions, 
    elist, such that 
    expr = op(op(...op(elist[0], elist[1]), ... elist[n-1]), elist[n]),
    that is, an iterated application of op associating to the left.
    """
    if not expr.is_app():
        raise Term_Error('dest_binop_left: DEBUG')
#        raise Term_Error('dest_binop_left: {0!s} is not {1!s}'.format(expr, op))
    r, args = dest_app_implicit(expr)
    if not r.is_const() or r.name != op.name:
        raise Term_Error('dest_binop_left: {0!s} is not {1!s}'.format(expr, op))
    elist = [args[1]]
    expr = args[0]
    while r.is_const() and r.name == op.name and expr.is_app():
        r, args = dest_app_implicit(expr)
        if r.is_const() and r.name == op.name:
            elist.append(args[1])
            expr = args[0]
    elist.append(expr)
    elist.reverse()
    return elist

def dest_binop_right(expr, op):   
    """Assuming 'op' is a binary operation, returns a list of expressions, 
    elist, such that 
    expr = op(elist[0], op(elist[1], ... op(elist[n-1], elist[n])))
    that is, an iterated application of op associating to the right.
    """
    if not expr.is_app():
        raise Term_Error('dest_binop: {0!s} is not an {1!s}'.format(expr, op))
    r, args = dest_app_implicit(expr)
    if not r.is_const() or r.name != op.name:
        raise Term_Error('dest_binop: {0!s} is not {1!s}'.format(expr, op))
    elist = [args[0]]
    expr = args[1]
    while r.is_const() and r.name == op.name and expr.is_app():
        r, args = dest_app_implicit(expr)
        if r.is_const() and r.name == op.name:
            elist.append(args[0])
            expr = args[1]
    elist.append(expr)
    return elist

# TODO: maybe the next four are not needed
def dest_And(expr):
    """Returns a list elist of expressions such that expr = And(elist)
    """
    return dest_binop_left(expr, And)

def dest_Or(expr):
    """Returns a list elist of expressions such that expr = Or(elist)
    """
    return dest_binop_left(expr, Or)

def dest_add(expr):
    """Returns a list elist of expressions such that expr = 
    elist[0] + ... + elist[n]
    """
    return dest_binop_left(expr, add)

def dest_mul(expr):
    """Returns a list elist of expressions such that expr = 
    elist[0] + ... + elist[n]
    """
    return dest_binop_left(expr, mul)

def dest_Implies(expr):
    """Returns a tuple hlist, conc of expressions such that 
    expr = Implies(hlist, conc)
    """
    elist = dest_binop_right(expr, Implies)
    return elist[:-1], elist[-1]


###############################################################################
#
# A global variable to determine whether to use verbose output when 
#   checking and elaborating terms, and defining objects
#
###############################################################################

verbose = False

def set_verbose(setting = True):
    global verbose
    
    verbose = setting


###############################################################################
#
# Term checking and elaboration. 
#
# TODO: right now these just use the default local context. 
#
###############################################################################

elab_tac = tac.par(u.unify) >> tac.trytac(u.instances)
type_tac = tac.auto >> tac.trytac(u.instances)

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


###############################################################################
#
# Routines to create objects and put them in a context.
#
# TODO: right now these just use the default local context. Abstract over
#   local_ctxt.
#
# TODO: clean these! 
#
###############################################################################

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

def defexpr(name, value, type=None, infix=None, tactic=None):
    """Define an expression with a given type and value.
    Checks that the type of value is correct, and adds the defining
    equation to the context.
    
    Arguments:
    - `name`: a string
    - `type`: an expression
    - `value`: an expression
    """
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
# Create a context for the basic definitions.
#
###############################################################################

local_ctxt = Context("local_ctxt")


###############################################################################
#
# Create some basic kinds of values.
#
# Terms of type value_description can be used
#
###############################################################################

# TODO: what is is_const used for?

value_description = deftype('value_description')
int_val = defconst('int_val', value_description)
float_val = defconst('float_val', value_description)
 
def ii(n):
    val = Value(n, desc = int_val, is_num = True)
    return Const(str(n), Int, val, is_const=True)


def rr(n):
    val = Value(n, desc = float_val, is_num = True)    
    return Const(str(n), Real, is_const=True)

enumtype_val = defconst('enumtype_val', value_description)
enumelt_val = defconst('enum_val', value_description)

def defenumtype(name, elts):
    """ Takes a name and list of strings, and builds an enumerated type
    
    For example: Beatles, (John, Paul, George, Ringo) =
      defenumtype('Beatles', ['John', 'Paul', 'George', 'Ringo')
    """
    enumtype = deftype(name)
    enumtype.value = Value(elts, enumtype_val)
    consts = ()
    for e in elts:
        c = defconst(e, enumtype)
        c.value = Value(e, enumelt_val)
        consts += (c,)
    return enumtype, consts


###############################################################################
#
# Equality and basic sorts
#
###############################################################################

def equals(e1, e2):
    return And(Sub(e1, e2), Sub(e2, e1))

#create a single instance of Bool() and Type().
Bool = e.Bool()
Bool.info.update(st_typ)

Type = e.Type()
Type.info.update(st_typ)


###############################################################################
#
# Logical operations
#
###############################################################################

# allow input and output syntax And(e1, e2, ..., en)
And = defconst('And', Bool >> (Bool >> Bool))
And.info['__call__'] = iterative_app_call
And.info['print_iterable_app'] = True

# allow input and output syntax Or(e1, e2, ..., en)
Or = defconst('Or', Bool >> (Bool >> Bool))
Or.info['__call__'] = iterative_app_call
Or.info['print_iterable_app'] = True

Not = defconst('Not', Bool >> Bool)

p = Bool('p')
q = Bool('q')
# allow input and output syntax Implies([h1, ..., hn], conc)
Implies = defexpr('Implies', abst(p, abst(q, Sub(p, q))), \
               Bool >> (Bool >> Bool))
Implies.info['__call__'] = Implies_call
Implies.info['print_Implies'] = True

#This is equivalent to the constant given as type to terms
# of the form Ev(tele), as constants are only compared
# by name. As a result, it is proven using the auto tactic
true = defconst('true', Bool)

false = defconst('false', Bool)


###############################################################################
#
# Basic operations on the integers and reals
#
###############################################################################

# reals

Real = deftype('Real')

# binary operations on the reals

add_real = defconst('add_real', Real >> (Real >> Real))
mul_real = defconst('mul_real', Real >> (Real >> Real))
minus_real = defconst('minus_real', Real >> (Real >> Real))
divide_real = defconst('divide_real', Real >> (Real >> Real))
power = defconst('**', Real >> (Real >> Real), infix = True) 
# TODO: not overloaded for now

# unary operations on the reals

uminus_real = defconst('uminus_real', Real >> Real)
abs_real = defconst('abs_real', Real >> Real)

# binary predicates on the reals

lt_real = defconst('lt_real', Real >> (Real >> Bool))
le_real = defconst('le_real', Real >> (Real >> Bool))

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
le_int = defconst('le_int', Int >> (Int >> Bool))


###############################################################################
#
# Type classes and polymorphic constrants for numeric operations
#
###############################################################################

X = deftype('X')

x = X('x')
y = X('y')

eq = defexpr('==', abst([X, x, y], And(Sub(x, y), Sub(y, x))), \
             pi(X, X >> (X >> Bool), impl=True), infix=True)

op = defconst('op', X >> (X >> X))
uop = defconst('uop', X >> X)

# allow input syntax mul(e1, e2, ..., en)
Mul = defclass('Mul', [X, op], true)
mul_ev = Const('mul_ev', Mul(X, op))
mul = defexpr('*', abst([X, op, mul_ev], op), \
              pi([X, op, mul_ev], X >> (X >> X), impl=True), \
              infix=True)
mul.info['__call__'] = iterative_app_call
definstance('Mul_real', Mul(Real, mul_real), triv())
definstance('Mul_int', Mul(Int, mul_int), triv())

# allow input synatx add(e1, e2, ..., en)
Add = defclass('Add', [X, op], true)
add_ev = Const('add_ev', Add(X, op))
add = defexpr('+', abst([X, op, add_ev], op), \
              pi([X, op, add_ev], X >> (X >> X), impl=True), \
              infix=True)
add.info['__call__'] = iterative_app_call
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


