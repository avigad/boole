#############################################################################
#
# conv.py
#
# description: Compute and compare normal forms.
#
#
# Authors:
# Cody Roux
#
#
##############################################################################

from expr import *
import info


def head_beta(expr):
    """Perform the following reductions:
    App(_,Abs(x,T,t),u) --> t[u/x]
    Proj(i,(t0,...,tn)) --> ti    if i <= n
    Box(_,t,T) --> t

    And do nothing otherwise.
    
    Arguments:
    - `expr`: an arbitrary expression.
    """
    if expr.is_app() and expr.fun.is_abst():
        return subst_expr([expr.arg], expr.fun.body)
    elif expr.is_fst() and expr.expr.is_pair():
        return expr.expr.fst
    elif expr.is_snd() and expr.expr.is_pair():
        return expr.expr.snd
    elif expr.is_box():
        return expr.expr
    else:
        return expr


class ParBeta(ExprVisitor):
    """Parallel beta reduction:
    reduce all beta-redexes from the bottom-up,
    without reducing redexes created by substitution
    of a bound variable.
    """
    
    def __init__(self):
        """Take as argument the substitution function,
        the opening and abstraction functions.
        """
        ExprVisitor.__init__(self)

    def visit_const(self, expr, *args, **kwargs):
        return expr

    def visit_db(self, expr, *args, **kwargs):
        return expr

    def visit_type(self, expr, *args, **kwargs):
        return expr

    def visit_kind(self, expr, *args, **kwargs):
        return expr

    def visit_bool(self, expr, *args, **kwargs):
        return expr

    def visit_bound(self, expr, *args, **kwargs):
        var, opened = open_bound_fresh(expr)
        dom = self.visit(expr.dom, *args, **kwargs)
        body = self.visit(opened, *args, **kwargs)
        body = abstract_expr([var], body)
        return Bound(expr.binder, dom, body)

    def visit_app(self, expr, *args, **kwargs):
        #We do not normalize the evidence term, as it
        #plays no role in conversion
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return head_beta(App(expr.conv, fun, arg))

    def visit_pair(self, expr, *args, **kwargs):
        fst = self.visit(expr.fst, *args, **kwargs)
        snd = self.visit(expr.snd, *args, **kwargs)
        type = self.visit(expr.type, *args, **kwargs)
        return Pair(fst, snd, type)

    def visit_fst(self, expr, *args, **kwargs):
        red_expr = self.visit(expr.expr, *args, **kwargs)
        return head_beta(Fst(red_expr))

    def visit_snd(self, expr, *args, **kwargs):
        red_expr = self.visit(expr.expr, *args, **kwargs)
        return head_beta(Snd(red_expr))

    def visit_ev(self, expr, *args, **kwargs):
        #do nothing, as evidence terms have
        #no computational content.
        return expr

    def visit_sub(self, expr, *args, **kwargs):
        lhs = self.visit(expr.lhs, *args, **kwargs)
        rhs = self.visit(expr.rhs, *args, **kwargs)
        return Sub(lhs, rhs)

    def visit_box(self, expr, *args, **kwargs):
        inside = self.visit(expr.expr, *args, **kwargs)
        return head_beta(Box(expr.conv, inside, expr.type))

    def visit_mvar(self, expr, *args, **kwargs):
        return expr

    def visit_tele(self, expr, *args, **kwargs):
        consts, opened_ty = open_tele_fresh(expr)
        ty_red = [self.visit(ty, *args, **kwargs) for \
                  ty in opened_ty]
        fr_vars = [c.name for c in consts]
        ty_red = [abstract_expr(fr_vars, ty) for ty in ty_red]
        return Tele(expr.vars, ty_red)

    @info.same_info
    def visit(self, expr, *args, **kwargs):
        return expr.accept(self, *args, **kwargs)
        

def par_beta(expr):
    """Perform parallel reduction of beta-expressions
    
    Arguments:
    - `expr`:
    """
    return ParBeta().visit(expr)


def beta_norm(expr):
    """Repeat beta reduction until
    the term is unchanged. May loop!
    
    Arguments:
    - `expr`:
    """
    unred = expr
    red = par_beta(expr)
    while not red.equals(unred):
        unred = red
        red = par_beta(unred)
    return red


def unfold(names, exp, context):
    """Replace a set of constants designated by names
    in expr, by looking up their definition in the context
    
    Arguments:
    - `names`: A list of strings
    - `exp`: An expression
    - `context`: A context
    """
    exprs = []
    for name in names:
        e = context.get_from_field(name, 'defs')
        exprs.append(e)
    return sub_in(exprs, names, exp)


def unfold_once(exp, context):
    """Unfolds ALL defined constants in an expression,
    NON recursive.
    
    Arguments:
    - `exp`: an expression
    - `context`: a context
    """
    all_names = [n for n in context.defs]
    return unfold(all_names, exp, context)


def unfold_all(exp, context):
    """Unfolds ALL defined constants in an expression,
    recursively.
    
    Arguments:
    - `exp`: an expression
    - `context`: a context
    """
    unred = exp
    all_names = [n for n in context.defs]
    red = unfold(all_names, exp, context)
    while not red.equals(unred):
        unred = red
        red = unfold(all_names, unred, context)
    return red
