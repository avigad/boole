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


def head_beta(expr, subst):
    """Perform the following reductions:
    App(_,Abs(x,T,t),u) --> t[u/x]
    Proj(i,(t0,...,tn)) --> ti    if i <= n
    Box(_,t,T) --> t

    And do nothing otherwise.
    
    Arguments:
    - `expr`: an arbitrary expression.
    - `subst`: a substitution function
    """
    if expr.is_app() and expr.fun.is_abst():
        return subst([expr.arg], expr.fun.body)
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
        self.subst = subst_expr
        self.open_expr = open_bound_fresh
        self.open_tele = open_tele_fresh
        self.abst = abstract_expr

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
        var, opened = self.open_expr(expr)
        dom = self.visit(expr.dom, *args, **kwargs)
        body = self.visit(opened, *args, **kwargs)
        body = self.abst([var], body)
        return Bound(expr.binder, dom, body)

    def visit_app(self, expr, *args, **kwargs):
        #We do not normalize the evidence term, as it
        #plays no role in conversion
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return head_beta(App(expr.conv, fun, arg), self.subst)

    def visit_pair(self, expr, *args, **kwargs):
        fst = self.visit(expr.fst, *args, **kwargs)
        snd = self.visit(expr.snd, *args, **kwargs)
        type = self.visit(expr.type, *args, **kwargs)
        return Pair(fst, snd, type)

    def visit_fst(self, expr, *args, **kwargs):
        red_expr = self.visit(expr.expr, *args, **kwargs)
        return head_beta(Fst(red_expr), self.subst)

    def visit_snd(self, expr, *args, **kwargs):
        red_expr = self.visit(expr.expr, *args, **kwargs)
        return head_beta(Snd(red_expr), self.subst)

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
        return head_beta(Box(expr.conv, inside, expr.type), self.subst)

    def visit_tele(self, expr, *args, **kwargs):
        consts, opened_ty = self.open_tele(expr)
        ty_red = [self.visit(ty, *args, **kwargs) for \
                  ty in opened_ty]
        fr_vars = [c.name for c in consts]
        ty_red = [self.abst(fr_vars, ty) for ty in ty_red]
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
    while not (red.equals(unred)):
        unred = red
        red = par_beta(unred)
    return red
