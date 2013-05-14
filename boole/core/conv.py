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
    if expr.is_app() and expr.fun.is_bound() and \
           expr.fun.binder.is_abst():
        return subst_expr([expr.arg], expr.fun.expr)
    elif expr.is_proj() and expr.expr.is_tuple() and \
             expr.index < len(expr.expr):
        return expr.expr.exprs[expr.index]
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
        """Do nothing
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
        var, open_expr = open_bound_with_fresh(expr)
        dom = self.visit(expr.dom, *args, **kwargs)
        body = self.visit(open_expr, *args, **kwargs)
        body = abstract_expr([var], body)
        return Bound(expr.binder, dom, body)

    def visit_app(self, expr, *args, **kwargs):
        #We do not normalize the evidence term, as it
        #plays no role in conversion
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return head_beta(App(expr.conv, fun, arg))

    def visit_sig(self, expr, *args, **kwargs):
        tel = self.visit(expr.telescope, *args, **kwargs)
        return Sig(tel)

    def visit_tuple(self, expr, *args, **kwargs):
        exprs = [self.visit(e, *args, **kwargs)\
                 for e in expr.exprs]
        type = self.visit(expr.type, *args, **kwargs)
        return Tuple(exprs, type)

    def visit_proj(self, expr, *args, **kwargs):
        tup = self.visit(expr.expr, *args, **kwargs)
        return head_beta(Proj(expr.index, tup))

    def visit_ev(self, expr, *args, **kwargs):
        #do nothing, as evidence terms have
        #no computational content.
        return expr

    def visit_eq(self, expr, *args, **kwargs):
        lhs = self.visit(expr.lhs, *args, **kwargs)
        rhs = self.visit(expr.rhs, *args, **kwargs)
        return Eq(lhs, rhs)

    def visit_box(self, expr, *args, **kwargs):
        inside = self.visit(expr.expr, *args, **kwargs)
        return head_beta(Box(expr.conv, inside, expr.type))

    def visit_tele(self, expr, *args, **kwargs):
        open_tel = open_tele_with_fresh(expr)
        tel_red = [(v, self.visit(e, *args, **kwargs)) for \
         v, e in open_tel]
        return sig(*tel_red)

    @info.same_info
    def visit(self, expr, *args, **kwargs):
        return expr.accept(self, *args, **kwargs)
        

def par_beta(expr):
    """Perform parallel reduction of beta-expressions
    
    Arguments:
    - `expr`:
    """
    return ParBeta().visit(expr)
