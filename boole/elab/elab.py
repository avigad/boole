#############################################################################
#
# elab.py
#
# description: Meta-Variables and unification for implicit arguments
#
#
# Authors:
# Cody Roux
#
#
##############################################################################

import boole.core.expr_base as expr_base
import boole.core.expr as e
import boole.core.typing as t
import boole.core.vargen as vargen

meta_var_gen = vargen.VarGen()

class Mvar(expr_base.Expr):
    """Unification variables for implicit arguments
    """
    
    def __init__(self, name, type, **kwargs):
        """
        Same definition as for Const, with a simple
        tag expressing status as Mvar
        """
        expr_base.Expr.__init__(self)
        self.name = name
        self.type = type
        self.value = None
        for k in kwargs:
            self.info[k] = kwargs[k]
        self.info['is_mvar'] = True

    def accept(self, visitor, *args, **kwargs):
        return visitor.visit_mvar(self, *args, **kwargs)

    def set_val(self, val):
        """Give a value to the meta-variable
        
        Arguments:
        - `val`: an expression
        """
        self.value = val


class MvarInfer(t.ExprInfer):
    """Infer the type and generate constraints for a term containing
    meta-variables.
    """
    
    def __init__(self):
        t.ExprInfer.__init__(self)

    #TODO: Should this add a constraint?
    def visit_mvar(self, expr, *args, **kwargs):
        sort = self.visit(expr.type, *args, **kwargs)
        if t.is_sort(sort):
            return expr.type


def mk_meta(name, type):
    """Create a meta-variable with a fresh
    name and the given type.
    
    Arguments:
    - `name`:
    - `type`:
    """
    fresh_name = meta_var_gen.get_name(name)
    return Mvar(fresh_name, type)


def app_expr(f, f_ty, conv, args):
    """Applies a function to a list of
    arguments, some of which are implicit.
    
    Arguments:
    - `f`: an expression denoting the function
    - `f_ty`: the function type
    - `conv`: list of evidence for the type conversions
    of each argument
    - `args`: a list of arguments
    """
    tm = f
    rem_args = args
    rem_conv = conv
    rem_ty = f_ty
    while len(rem_args) != 0:
        if rem_ty.is_bound() and rem_ty.binder.is_pi()\
           and rem_ty.dom.info.implicit:
            mvar = mk_meta(rem_ty.binder.var, rem_ty.dom)
            mconv = mk_meta('Meta_conv', e.Sub(rem_ty.dom, rem_ty.dom))
            tm = t.App(mconv, tm, mvar)
            rem_ty = e.subst_expr([mvar], rem_ty.body)
        elif rem_ty.is_bound() and rem_ty.binder.is_pi():
            tm = t.App(rem_conv[0], tm, rem_args[0])
            rem_ty = e.subst_expr([rem_args[0]], rem_ty.body)
            rem_conv = rem_conv[1:]
            rem_args = rem_args[1:]
        else:
            #In this case, something is wrong with the type
            #of f, and we simply blindly apply all the remaining
            #arguments.
            tm = t.App(rem_conv[0], tm, rem_args[0])
            rem_conv = rem_conv[1:]
            rem_args = rem_args[1:]
    return tm
        
