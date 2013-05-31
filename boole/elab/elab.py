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
import boole.core.context as context
import boole.core.goals as goals

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
        self.tele = e.nullctxt()
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

    def to_string(self):
        return "Mvar_{0!s}".format(self.name)

    def equals(self, expr):
        #There should only be one instance of
        #each meta-variable, so pointer equality is
        #sufficient
        return self is expr


class MvarSubst(e.SubstExpr):

    def __init__(self, exprs):
        e.SubstExpr.__init__(self, exprs)

    def visit_mvar(self, expr, *args, **kwargs):
        #return the actual object here, as we want values to
        #be propagated
        return expr


def subst_expr(exprs, expr):
    subster = MvarSubst(exprs)
    return subster.visit(expr, 0)


class MvarInfer(t.ExprInfer):
    """Infer the type and generate constraints for a term containing
    meta-variables. A constraint is created when a meta-variable is of
    type Bool.
    """
    
    def __init__(self):
        t.ExprInfer.__init__(self)
        self.check = MvarCheck
        self.sub = subst_expr

    def visit_mvar(self, expr, constrs, *args, **kwargs):
        sort = self.visit(expr.type, constrs, *args, **kwargs)
        if t.is_sort(sort):
            #If the meta-variable stands as evidence for a proposition
            #we add that proposition to the set of constraints, and
            #set the value of the meta-variable to Ev.
            if sort.is_bool():
                expr.set_val(e.Ev(expr.tele))
                constrs.append(goals.Goal(expr.tele, expr.type))
            return expr.type
        else:
            mess = 'The type of {0!s} is {1!s} '
            'which should be Type, Kind or Bool'\
                   .format(expr.type, sort)
            raise t.ExprTypeError(mess, expr)
        

class MvarCheck(t.ExprCheck):
    """Check the type and generate constraints for
    a term containing meta-variables
    """
    
    def __init__(self):
        t.ExprCheck.__init__(self)
        self.infer = MvarInfer

    def visit_mvar(self, expr, type, *args, **kwargs):
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False



def mk_meta(name, type):
    """Create a meta-variable with a fresh
    name and the given type.
    
    Arguments:
    - `name`: a string denoting the name of the Mvar
    - `type`: an expression denoting the type of the Mvar
    """
    fresh_name = meta_var_gen.get_name(name)
    return Mvar(fresh_name, type)

def mvar_infer(expr, type=None, ctxt=None):
    """Infer the type of an expression and return the pair
    (type, proof obligations) or raise an exception of type
    ExprTypeError.
    
    Arguments:
    - `expr`: an expression
    """
    if ctxt == None:
        ty_ctxt_name = meta_var_gen.get_name('_unif_ctxt')
        ty_ctxt = context.Context(ty_ctxt_name)
    else:
        ty_ctxt = ctxt
    prf_obl_name = meta_var_gen.get_name('_unif_goals')
    prf_obl = goals.empty_goals(prf_obl_name, ty_ctxt)
    #slight hack here: we compare pointers to avoid calling the
    # __eq__ method of type. There should only be one instance of
    # the None object, so pointer equality is valid.
    if type is None:
        ty = MvarInfer().visit(expr, prf_obl)
        return (ty, prf_obl)
    else:
        if MvarCheck().visit(expr, type, prf_obl):
            return (type, prf_obl)
        else:
            mess = "Expected {0!s} to be of type {1!s}"\
                   .format(expr, type)
            raise t.ExprTypeError(mess, expr)


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
            # mconv = mk_meta('{0!s}_conv'.format(mvar.name), \
            #                 e.Sub(rem_ty.dom, rem_ty.dom))
            #For now we generate the trivial evidence.
            #If more information is needed, we need to go through the whole
            #term to collect local information (variables), to add them
            #the evidence term
            mconv = e.trivial()
            tm = t.App(mconv, tm, mvar)
            rem_ty = subst_expr([mvar], rem_ty.body)
        elif rem_ty.is_bound() and rem_ty.binder.is_pi():
            tm = t.App(rem_conv[0], tm, rem_args[0])
            rem_ty = subst_expr([rem_args[0]], rem_ty.body)
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
        
