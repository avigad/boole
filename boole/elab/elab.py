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

##############################################################################
#
# We add a new constructor to the Expr class: it represents meta-variables
# which can be given a value when determined to be equal to an expression
# by unification.
#
##############################################################################


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
        self.tele = nullctxt()
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
        #update the info field to correspond to that
        #of the value: this makes mvar substitution
        #behave correctly with respect to info
        self.info.update(val.info)

    def to_string(self):
        return "?{0!s}".format(self.name)

    def equals(self, expr):
        #There should only be one instance of
        #each meta-variable, so pointer equality is
        #sufficient
        return self is expr

##############################################################################
#
# We re-write all the function defined on Expr
#  to handle the extra constructor
#
##############################################################################


class MvarAbst(e.AbstractExpr):
    
    def __init__(self, names):
        e.AbstractExpr.__init__(self, names)

    def visit_mvar(self, expr, *args, **kwargs):
        #return the actual object here, as we want values to
        #be propagated
        if not (expr.value is None):
            expr.value = self.visit(expr.value, *args, **kwargs)
            return expr
        else:
            return expr


class MvarSubst(e.SubstExpr):

    def __init__(self, exprs):
        e.SubstExpr.__init__(self, exprs)

    def visit_mvar(self, expr, *args, **kwargs):
        #return the actual object here, as we want values to
        #be propagated
        if not (expr.value is None):
            expr.value = self.visit(expr.value, *args, **kwargs)
            return expr
        else:
            return expr


#A bit of code duplication here from expr.py
def abstract_expr(vars, expr):
    abstractor = MvarAbst(vars)
    return abstractor.visit(expr, 0)


def subst_expr(exprs, expr):
    subster = MvarSubst(exprs)
    return subster.visit(expr, 0)


def open_expr(var, typ, expr, checked=None):
    if checked == None:
        const = e.Const(var, typ, checked=True)
    else:
        const = e.Const(var, typ, checked=checked)
    return subst_expr([const], expr)


def open_bound_fresh(expr, checked=None):
    var = e.fresh_name.get_name(expr.binder.var)
    return (var, open_expr(var, expr.dom, expr.body, checked=checked))


def open_tele(tele, vars, checked=False):
    """Takes a telescope and returns a list of pairs
    (constant, type) where the subsequent types may depend
    on the constant.
    
    Arguments:
    - `tele`:
    """
    opened_ty = tele.types
    consts = []
    for i in range(0, tele.len):
        opened_ty[i] = subst_expr(consts, opened_ty[i])
        x = e.Const(vars[i], opened_ty[i], checked=checked)
        consts.append(x)
    return (consts, opened_ty)


def open_tele_fresh(tele, checked=False):
    """Open a telescope with fresh variables
    
    Arguments:
    - `tele`: a telescope
    """
    fr_vars = [e.fresh_name.get_name(v) for v in tele.vars]
    return open_tele(tele, fr_vars, checked=checked)


class MvarInfer(t.ExprInfer):
    """Infer the type and generate constraints for a term containing
    meta-variables. A constraint is created when a meta-variable is of
    type Bool.
    """
    
    def __init__(self):
        t.ExprInfer.__init__(self)
        self.check = MvarCheck
        self.sub = subst_expr
        self.abst = abstract_expr
        self.open_fresh = open_bound_fresh
        self.open_tele_fresh = open_tele_fresh

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
            mess = "The type of {0!s} is {1!s} "
            "which should be Type, Kind or Bool"\
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
            #For now we generate the trivial evidence.
            #If more information is needed, we need to go through the whole
            #term to collect local information (variables), to add them
            #the evidence term
            mconv = trivial()
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


def pi(*args):
    """Create the term
    Pi x:A.B from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `codom`: an expression possibly containing var
    """
    if len(args) == 2:
        var = args[0]
        codom = args[1]
        if var.is_const():
            codom_abs = abstract_expr([var.name], codom)
            return e.Bound(e.Pi(var.name), var.type, codom_abs)
        else:
            mess = "Expected {0!s} to be a constant".format(var)
            raise e.ExprError(mess, var)
    elif len(args) == 3:
        name = args[0]
        dom = args[1]
        codom = args[2]
        return e.Bound(e.Pi(name), dom, codom)
    else:
        raise Exception("Wrong number of arguments!")


def abst(var, body):
    """Create the term
    lambda x:A.t from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `body`: an expression possibly containing var
    """
    if var.is_const():
        body_abs = abstract_expr([var.name], body)
        return e.Bound(e.Abst(var.name), var.type, body_abs)
    else:
        mess = "Expected {0!s} to be a constant".format(var)
        raise e.ExprError(mess, var)


def forall(var, prop):
    """Create the term
    forall x:A.t from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `prop`: an expression possibly containing var
    """
    if var.is_const():
        prop_abs = abstract_expr([var.name], prop)
        return e.Bound(e.Forall(var.name), var.type, prop_abs)
    else:
        mess = "Expected {0!s} to be a constant".format(var)
        raise e.ExprError(mess, var)


def exists(var, prop):
    """Create the term
    exists x:A.t from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `prop`: an expression possibly containing var
    """
    if var.is_const():
        prop_abs = abstract_expr([var.name], prop)
        return e.Bound(e.Exists(var.name), var.type, prop_abs)
    else:
        mess = "Expected {0!s} to be a constant".format(var)
        raise e.ExprError(mess, var)


def sig(var, codom):
    """Create the term
    Sig x:A.B from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `codom`: an expression possibly containing var
    """
    if var.is_const():
        codom_abs = abstract_expr([var.name], codom)
        return e.Bound(e.Sig(var.name), var.type, codom_abs)
    else:
        mess = "Expected {0!s} to be a constant".format(var)
        raise e.ExprError(mess, var)


def true():
    """The true constant.
    """
    return e.Const('true', e.Bool())


def false():
    """The false constant.
    """
    return e.Const('false', e.Bool())


def nullctxt():
    """The empty telescope
    """
    return e.Tele([], [])


def trivial():
    """The trivial evidence term
    """
    return e.Ev(nullctxt())
