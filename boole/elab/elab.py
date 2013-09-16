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
import boole.core.info as info
import boole.core.goals as goals
import boole.core.conv as conv


###############################################################################
#
# Utility functions for manipulating a term with mvars.
#
###############################################################################


def mvar_open_expr(var, typ, expr):
    mvar = e.Mvar(var, typ)
    return e.subst_expr([mvar], expr)


def mvar_open_bound_fresh(expr):
    var = meta_var_gen.get_name(expr.binder.var)
    return (var, mvar_open_expr(var, expr.dom, expr.body))


def mk_meta(name, type):
    """Create a meta-variable with a fresh
    name and the given type.
    
    Arguments:
    - `name`: a string denoting the name of the Mvar
    - `type`: an expression denoting the type of the Mvar
    """
    fresh_name = meta_var_gen.get_name(name)
    return e.Mvar(fresh_name, type)


def mvar_infer(expr, ctxt=None):
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
    ty = t.ExprInfer().visit(expr, prf_obl)
    return (ty, prf_obl)


class SubMvar(e.ExprVisitor):
    """Replace all meta-variables by their
    value in a term.
    
    Arguments:
    - `undef`: if this flag is set to True,
    fail on unresolved meta-vars.
    """
    
    def __init__(self, undef=None):
        e.ExprVisitor.__init__(self)
        self.undef = undef

# TODO (JDA): I had to modify the third line below by adding the value.
# Is this right? What about the instances of Const with true and false below?
    def visit_const(self, expr):
        ty = self.visit(expr.type)
        return e.Const(expr.name, ty, value=expr.value)

    def visit_db(self, expr):
        return expr

    def visit_type(self, expr):
        return expr

    def visit_kind(self, expr):
        return expr

    def visit_bool(self, expr):
        return expr

    def visit_bound(self, expr):
        dom = self.visit(expr.dom)
        body = self.visit(expr.body)
        return e.Bound(expr.binder, dom, body)

    def visit_app(self, expr):
        conv = self.visit(expr.conv)
        fun = self.visit(expr.fun)
        arg = self.visit(expr.arg)
        return e.App(conv, fun, arg)

    def visit_pair(self, expr):
        fst = self.visit(expr.fst)
        snd = self.visit(expr.snd)
        type = self.visit(expr.type)
        return e.Pair(fst, snd, type)

    def visit_fst(self, expr):
        return e.Fst(self.visit(expr.expr))

    def visit_snd(self, expr):
        return e.Snd(self.visit(expr.expr))

    def visit_ev(self, expr):
        return e.Ev(self.visit(expr.tele))

    def visit_sub(self, expr):
        lhs = self.visit(expr.lhs)
        rhs = self.visit(expr.rhs)
        return e.Sub(lhs, rhs)

    def visit_box(self, expr):
        conv = self.visit(expr.conv)
        expr1 = self.visit(expr.expr)
        type = self.visit(expr.type)
        return e.Box(conv, expr1, type)

    def visit_tele(self, expr):
        types = [self.visit(t) for t in expr.types]
        return e.Tele(expr.vars, types)

    def visit_mvar(self, expr):
        if expr.has_value():
            sub_val = self.visit(expr._value)
            if self.undef is None:
                #we are in this case if we are still solving
                #constraints: the instantiations should not be applied
                #yet.
                pass
            else:
                for p in expr.pending:
                    sub_val = p.now(sub_val)
            return sub_val
        else:
            if self.undef is None:
                return expr
            else:
                typ = self.visit(expr.type)
                mess = "Cannot find a value for {0!s}:{1!s}"\
                       .format(expr, typ)
                raise e.ExprError(mess, expr)

    @info.same_info
    def visit(self, expr, *args, **kwargs):
        return expr.accept(self, *args, **kwargs)


def sub_mvar(expr, undef=None):
    """Replace all meta-variables by their
    value in a term.
    
    Arguments:
    - `undef`: if this flag is set to True,
    fail on unresolved meta-vars.
    """
    return SubMvar(undef=undef).visit(expr)


class MvarIsPresent(e.ExprVisitor):
    """Determine if a meta-variable name is present in a term.
    """
    
    def __init__(self, name=None):
        e.ExprVisitor.__init__(self)
        self.name = name
        
    def visit_const(self, expr):
        pass

    def visit_db(self, expr):
        pass

    def visit_type(self, expr):
        pass

    def visit_kind(self, expr):
        pass

    def visit_bool(self, expr):
        return expr

    def visit_bound(self, expr):
        self.visit(expr.dom)
        self.visit(expr.body)

    def visit_app(self, expr):
        self.visit(expr.conv)
        self.visit(expr.fun)
        self.visit(expr.arg)

    def visit_pair(self, expr):
        self.visit(expr.fst)
        self.visit(expr.snd)
        self.visit(expr.type)

    def visit_fst(self, expr):
        self.visit(expr.expr)

    def visit_snd(self, expr):
        self.visit(expr.expr)

    def visit_ev(self, expr):
        self.visit(expr.tele)

    def visit_sub(self, expr):
        self.visit(expr.lhs)
        self.visit(expr.rhs)

    def visit_box(self, expr):
        self.visit(expr.conv)
        self.visit(expr.expr)
        self.visit(expr.type)

    def visit_tele(self, expr):
        for t in expr.types:
            self.visit(t)

    def visit_mvar(self, expr):
        if self.name != None:
            if expr.name == self.name:
                return True
        else:
            return True


def mvar_is_present(expr, mvar=None):
    if MvarIsPresent(name=mvar.name).visit(expr):
        return True
    else:
        return False


meta_var_gen = vargen.VarGen()


###############################################################################
#
# utility functions for elaborating top-level expressions
#
###############################################################################


class Enrich(e.ExprVisitor):
    """Enrich the evidence terms with a new
    hypothesis
    """
    
    def __init__(self, name, prop):
        e.ExprVisitor.__init__(self)
        self.name = name
        self.prop = prop
        self.abst = e.abstract_expr
        self.open_fresh = e.open_bound_fresh
        
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
        var, open_expr = self.open_fresh(expr)
        new_open_expr = self.visit(open_expr)
        dom = self.visit(expr.dom)
        return e.Bound(expr.binder, dom, self.abst([var], new_open_expr))

    def visit_app(self, expr, *args, **kwargs):
        ev = self.visit(expr.conv)
        fun = self.visit(expr.fun)
        arg = self.visit(expr.arg)
        return e.App(ev, fun, arg)

    def visit_pair(self, expr, *args, **kwargs):
        fst = self.visit(expr.fst)
        snd = self.visit(expr.snd)
        ty = self.visit(expr.type)
        return e.Pair(fst, snd, ty)

    def visit_fst(self, expr, *args, **kwargs):
        return e.Fst(self.visit(expr.expr))

    def visit_snd(self, expr, *args, **kwargs):
        return e.Snd(self.visit(expr.expr))

    #We assume that elements of a telescope do not
    #need to be enriched
    def visit_ev(self, expr, *args, **kwargs):
        vars = [self.name] + expr.tele.vars
        types = [self.prop] + expr.tele.types
        return e.Ev(e.Tele(vars, types))

    def visit_sub(self, expr, *args, **kwargs):
        lhs = self.visit(expr.lhs)
        rhs = self.visit(expr.rhs)
        return e.Sub(lhs, rhs)

    def visit_box(self, expr, *args, **kwargs):
        ev = self.visit(expr.conv)
        exp = self.visit(expr.expr)
        type = self.visit(expr.type)
        return e.Box(ev, exp, type)

    def visit_mvar(self, expr):
        vars = [self.name] + expr.tele.vars
        types = [self.prop] + expr.tele.types
        expr.tele = e.Tele(vars, types)
        return expr

    def visit_tele(self, expr):
        raise NotImplementedError()

    @info.same_info
    def visit(self, expr, *args, **kwargs):
        """Call the appropriate method of self
        on expr depending on its form.
        
        Arguments:
        - `expr`: an expression
        """
        return expr.accept(self, *args, **kwargs)


def enrich(name, prop, expr):
    """Enrich the telescopes of the
    evidence terms of expr with the hypothesis
    prop with name name.
    
    Arguments:
    - `name`:
    - `prop`:
    - `expr`:
    """
    return Enrich(name, prop).visit(expr)


def app_expr(f, f_ty, cast, args):
    """Applies a function to a list of
    arguments, some of which are implicit.
    
    Arguments:
    - `f`: an expression denoting the function
    - `f_ty`: the function type
    - `cast`: list of evidence terms for the type conversions
    of each argument
    - `args`: a list of arguments
    """
    tm = f
    rem_args = args
    rem_cast = cast
    rem_ty = f_ty

    #TODO: This is a bit of a hack. We need "maximally inserted arguments"
    #as in Coq to do this cleanly
    if len(args) == 0:
        while rem_ty.is_pi()\
              and rem_ty.info.implicit:
            mvar = mk_meta(rem_ty.binder.var, rem_ty.dom)
            #At this point we give the trivial evidence.
            #after the term is created, we go through the whole
            #term to collect local information (variables) and to add them
            #the evidence term
            mcast = trivial()
            tm = t.App(mcast, tm, mvar)
            rem_ty = e.subst_expr([mvar], rem_ty.body)
    else:
        while len(rem_args) != 0:
            if rem_ty.is_pi()\
               and rem_ty.info.implicit:
                mvar = mk_meta(rem_ty.binder.var, rem_ty.dom)
                mcast = trivial()
                tm = t.App(mcast, tm, mvar)
                rem_ty = e.subst_expr([mvar], rem_ty.body)
            elif rem_ty.is_pi():
                tm = t.App(rem_cast[0], tm, rem_args[0])
                rem_ty = e.subst_expr([rem_args[0]], rem_ty.body)
                rem_cast = rem_cast[1:]
                rem_args = rem_args[1:]
            else:
                #In this case, something is wrong with the type
                #of f, and we simply blindly apply all the remaining
                #arguments.
                tm = t.App(rem_cast[0], tm, rem_args[0])
                rem_cast = rem_cast[1:]
                rem_args = rem_args[1:]
    return tm


def pi(var, codom, impl=None):
    """Create the term
    Pi x:A.B from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `codom`: an expression possibly containing var
    - `impl`: a flag which notes if the argument is implicit.
    """
    if var.is_const():
        codom_abs = e.abstract_expr([var.name], codom)
        ret = e.Bound(e.Pi(var.name), var.type, codom_abs)
        if impl:
            ret.info['implicit'] = True
        return ret
    else:
        mess = "Expected {0!s} to be a constant".format(var)
        raise e.ExprError(mess, var)


def abst(var, body):
    """Create the term
    lambda x:A.t from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `body`: an expression possibly containing var
    """
    if var.is_const():
        ty, _ = mvar_infer(var.type)
        if ty.equals(e.Bool()):
            body = enrich(var.name, var.type, body)
        else:
            pass
        body_abs = e.abstract_expr([var.name], body)
        return e.Bound(e.Abst(var.name), var.type, body_abs)
    else:
        print var.__class__
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
        prop_abs = e.abstract_expr([var.name], prop)
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
        prop_abs = e.abstract_expr([var.name], prop)
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
        codom_abs = e.abstract_expr([var.name], codom)
        return e.Bound(e.Sig(var.name), var.type, codom_abs)
    else:
        mess = "Expected {0!s} to be a constant".format(var)
        raise e.ExprError(mess, var)


def trivial():
    """The empty evidence term
    """
    return e.Ev(e.nullctxt())
