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

meta_var_gen = vargen.VarGen()

##############################################################################
#
# The type of Pending substitution and abstraction operations.
# These are performed as the meta-variable is instantiated to a value
#
##############################################################################


class Pending(object):
    pass


class PendAbs(Pending):
    """A pending abstraction
    """
    
    def __init__(self, names, depth):
        """
        
        Arguments:
        - `names`:
        """
        Pending.__init__(self)
        self.names = names
        self.depth = depth
        
    def now(self, expr):
        """Evaluate the abstraction
        
        Arguments:
        - `expr`:
        """
        return MvarAbst(self.names).visit(expr, self.depth)


class PendSub(Pending):
    """A pending Substitution
    """
    
    def __init__(self, exprs, depth):
        """
        
        Arguments:
        - `names`:
        """
        Pending.__init__(self)
        self.exprs = exprs
        self.depth = depth

    def now(self, expr):
        """Evaluate the substitution
        
        Arguments:
        - `expr`:
        """
        return MvarSubst(self.exprs).visit(expr, self.depth)

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
    
    def __init__(self, name, type):
        """
        Same definition as for Const, without info fields
        and the additional information for:
        - potential value,
        - the conext in which it was created (to be used when finding
        a value)
        - the pending abstractions to be applied to the final value when found.
        """
        expr_base.Expr.__init__(self)
        self.name = name
        self.type = type
        self._value = None
        self.tele = nullctxt()
        self.pending = []

    def accept(self, visitor, *args, **kwargs):
        return visitor.visit_mvar(self, *args, **kwargs)

    def set_val(self, val):
        """Give a value to the meta-variable
        
        Arguments:
        - `val`: an expression
        """
        #update the info field to correspond to that
        #of the value: this makes mvar substitution
        #behave correctly with respect to info
        self.info = val.info
        self._value = val

    def to_string(self):
        return "?{0!s}".format(self.name)

    def equals(self, expr):
        #There should only be one instance of
        #each meta-variable, so we use pointer equality
        return self is expr

    def has_value(self):
        """Returns True if the expression has a value
        """
        return not (self._value is None)

    def clear(self):
        """Clear the value and the information of the
        meta-variable.
        """
        self.info = info.DefaultInfo()
        self._value = None

##############################################################################
#
# We re-write all the function defined on Expr
#  to handle the extra constructor
#
##############################################################################


class MvarAbst(e.AbstractExpr):
    
    def __init__(self, names):
        e.AbstractExpr.__init__(self, names)

    def visit_mvar(self, expr, depth):
        expr.tele = self.visit(expr.tele, depth)
        #Add the abstraction to the list of pending abstractions
        #to be performed when substituting a value
        # print "Abstracting over", self.names[0]
        # expr.pending.append(PendAbs(self.names, depth))
        #return the actual object here, as we want the value to
        #be propagated at each instance of the meta-variable
        return expr


class MvarSubst(e.SubstExpr):

    def __init__(self, exprs, is_open=None):
        e.SubstExpr.__init__(self, exprs, is_open=is_open)

    def visit_mvar(self, expr, depth):
        expr.tele = self.visit(expr.tele, depth)
        #We record the opens performed on an Mvar, and apply
        #them as it is substituted by it's value
        if self.is_open:
            names = [exp.name for exp in self.exprs]
            expr.pending.append(PendAbs(names, depth))
        # expr.pending.append(PendSub(self.exprs, depth))
        return expr


#rewrite code here from expr.py
def abstract_expr(vars, expr):
    abstractor = MvarAbst(vars)
    return abstractor.visit(expr, 0)


def subst_expr(exprs, expr, is_open=None):
    if is_open != None:
        subster = MvarSubst(exprs, is_open=is_open)
    else:
        subster = MvarSubst(exprs)
    return subster.visit(expr, 0)


def sub_in(exprs, vars, expr):
    return subst_expr(exprs, abstract_expr(vars, expr))


def open_expr(var, typ, expr, checked=None):
    if checked == None:
        const = e.Const(var, typ, checked=True)
    else:
        const = e.Const(var, typ, checked=checked)
    return subst_expr([const], expr, is_open=True)


def open_bound_fresh(expr, checked=None):
    var = e.fresh_name.get_name(expr.binder.var)
    return (var, open_expr(var, expr.dom, expr.body, checked=checked))


def mvar_open_expr(var, typ, expr):
    mvar = Mvar(var, typ)
    return subst_expr([mvar], expr)


def mvar_open_bound_fresh(expr):
    var = meta_var_gen.get_name(expr.binder.var)
    return (var, mvar_open_expr(var, expr.dom, expr.body))


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
        opened_ty[i] = subst_expr(consts, opened_ty[i], is_open=True)
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


def root_pi(expr):
    """Returns the pair (r, [an,..,a0])
    such that expr = Pi(a0, Pi(.. Pi(an, r)..)
    
    Arguments:
    - `expr`: an expression
    """
    root = expr
    args = []
    while root.is_pi():
        args.append(root.dom)
        _, root = open_bound_fresh(root)
    return (root, args)


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
    ty = MvarInfer().visit(expr, prf_obl)
    return (ty, prf_obl)


class MvarParBeta(conv.ParBeta):
    
    def __init__(self):
        """Take as argument the substitution function,
        the opening and abstraction functions.
        """
        conv.ParBeta.__init__(self)
        self.subst = subst_expr
        self.open_expr = open_bound_fresh
        self.open_tele = open_tele_fresh
        self.abst = abstract_expr

    def visit_mvar(self, expr, *args, **kwargs):
        return expr


def par_beta(expr):
    return MvarParBeta().visit(expr)


###############################################################################
#
# Utility functions for manipulating a term with mvars.
#
###############################################################################

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
        
    def visit_const(self, expr):
        ty = self.visit(expr.type)
        return e.Const(expr.name, ty)

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
        self.abst = abstract_expr
        self.open_fresh = open_bound_fresh
        
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
            #For now we generate the trivial evidence.
            #If more information is needed, we need to go through the whole
            #term to collect local information (variables), to add them
            #the evidence term
            mcast = trivial
            tm = t.App(mcast, tm, mvar)
            rem_ty = subst_expr([mvar], rem_ty.body)
    else:
        while len(rem_args) != 0:
            if rem_ty.is_pi()\
               and rem_ty.info.implicit:
                mvar = mk_meta(rem_ty.binder.var, rem_ty.dom)
                mcast = trivial
                tm = t.App(mcast, tm, mvar)
                rem_ty = subst_expr([mvar], rem_ty.body)
            elif rem_ty.is_pi():
                tm = t.App(rem_cast[0], tm, rem_args[0])
                rem_ty = subst_expr([rem_args[0]], rem_ty.body)
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
    """
    if var.is_const():
        codom_abs = abstract_expr([var.name], codom)
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


trivial = e.Ev(nullctxt())
