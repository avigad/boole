##############################################################################
#
# typing.py
#
# description: the type inference and constraint generation in Boole.
#
#
# Authors:
# Cody Roux
#
#
##############################################################################

from expr import *
import goals
import context
import tactics


def is_sort(expr):
    """Returns True if the expression is a sort.
    
    Arguments:
    - `expr`:
    """
    return expr.is_type() or expr.is_kind() or expr.is_bool()


def max_sort(e1, e2):
    """Returns the greatest sort using the order
    Bool < Type < Kind
    
    Arguments:
    - `e1, e2`: expressions
    """
    if is_sort(e1) and is_sort(e2):
        if e1.is_kind() or e2.is_kind():
            return Kind()
        elif e1.is_bool():
            return e2
        elif e2.is_bool():
            return e1
        else:
            assert(e1.is_type() and e2.is_type())
            return Type()
    else:
        if not is_sort(e1):
            raise ExprError("Expected {0!s} be a sort".format(e1), e1)
        if not is_sort(e2):
            raise ExprError("Expected {0!s} be a sort".format(e2), e2)


class ExprTypeError(Exception):
    """Errors raised by the typing process
    """
    
    def __init__(self, mess, expr):
        """
        
        Arguments:
        - `mess`:
        - `expr`:
        """
        Exception.__init__(self)
        self.mess = mess
        self.expr = expr
        print "Type error in the expression {0!s}:\n{1!s}"\
              .format(expr, mess)


class ExprInfer(ExprVisitor):
    """Infer the type of an expression. Mutually recursive with
    ExprCheck. Returns an expression or raises
    ExprTypeError.

    Arguments:
    - `expr`: an expression
    - `constrs`: a list of constraints
    """
    
    def __init__(self):
        ExprVisitor.__init__(self)
        self.check = ExprCheck
        self.sub = subst_expr
        self.abst = abstract_expr
        self.open_fresh = open_bound_fresh
        self.open_tele_fresh = open_tele_fresh

    def visit_const(self, expr, *args, **kwargs):
        if expr.info.checked:
            return expr.type
        else:
            sort = self.visit(expr.type, *args, **kwargs)
            if is_sort(sort):
                return expr.type
            else:
                mess = "The type of {0!s} is {1!s}\n"\
                " which should be Type, Kind or Bool"\
                       .format(expr.type, sort)
                raise ExprTypeError(mess, expr)

    def visit_db(self, expr, *args, **kwargs):
        raise ExprTypeError('Cannot determine the type of a De Bruijn index', \
                            expr)

    def visit_type(self, expr, *args, **kwargs):
        return Kind()

    def visit_kind(self, expr, *args, **kwargs):
        raise ExprTypeError("Kind has no type.", expr)

    def visit_bool(self, expr, *args, **kwargs):
        return Type()

    def visit_bound(self, expr, *args, **kwargs):
        dom_ty = self.visit(expr.dom, *args, **kwargs)
        #check that the domain is well-kinded
        if is_sort(dom_ty):
            pass
        else:
            mess = "The term {0!s} has type {1!s} which must be a sort\
            or have as type a sort".format(expr.dom, dom_ty)
            raise ExprTypeError(mess, expr)
        #substitute a fresh constant in the body of the binder
        var, open_expr = self.open_fresh(expr)
        #since the term may contain meta-variables, we close the open
        #expression to 'mark' the meta-variables with the closing operation
        self.abst([var], open_expr)
        #compute the type of the resulting expression
        expr_ty = self.visit(open_expr, *args, **kwargs)
        #Infer the type for each different binder
        if expr.binder.is_pi() or expr.binder.is_sig():
            if is_sort(expr_ty):
                #We force Pis and Sigmas to be at least in Type()
                return max_sort(max_sort(dom_ty, expr_ty), Type())
            else:
                mess = "The type of {0!s} is {1!s} which must be a sort"\
                       .format(open_expr, expr_ty)
                raise ExprTypeError(mess, expr)
        elif expr.binder.is_abst():
            #Just need to check to see if the product is well-kinded:
            #for example: abs(x:Bool, Type) is not well-kinded
            self.visit(expr_ty, *args, **kwargs)
            expr_ty = self.abst([var], expr_ty)
            return Bound(Pi(expr.binder.var), expr.dom, expr_ty)
        else:
            assert(expr.binder.is_forall() or expr.binder.is_exists())
            if Bool().equals(expr_ty):
                return Bool()
            else:
                mess = "The type of {0!s} must be Bool".format(open_expr)
                raise ExprTypeError(mess, expr)

    def visit_app(self, expr, *args, **kwargs):
        fun_ty = self.visit(expr.fun, *args, **kwargs)
        arg_ty = self.visit(expr.arg, *args, **kwargs)
        if fun_ty.is_bound() and fun_ty.binder.is_pi():
            #We check that the types of the argument is
            #a subtype of the domain using expr.conv as
            #evidence.
            sub_dom = Sub(arg_ty, fun_ty.dom)
            self.check().visit(expr.conv, sub_dom, *args, **kwargs)
            return self.sub([expr.arg], fun_ty.body)
        else:
            raise ExprTypeError("Non functional application in {0!s}"\
                                .format(expr), expr)

    def visit_pair(self, expr, *args, **kwargs):
        if expr.type.is_bound() and expr.type.binder.is_sig():
            self.check().visit(expr.fst, expr.type.dom, *args, **kwargs)
            codom = self.sub([expr.fst], expr.type.body)
            self.check().visit(expr.snd, codom, *args, **kwargs)
            return expr.type
        else:
            mess = "Expected a Sig type, obtained {0!s} instead"\
                   .format(expr.type)
            raise ExprTypeError(mess, expr)

    def visit_fst(self, expr, *args, **kwargs):
        arg_ty = self.visit(expr.expr, *args, **kwargs)
        if arg_ty.is_bound() and arg_ty.binder.is_sig():
            return arg_ty.dom
        else:
            mess = "Expected a Sig type, got {0!s} instead"\
                   .format(arg_ty)
            raise ExprTypeError(mess, expr)

    def visit_snd(self, expr, *args, **kwargs):
        arg_ty = self.visit(expr.expr, *args, **kwargs)
        if arg_ty.is_bound() and arg_ty.binder.is_sig():
            fst_proj = Fst(expr.expr)
            return self.sub([fst_proj], arg_ty.body)
        else:
            mess = "Expected a Sig type, got {0!s} instead"\
                   .format(arg_ty)
            raise ExprTypeError(mess, expr)

    def visit_ev(self, expr, *args, **kwargs):
        #Check if the telescope is well-formed
        self.visit(expr.tele, *args, **kwargs)
        #This is a bit ad-hoc, as it relies on
        #terms being compared by name only.
        return Const('true', Bool(), is_prop=True)

    def visit_sub(self, expr, *args, **kwargs):
        #Just check that the lhs and rhs have some type
        self.visit(expr.lhs, *args, **kwargs)
        self.visit(expr.rhs, *args, **kwargs)
        return Bool()

    def visit_box(self, expr, *args, **kwargs):
        expr_ty = self.visit(expr.expr, *args, **kwargs)
        sub_ty = Sub(expr_ty, expr.type)
        self.check().visit(expr.conv, sub_ty, *args, **kwargs)
        ty_sort = self.visit(expr.type, *args, **kwargs)
        if is_sort(ty_sort):
            return expr.type
        else:
            mess = "The type of {0!s} must be a sort.".format(expr.type)
            raise ExprTypeError(mess, expr)

    def visit_tele(self, expr, *args, **kwargs):
        #There is no need to check that the constants
        # are well-kinded as this will be done when
        # checking each type in the telescope.
        open_tel = self.open_tele_fresh(expr, checked=True)[1]
        sorts = []
        for ty in open_tel:
            sorts.append(self.visit(ty, *args, **kwargs))
        #We wish for telescopes to be at least in Type()
        max_s = Type()
        for i, s in enumerate(sorts):
            if is_sort(s):
                max_s = max_sort(max_s, s)
            else:
                mess = "The type of {0!s} must be a\
                sort.".format(open_tel[i])
                raise ExprTypeError(mess, expr)
        return max_s


class ExprCheck(ExprVisitor):
    """Check that a term has a given type.
    Mutually recursive with ExprInfer. Returns a Boolean
    or raises ExprTypeError.

    Arguments:
    - `expr`: an expression
    - `type`: a type
    - `constrs`: a list of constraints
    """
    
    def __init__(self):
        ExprVisitor.__init__(self)
        self.infer = ExprInfer

    def visit_ev(self, expr, prop, constrs, *args, **kwargs):
        """Check that prop is a proposition, and return
        True, and add the constraint to the list of
        constraints if it is.
        
        Arguments:
        - `expr`: an expression
        - `prop`: an expression denoting a proposition
        - `constr`: a list of constraints
        """
        #check that expr is well-formed
        self.infer().visit(expr, constrs, *args, **kwargs)
        if self.visit(prop, Bool(), constrs, *args, **kwargs):
            constrs.append(goals.Goal(expr.tele, prop))
            return True
        else:
            return False

    def visit_const(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_type(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_kind(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        - `**kwargs`:
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_bool(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_db(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_bound(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_app(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_pair(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_fst(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_snd(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_sub(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_box(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        - `**kwargs`:
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_tele(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = self.infer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False


def infer(expr, type=None, ctxt=None):
    """Infer the type of an expression and return the pair
    (type, proof obligations) or raise an exception of type
    ExprTypeError.
    
    Arguments:
    - `expr`: an expression
    """
    if ctxt == None:
        ty_ctxt_name = fresh_name.get_name('_ty_ctxt')
        ty_ctxt = context.Context(ty_ctxt_name)
    else:
        ty_ctxt = ctxt
    prf_obl_name = fresh_name.get_name('_ty_goals')
    prf_obl = goals.empty_goals(prf_obl_name, ty_ctxt)
    #slight hack here: we compare pointers to avoid calling the
    # __eq__ method of type which may be overloaded.
    # There should only be one instance of
    # the None object, so pointer equality is valid.
    if type is None:
        ty = ExprInfer().visit(expr, prf_obl)
        return (ty, prf_obl)
    else:
        if ExprCheck().visit(expr, type, prf_obl):
            return (type, prf_obl)
        else:
            mess = "Expected {0!s} to be of type {1!s}"\
                   .format(expr, type)
            raise ExprTypeError(mess, expr)
