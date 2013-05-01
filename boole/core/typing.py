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
import constr as con


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
        if e1.is_kind or e2.is_kind:
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
        #self.check = ExprCheck()

    #TODO: add flag indicating whether type has been checked
    # for sortedness already.
    def visit_const(self, expr, *args, **kwargs):
        sort = self.visit(expr.type, *args, **kwargs)
        if is_sort(sort):
            return expr.type
        else:
            mess = 'The type of {0!s} is {1!s} which should\
            be Type, Kind or Bool'.format(expr, expr.type)
            raise ExprTypeError(mess, expr)

    def visit_db(self, expr, *args, **kwargs):
        raise ExprTypeError('Cannot determine the type of\
        a De Bruijn index', expr)

    def visit_type(self, expr, *args, **kwargs):
        return Kind()

    def visit_kind(self, expr, *args, **kwargs):
        raise ExprTypeError("Kind has no type.", expr)

    def visit_bool(self, expr, *args, **kwargs):
        return Type()

    def visit_bound(self, expr, *args, **kwargs):
        dom_ty = self.visit(expr.dom, *args, **kwargs)
        var = fresh_name.get_name(expr.binder.var)
        const = Const(var, expr.dom)
        open_expr = subst_expr([const], expr.expr)
        expr_ty = self.visit(open_expr, *args, **kwargs)
        if expr.binder.is_pi():
            if is_sort(dom_ty) and is_sort(expr_ty):
                #We wish for Pis to be at least in Type()
                return max_sort(max_sort(dom_ty, expr_ty), Type())
            else:
                if not is_sort(dom_ty):
                    mess = "The type of {0!s} must be a sort".format(expr.dom)
                    raise ExprTypeError(mess, expr)
                if not is_sort(expr_ty):
                    mess = "The type of {0!s} must be a sort".format(expr.expr)
                    raise ExprTypeError(mess, expr)
        elif expr.binder.is_abst():
            #Just need to check to see if the product is well-kinded:
            body_sort = self.visit(expr_ty, *args, **kwargs)
            if is_sort(dom_ty) and is_sort(body_sort):
                expr_ty = abstract_expr([var], expr_ty)
                return Pi(expr.binder.var, expr.dom, expr_ty)
            else:
                #In this case, it is necessarily the domain that
                # is ill-sorted. (the type of a type must be a sort,
                # if it exists)
                mess = "The type of {0!s} must be a sort".format(expr.dom)
                raise ExprTypeError(mess, expr)
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
            #We check that the types of the domain and
            #co-domain are equal using expr.conv as
            #evidence.
            eq_dom = Eq(fun_ty.dom, arg_ty)
            ExprCheck().visit(expr.conv, eq_dom, *args, **kwargs)
            return subst_expr([expr.arg], fun_ty.expr)
        else:
            raise ExprTypeError("Non functional application in\
            {0!s}".format(expr), expr)

    def visit_sig(self, expr, *args, **kwargs):
        return self.visit(expr.telescope, *args, **kwargs)

    def visit_tuple(self, expr, *args, **kwargs):
        if expr.type.is_sig():
            tele_ty = expr.type.telescope.types
            if len(expr.exprs) == len(tele_ty):
                # a bit risky: requires the expressions to be
                # free of "dangling" DB indices.
                for i, ty in enumerate(tele_ty):
                    ty_sub = subst_expr([expr.exprs], ty)
                    e = expr.exprs[i]
                    #we simply check that the term has exactly the right
                    #type (structurally). Any conversions need to be
                    #handled with Boxes.
                    if ExprCheck().visit(e, ty_sub, *args, **kwargs):
                        pass
                    else:
                        mess = "Expected {0!s} to be of type\
                        {1!s}".format(e, ty_sub)
                        raise ExprTypeError(mess, expr)
                return expr.type
            else:
                mess = "Length mismatch between\
                {0!s} and {1!s}".format(expr.exprs, expr.type.telescope)
                raise ExprTypeError(mess, expr)
        else:
            mess = "Expected a Sig type, obtained {0!s} instead"\
                   .format(expr.type)
            raise ExprTypeError(mess, expr)

    def visit_proj(self, expr, *args, **kwargs):
        arg_ty = self.visit(expr.expr, *args, **kwargs)
        if arg_ty.is_sig():
            if len(arg_ty) >= expr.index:
                projs = []
                for i in range(expr.index):
                    projs.append(Proj(i, expr.expr))
                ty_expr = arg_ty.telescope.types[expr.index]
                ty_expr = subst_expr(projs, ty_expr)
                return ty_expr
            else:
                mess = "Length mismatch: expected {0!s} to be of length\
                at least {1!s}".format(arg_ty, expr.index)
                raise ExprTypeError(mess, expr)
        else:
            mess = "Expected a Sig type, got {0!s} instead"\
                   .format(arg_ty)
            raise ExprTypeError(mess, expr)

    def visit_ev(self, expr, *args, **kwargs):
        #Check if the telescope is well-formed
        self.visit(expr.telescope, *args, **kwargs)
        return true()

    def visit_eq(self, expr, *args, **kwargs):
        #Just check that the lhs and rhs have some type
        self.visit(expr.lhs, *args, **kwargs)
        self.visit(expr.rhs, *args, **kwargs)
        return Bool()

    def visit_box(self, expr, *args, **kwargs):
        expr_ty = self.visit(expr.expr)
        eq_ty = Eq(expr.type, expr_ty)
        ExprCheck().visit(expr.conv, eq_ty, *args, **kwargs)
        ty_sort = self.visit(expr.type)
        if is_sort(ty_sort):
            return expr.type
        else:
            mess = "The type of {0!s} must be a sort.".format(expr.type)
            raise ExprTypeError(mess, expr)

    def visit_tele(self, expr, *args, **kwargs):
        open_tel = open_tele_with_fresh(expr)
        sorts = []
        for _, ty in open_tel:
            sorts.append(self.visit(ty, *args, **kwargs))
        #We wish for telescopes to be at least in Type()
        max_s = Type()
        for i, s in enumerate(sorts):
            if is_sort(s):
                max_s = max_sort(max_s, s)
            else:
                mess = "The type of {0!s} must be a\
                sort.".format(open_tel[i][1])
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
        #self.infer = ExprInfer()

    def visit_ev(self, expr, prop, constrs, *args, **kwargs):
        """Check that prop is a proposition, and return
        True, and add the constraint to the list of
        constraints if it is.
        
        Arguments:
        - `expr`: an expression
        - `prop`: an expression denoting a proposition
        - `constr`: a list of constraints
        """
        if self.visit(prop, Bool(), constrs, *args, **kwargs):
            constrs.append(con.Constr(expr.telescope, prop))
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_sig(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_tuple(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_proj(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False

    def visit_eq(self, expr, type, *args, **kwargs):
        """Check the syntactic equality of the inferred
        type of expr and type.
        
        Arguments:
        - `expr`: an expression
        - `type`: a type
        """
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
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
        expr_ty = ExprInfer().visit(expr, *args, **kwargs)
        if expr_ty.equals(type):
            return True
        else:
            return False


def infer(expr):
    """Infer the type of an expression and return the pair
    (type, proof obligations) or raise an exception of type
    ExprTypeError.
    
    Arguments:
    - `expr`: an expression
    """
    prf_obl = con.empty_obl()
    ty = ExprInfer().visit(expr, prf_obl)
    return (ty, prf_obl)



if __name__ == "__main__":

    nullctxt = Tele([], [])

    unit = sig()

    dummy = Const('_', unit)

    def app(fun, arg):
        return App(Ev(nullctxt), fun, arg)


    nat = Const('nat', Type())

    print nat, ":", nat.type

    print nat.equals(nat)

    typair = sig((dummy, Type()), (dummy, Type()))

    print typair
    print typair.equals(typair)
    
    natpair = sig((dummy, nat), (dummy, nat))

    print natpair
    print natpair.equals(natpair)
    
    plusty = pi(dummy, natpair, nat)

    print plusty
    print plusty.equals(plusty)

    plus = Const("plus", plusty)

    x = Const("x", nat)
    y = Const("y", nat)

    pair_x_y = Tuple([x, y], natpair)

    plus_x_y = app(plus, pair_x_y)
    
    ty, obl = infer(plus_x_y)
    
    print plus_x_y
    print ty
    print obl
    obl.solve_with('trivial')
    print obl.is_solved()
    
