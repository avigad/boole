###############################################################################
#
# ineq_interface.py
#
# description: interface between Boole and the real inequality solver
#
###############################################################################

from boole.elab.terms import root_app_implicit, Real, Bool
import boole.core.typing as ty
import boole.interfaces.ineqs.classes as ineq

###############################################################################
#
# Translation exceptions
#
###############################################################################


class TranslationException(Exception):
    """Raised when there is an error in the translation
    """
    
    def __init__(self, *args):
        Exception.__init__(self, *args)


class NotFirstOrder(TranslationException):
    """Raised if the term is not a first-order term
    """
    
    def __init__(self, *args):
        """
        
        Arguments:
        - `*args`:
        """
        TranslationException.__init__(self, *args)
        self.args = args


class UndefinedConstant(TranslationException):
    """Raised if the constant is not recognized
    """
    
    def __init__(self, *args):
        """
        
        Arguments:
        - `*args`:
        """
        TranslationException.__init__(self, *args)
        self.args = args


class UnsupportedType(TranslationException):
    """Raised if the type of an expression is not supported
    in the translation.
    """
    
    def __init__(self, *args):
        TranslationException.__init__(self, *args)
        self.args = args


###############################################################################
#
# Helper functions to create first-order terms
#
###############################################################################


def is_first_order(expr):
    """Returns True if the expression
    is made of simply constants applied to arguments,
    excluding the implicit arguments.
    
    Arguments:
    - `expr`: an expression
    """
    r, args = root_app_implicit(expr)
    if not r.is_const():
        return False
    else:
        args = [is_first_order(a) for a in args]
        return all(args)


def add_tms(tm1, tm2):
    return ineq.Add_term([tm1, tm2])


def mul_tms(tm1, tm2):
    return ineq.Mul_term([tm1, tm2])


def lt_tms(tm1, tm2):
    return ineq.CompLT(tm1, tm2)


def conj_tms(tm1, tm2):
    """
    
    Arguments:
    - `tm1`:
    - `tm2`:
    """
    raise NotImplementedError()


def eq_tms(tm1, tm2):
    """
    
    Arguments:
    - `tm1`:
    - `tm2`:
    """
    raise NotImplementedError()

#Dictionary that maps Bool constant names to the function which constructs
# a term in the ineq datatype
fun_defs = {"+": add_tms, "*": mul_tms, "<": lt_tms,
            "&": conj_tms, "==": eq_tms}


def cast_const(cst):
    """Cast a constant to its value
    
    Arguments:
    - `cst`:
    """
    name = cst.name
    if name in fun_defs:
        return fun_defs[name]
    else:
        try:
            float(name)
            return lambda: ineq.Const(name)
        except ValueError:
            if cst.type is Real:
                return ineq.Var(name)
            else:
                raise UndefinedConstant("Undefined constant {0!s}"\
                                        .format(name))


def is_bool_or_real(expr):
    """checks that the expression has type bool
    or real, without generating obligations.
    
    Arguments:
    - `expr`:
    """
    t, _ = ty.infer(expr)
    return (t is Real) or (t is Bool)


def translate(expr):
    """Translate a Boole term to an Ineqs term
    
    Arguments:
    - `expr`:
    """
    if is_first_order(expr):
        if is_bool_or_real(expr):
            r, args = root_app_implicit(expr)
            args = [translate(a) for a in args]
            return cast_const(r)(*args)
        else:
            raise UnsupportedType()
    else:
        raise NotFirstOrder()


def translate_goal(hyps, prop):
    """Translate a set of hypotheses and a goal into
    a list of constraints
    
    Arguments:
    - `hyps`: a set of Boole terms of type bool
    - `prop`: a term of type bool
    """
    ineq_hyps = []
    for h in hyps:
        try:
            ineq_hyps.append(translate(h))
        except TranslationException:
            pass
    try:
        ineq_hyps.append(translate(prop).neg())
    except TranslationException:
        pass
