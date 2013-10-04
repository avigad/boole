#############################################################################
#
# value.py
#
# description: a class to hold semantic objects, that is, values of
# interpreted constants, and values assigned by models
#
#
# Authors:
# Jeremy Avigad
#
#
##############################################################################

import boole.core.expr as e


class NoValue(Exception):
    """Raised when trying to evaluate a value-less constant or
    built-in construct.
    """
    
    def __init__(self, expr):
        mess = "The expression {0!s} has no value".format(expr)
        Exception.__init__(self, mess)
        self.expr = expr


class Value(object):
    """The class of semantic values
    
    Arguments:
    - `pyval`: a python value
    - `desc`: a boole expression that, together with the pyval,
    gives a description of the object in question
    - `is_num`: a boolean, indicates that pyval supports numeric operations
    """

    def __init__(self, pyval=None, desc=None, is_num=False):
        """Creats the object
        """
        self.pyval = pyval
        self.desc = desc
        self._is_num = is_num
        
    # TODO: what should the string method do? For now, just take the Python
    # object
    def __str__(self):
        return str(self.pyval)
    
    def is_num(self):
        return self._is_num
    

class Model(object):
    """The class of models, which allow interpretation of
    expressions by giving a value to constants.
    """
    
    def __init__(self, eqns, val_dict):
        """
        
        Arguments:
        - `eqns`: a map from names to equations defining the model
        - `val_dict`: a dictionary mapping constant names to their value
        """
        self.eqns = eqns
        self.vals = val_dict
        
    def __str__(self):
        """Print the equational definitions
        """
        s_eqns = [str(self.eqns[e]) for e in self.eqns]
        return "[" + ", ".join(s_eqns) + "]"
        
    def add_to_ctxt(self, context):
        """Add the equations in the model to the local
        context hypotheses.
        
        Arguments:
        - `context`: a boole context
        """
        context.hyps.update(self.eqns)


BoolVal = Value([True, False], 'Bool')


class ExprValue(e.ExprVisitor):
    """Return the value of an expression.
    """
    
    def __init__(self, strict=False):
        e.ExprVisitor.__init__(self)
        self.strict = strict

    def visit_const(self, expr, model=None, bindings=None):
        if expr.value:
            return expr.value.pyval
        else:
            try:
                v = model.vals[expr.name]
                return v.pyval
            except KeyError:
                if self.strict:
                    raise NoValue(expr)
                else:
                    return None

    def visit_db(self, expr, model=None):
        if self.strict:
            raise NoValue(expr)
        else:
            return None


    def visit_type(self, expr, model=None):
        if self.strict:
            raise NoValue(expr)
        else:
            return None

    def visit_kind(self, expr, model=None):
        if self.strict:
            raise NoValue(expr)
        else:
            return None

    def visit_bool(self, expr, model=None):
        return BoolVal

    def visit_bound(self, expr, model=None):
        raise NotImplementedError()

    def visit_app(self, expr, model=None):
        #evaluate all the arguments at once.
        #Include the implicit arguments.
        f, args = e.root_app(expr)
        f_val = self.visit(f, model)
        args_val = [self.visit(a, model) for a in args]
        return f_val(*args_val)

    def visit_pair(self, expr, model=None):
        fst_val = self.visit(expr.fst, model)
        snd_val = self.visit(expr.snd, model)
        return (fst_val, snd_val)

    def visit_fst(self, expr, model=None):
        pair_val = self.visit(expr.expr, model)
        return pair_val[0]

    def visit_snd(self, expr, model=None):
        pair_val = self.visit(expr.expr, model)
        return pair_val[1]

    def visit_ev(self, expr, model=None):
        return ()

    def visit_sub(self, expr, model=None):
        def sub_val(v1, v2): 
            if isinstance(v1, bool) and isinstance(v2, bool):
                return (not v1) or v2
            else:
                return v1 == v2
        return sub_val

    def visit_box(self, expr, model=None):
        return self.visit(expr.expr, model)

    def visit_tele(self, expr, model=None):
        raise NotImplementedError()

    def visit_mvar(self, expr, model=None):
        if self.strict:
            raise NoValue(expr)
        else:
            return None


###############################################################################
#
# Semantics of built-in operations
#
###############################################################################

def add_real_fun(x, y):
    return x + y


def mul_real_fun(x, y):
    return x * y


def minus_real_fun(x, y):
    return x - y


def divide_real_fun(x, y):
    return float(x) / y


def power_fun(x, y):
    return x ** y


def uminus_real_fun(x):
    return -x


def abs_real_fun(x):
    return abs(x)


def lt_real_fun(x, y):
    return x < y


def le_real_fun(x, y):
    return x <= y


def add_int_fun(x, y):
    return x + y


def mul_int_fun(x, y):
    return x * y


def minus_int_fun(x, y):
    return x - y


def divide_int_fun(x, y):
    return x / y


def uminus_int_fun(x):
    return -x


def abs_int_fun(x):
    return abs(x)


def lt_int_fun(x, y):
    return x < y


def le_int_fun(x, y):
    return x <= y


def mod_fun(x, y):
    return x % y


def eq_fun(_, x, y):
    return x == y


def mul_fun(_, op, _1, x, y):
    return op(x, y)


def add_fun(_, op, _1, x, y):
    return op(x, y)


def minus_fun(_, op, _1, x, y):
    return op(x, y)


def div_fun(_, op, _1, x, y):
    return op(x, y)


def uminus_fun(_, op, _1, x):
    return op(x)


def abs_fun(_, op, _1, x):
    return op(x)


def lt_fun(_, op, _1, x, y):
    return op(x, y)


def le_fun(_, op, _1, x, y):
    return op(x, y)
