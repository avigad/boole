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

EmptyMod = Model({}, {})

BoolVal = Value([True, False], 'Bool')


class ExprValue(e.ExprVisitor):
    """Return the value of an expression.
    """
    
    def __init__(self, strict):
        e.ExprVisitor.__init__(self)
        self.strict = strict

    def visit_const(self, expr, model, bindings):
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

    def visit_db(self, expr, model, bindings):
        if expr.index < len(bindings):
            return bindings[-(expr.index + 1)]
        if self.strict:
            raise NoValue(expr)
        else:
            return None

    def visit_type(self, expr, model, bindings):
        if self.strict:
            raise NoValue(expr)
        else:
            return None

    def visit_kind(self, expr, model, bindings):
        if self.strict:
            raise NoValue(expr)
        else:
            return None

    def visit_bool(self, expr, model, bindings):
        return BoolVal

    def visit_bound(self, expr, model, bindings):
        if expr.is_abst():
            n_args = 0
            e = expr
            while e.is_abst():
                n_args += 1
                e = e.body

            #A nameless function denoting the abstraction,
            #note that arguments to nested lambdas are passed all at once.
            def nameless(*args):
                if len(args) > n_args:
                    mess = "{0!s} arguments passed to a\
                    function which takes only {1!s}"\
                           .format(len(args), n_args)
                    raise TypeError(mess)
                else:
                    return self.visit(e, model, bindings + args)
                
            return nameless

        elif expr.is_forall():
            dom_val = self.visit(expr.dom, model, bindings)
            for v in dom_val:
                if self.visit(expr.body, model, bindings + [v]):
                    pass
                else:
                    return False
            return True
        
        elif expr.is_exists():
            dom_val = self.visit(expr.dom, model, bindings)
            for v in dom_val:
                if self.visit(expr.body, model, bindings + [v]):
                    return True
                else:
                    pass
            return False

        elif self.strict:
            raise NoValue(expr)
        else:
            return None

    def visit_app(self, expr, model, bindings):
        #evaluate all the arguments at once.
        #Include the implicit arguments.
        f, args = e.root_app(expr)
        f_val = self.visit(f, model, bindings)
        args_val = [self.visit(a, model, bindings) for a in args]
        return f_val(*args_val)

    def visit_pair(self, expr, model, bindings):
        fst_val = self.visit(expr.fst, model, bindings)
        snd_val = self.visit(expr.snd, model, bindings)
        return (fst_val, snd_val)

    def visit_fst(self, expr, model, bindings):
        pair_val = self.visit(expr.expr, model, bindings)
        return pair_val[0]

    def visit_snd(self, expr, model, bindings):
        pair_val = self.visit(expr.expr, model, bindings)
        return pair_val[1]

    def visit_ev(self, expr, model, bindings):
        return ()

    def visit_sub(self, expr, model, bindings):
        lhs_val = self.visit(expr.lhs, model, bindings)
        rhs_val = self.visit(expr.rhs, model, bindings)
        if isinstance(lhs_val, bool) and isinstance(rhs_val, bool):
            return (not lhs_val) or rhs_val
        else:
            return lhs_val == rhs_val

    def visit_box(self, expr, model, bindings):
        return self.visit(expr.expr, model, bindings)

    def visit_tele(self, expr, model, bindings):
        raise NotImplementedError()

    def visit_mvar(self, expr, model, bindings):
        if self.strict:
            raise NoValue(expr)
        else:
            return None


def eval_expr(expr, model=None, strict=False):
    """Evaluate an expression in a model.
    
    Arguments:
    - `expr`:
    - `model`:
    """
    if model is None:
        m = EmptyMod
    else:
        m = model
    return ExprValue(strict).visit(expr, m, [])


###############################################################################
#
# Semantics of built-in operations
#
###############################################################################

def add_real_fun(x, y):
    return x + y
add_real_val = Value(add_real_fun)


def mul_real_fun(x, y):
    return x * y
mul_real_val = Value(mul_real_fun)


def minus_real_fun(x, y):
    return x - y
minus_real_val = Value(minus_real_fun)


def divide_real_fun(x, y):
    return float(x) / y
divide_real_val = Value(divide_real_fun)


def power_fun(x, y):
    return x ** y
power_val = Value(power_fun)


def uminus_real_fun(x):
    return -x
uminus_real_val = Value(uminus_real_fun)


def abs_real_fun(x):
    return abs(x)
abs_real_val = Value(abs_real_fun)


def lt_real_fun(x, y):
    return x < y
lt_real_val = Value(lt_real_fun)


def le_real_fun(x, y):
    return x <= y
le_real_val = Value(le_real_fun)


def add_int_fun(x, y):
    return x + y
add_int_val = Value(add_int_fun)


def mul_int_fun(x, y):
    return x * y
mul_int_val = Value(mul_int_fun)


def minus_int_fun(x, y):
    return x - y
minus_int_val = Value(minus_int_fun)


def divide_int_fun(x, y):
    return x / y
divide_int_val = Value(divide_int_fun)


def uminus_int_fun(x):
    return -x
uminus_int_val = Value(uminus_int_fun)


def abs_int_fun(x):
    return abs(x)
abs_int_val = Value(abs_int_fun)


def lt_int_fun(x, y):
    return x < y
lt_int_val = Value(lt_int_fun)


def le_int_fun(x, y):
    return x <= y
le_int_val = Value(le_int_fun)


def mod_fun(x, y):
    return x % y
mod_val = Value(mod_fun)


def eq_fun(_, x, y):
    return x == y
eq_val = Value(eq_fun)


def mul_fun(_, op, _1, x, y):
    return op(x, y)
mul_val = Value(mul_fun)


def add_fun(_, op, _1, x, y):
    return op(x, y)
add_val = Value(add_fun)


def minus_fun(_, op, _1, x, y):
    return op(x, y)
minus_val = Value(minus_fun)


def div_fun(_, op, _1, x, y):
    return op(x, y)
div_val = Value(div_fun)


def uminus_fun(_, op, _1, x):
    return op(x)
uminus_val = Value(uminus_fun)


def abs_fun(_, op, _1, x):
    return op(x)
abs_val = Value(abs_fun)


def lt_fun(_, op, _1, x, y):
    return op(x, y)
lt_val = Value(lt_fun)


def le_fun(_, op, _1, x, y):
    return op(x, y)
le_val = Value(le_fun)
