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
        - `val_dict`: a dictionary mapping constants to their value
        """
        self.eqns = eqns
        self.val_dict = val_dict
        
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


class ExprValue(e.ExprVisitor):
    """Return the value of an expression.
    """
    
    def __init__(self):
        e.ExprVisitor.__init__(self)

    def visit_const(self, expr, model=None):
        if expr.value:
            return expr.value
        else:
            try:
                return model.vals[expr.name]
            except KeyError:
                raise NoValue(expr)

    def visit_db(self, expr, model=None):
        raise NoValue(expr)

    def visit_type(self, expr, model=None):
        raise NoValue(expr)

    def visit_kind(self, expr, model=None):
        raise NoValue(expr)

    def visit_bool(self, expr, model=None):
        return [True, False]

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
            if isinstance(v1, v2):
                return (not v1) or v2
            else:
                return v1 == v2
        return sub_val

    def visit_box(self, expr, model=None):
        return self.visit(expr.expr, model)

    def visit_tele(self, expr, model=None):
        raise NoValue(expr)

    def visit_mvar(self, expr, model=None):
        raise NoValue(expr)
