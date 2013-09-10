#############################################################################
#
# expr_base.py
#
# description: basic types and expressions in Boole
#
#
# Authors:
# Jeremy Avigad
# Cody Roux
#
#
##############################################################################


import info

##############################################################################
#
# Exceptions associated with expressions
#
###############################################################################


class ExprError(Exception):
    """Errors for expressions
    """
    def __init__(self, mess, expr):
        Exception.__init__(self, mess)
        self.expr = expr


class Expr(object):
    """The base class for expressions and telescopes.
    """

    def __init__(self):
        """Sets the default info
        """
        self.info = info.DefaultInfo()

    def __str__(self):
        """Call the printer implemented in info
        """
        try:
            return self.info['__str__'](self)
        except KeyError:
            return object.__str__(self)

    def __call__(self, *args):
        """Call the function call implemented in info
        """
        try:
            return self.info['__call__'](self, *args)
        except KeyError:
            raise TypeError('`BaseExpr` object is not callable')

    def __getitem__(self, index):
        """Call getitem implemented in info
        """
        try:
            return self.info['__getitem__'](self, index)
        except KeyError:
            mess = '`BaseExpr` object does not support lookup'
            raise TypeError(mess)
        
    def equals(self, expr):
        """Structural equality. Checks if
        the terms are pointer-equal, and calls
        the constructor specific method otherwise.
        
        Arguments:
        - `expr`: an arbitrary expression
        """
        if self is expr:
            return True
        else:
            return self.eq(expr)

    # equality and disequality
    
    def __eq__(self, arg):
        """Call eq implemented in info
        """
        try:
            return self.info['__eq__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support equality'
            raise TypeError(mess)

    def __ne__(self, arg):
        """Call neq implemented in info
        """
        try:
            return self.info['__ne__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support equality'
            raise TypeError(mess)

    # binary arithmetic operations
    
    def __add__(self, arg):
        """Call the addition implemented in info
        """
        try:
            return self.info['__add__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support addition'
            raise TypeError(mess)

    def __radd__(self, arg):
        """Call the addition implemented in info
        """
        try:
            return self.info['__radd__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support addition'
            raise TypeError(mess)

    def __mul__(self, arg):
        """Call the multiplication implemented in info
        """
        try:
            return self.info['__mul__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support multiplication'
            raise TypeError(mess)

    def __rmul__(self, arg):
        """Call the multiplication implemented in info
        """
        try:
            return self.info['__rmul__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support multiplication'
            raise TypeError(mess)

    def __sub__(self, arg):
        """Call the subtraction implemented in info
        """
        try:
            return self.info['__sub__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support subtraction'
            raise TypeError(mess)

    def __rsub__(self, arg):
        """Call the subtraction implemented in info
        """
        try:
            return self.info['__rsub__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support subtraction'
            raise TypeError(mess)
        
    def __div__(self, arg):
        """Call the division implemented in info
        """
        try:
            return self.info['__div__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support division'
            raise TypeError(mess)

    def __rdiv__(self, arg):
        """Call the division implemented in info
        """
        try:
            return self.info['__rdiv__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support division'
            raise TypeError(mess)

    def __mod__(self, arg):
        """Call the mod implemented in info
        """
        try:
            return self.info['__mod__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support mod'
            raise TypeError(mess)

    def __rmod__(self, arg):
        """Call the mod implemented in info
        """
        try:
            return self.info['__rmod__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support mod'
            raise TypeError(mess)

    def __pow__(self, arg):
        """Call the pow implemented in info
        """
        try:
            return self.info['__pow__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support ** or pow()'
            raise TypeError(mess)

    def __rpow__(self, arg):
        """Call the pow implemented in info
        """
        try:
            return self.info['__rpow__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support ** or pow()'
            raise TypeError(mess)

    # unary arithmetic operations

    def __neg__(self):
        """Call negation implemented in info
        """
        try:
            return self.info['__neg__'](self)
        except KeyError:
            mess = '`BaseExpr` object can not be negated'
            raise TypeError(mess)

    def __abs__(self):
        """Call negation implemented in info
        """
        try:
            return self.info['__abs__'](self)
        except KeyError:
            mess = '`BaseExpr` object does not support abs'
            raise TypeError(mess)

    # binary arithmetic relations
    
    def __le__(self, arg):
        """Call le implemented in info
        """
        try:
            return self.info['__le__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support le'
            raise TypeError(mess)

    def __lt__(self, arg):
        """Call lt implemented in info
        """
        try:
            return self.info['__lt__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support lt'
            raise TypeError(mess)

    def __ge__(self, arg):
        """Call ge implemented in info
        """
        try:
            return self.info['__ge__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support ge'
            raise TypeError(mess)

    def __gt__(self, arg):
        """Call ge implemented in info
        """
        try:
            return self.info['__gt__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support gt'
            raise TypeError(mess)

    # bit operations
          
    def __and__(self, arg):
        """Call and implemented in info
        """
        try:
            return self.info['__and__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support conjunction'
            raise TypeError(mess)

    def __rand__(self, arg):
        """Call and implemented in info
        """
        try:
            return self.info['__rand__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support conjunction'
            raise TypeError(mess)
    
    def __or__(self, arg):
        """Call or implemented in info
        """
        try:
            return self.info['__or__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support or'
            raise TypeError(mess)

    def __ror__(self, arg):
        """Call or implemented in info
        """
        try:
            return self.info['__ror__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support or'
            raise TypeError(mess)
        
    def __invert__(self):
        """Call not implemented in info
        """
        try:
            return self.info['__invert__'](self)
        except KeyError:
            mess = '`BaseExpr` object does not support invert'
            raise TypeError(mess)

    def __rshift__(self, arg):
        """Call right_shift implemented in info
        """
        try:
            return self.info['__rshift__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object can not be right-shifted'
            raise TypeError(mess)
        
    # methods to support recursion
    
    def accept(self, visitor, *args, **kwargs):
        """

        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        raise NotImplementedError()

    def is_type(self):
        """Tests whether the expression is an instance of
        Type
        """
        return False

    def is_kind(self):
        """Tests whether the expression is an instance of
        Kind
        """
        return False

    def is_bound(self):
        """Tests whether the expression is an instance of
        Bound
        """
        return False

    def is_app(self):
        """Tests whether the expression is an instance of
        App
        """
        return False

    def is_pair(self):
        """Tests whether the expression is an instance of
        Tuple
        """
        return False

    def is_fst(self):
        """Tests whether the expression is an instance of
        Fst
        """
        return False

    def is_snd(self):
        """Tests whether the expression is an instance of
        Snd
        """
        return False

    def is_sub(self):
        """Tests whether the expression is an instance of
        Eq
        """
        return False

    def is_box(self):
        """Tests whether the expression is an instance of
        Box
        """
        return False

    def is_const(self):
        """Tests whether the expression is an instance of
        Const
        """
        return False

    def is_db(self):
        """Tests whether the expression is an instance of
        DB
        """
        return False

    def is_bool(self):
        """Tests whether the expression is an instance of
        Bool
        """
        return False

    def is_ev(self):
        """Tests whether the expression is an instance of
        Ev
        """
        return False

    def is_mvar(self):
        """Tests whether the expression is an instance of
        Mvar
        """
        return False

    def is_tele(self):
        """Tests whether the expression is an instance of
        Tele
        """
        return False

    def is_pi(self):
        """Tests whether the expression is an instance of
        Bound and the binder is pi
        """
        return self.is_bound() and self.binder.is_pi()

    def is_sig(self):
        """Tests whether the expression is an instance of
        Bound and the binder is sig
        """
        return self.is_bound() and self.binder.is_sig()

    def is_forall(self):
        """Tests whether the expression is an instance of
        Bound and the binder is forall
        """
        return self.is_bound() and self.binder.is_forall()

    def is_exists(self):
        """Tests whether the expression is an instance of
        Bound and the binder is exists
        """
        return self.is_bound() and self.binder.is_exists()

    def is_abst(self):
        """Tests whether the expression is an instance of
        Bound and the binder is abst
        """
        return self.is_bound() and self.binder.is_abst()


