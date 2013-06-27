#############################################################################
#
# expr.py
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
import vargen

##############################################################################
#
# Global fresh variable generator for expressions
#
##############################################################################


fresh_name = vargen.VarGen()

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

    def __mul__(self, arg):
        """Call the multiplication implemented in info
        """
        try:
            return self.info['__mul__'](self, arg)
        except KeyError:
            print self, self.info
            mess = '`BaseExpr` object does not support multiplication'
            raise TypeError(mess)

    def __add__(self, arg):
        """Call the addition implemented in info
        """
        try:
            return self.info['__add__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support addition'
            raise TypeError(mess)

    def __rmul__(self, arg):
        """Call the multiplication implemented in info
        """
        try:
            return self.info['__rmul__'](self, arg)
        except KeyError:
            print self, self.info
            mess = '`BaseExpr` object does not support left multiplication'
            raise TypeError(mess)

    def __radd__(self, arg):
        """Call the addition implemented in info
        """
        try:
            return self.info['__radd__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support left addition'
            raise TypeError(mess)

    def __rshift__(self, arg):
        """Call right_shift implemented in info
        """
        try:
            return self.info['__rshift__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object can not be right-shifted'
            raise TypeError(mess)

    def __eq__(self, arg):
        """Call eq implemented in info
        """
        try:
            return self.info['__eq__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support equality'
            raise TypeError(mess)

    def __getitem__(self, index):
        """Call getitem implemented in info
        """
        try:
            return self.info['__getitem__'](self, index)
        except KeyError:
            mess = '`BaseExpr` object does not support lookup'
            raise TypeError(mess)

    def __le__(self, arg):
        """Call le implemented in info
        """
        try:
            return self.info['__le__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support le'
            raise TypeError(mess)

    def __lt__(self, arg):
        """Call le implemented in info
        """
        try:
            return self.info['__lt__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object does not support lt'
            raise TypeError(mess)

    def accept(self, visitor, *args, **kwargs):
        """

        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        raise NotImplementedError()

    def is_type(self):
        """Tests wether the expression is an instance of
        Type
        """
        return False

    def is_kind(self):
        """Tests wether the expression is an instance of
        Kind
        """
        return False

    def is_bound(self):
        """Tests wether the expression is an instance of
        Bound
        """
        return False

    def is_app(self):
        """Tests wether the expression is an instance of
        App
        """
        return False

    def is_pair(self):
        """Tests wether the expression is an instance of
        Tuple
        """
        return False

    def is_fst(self):
        """Tests wether the expression is an instance of
        Fst
        """
        return False

    def is_snd(self):
        """Tests wether the expression is an instance of
        Snd
        """
        return False

    def is_sub(self):
        """Tests wether the expression is an instance of
        Eq
        """
        return False

    def is_box(self):
        """Tests wether the expression is an instance of
        Box
        """
        return False

    def is_const(self):
        """Tests wether the expression is an instance of
        Const
        """
        return False

    def is_db(self):
        """Tests wether the expression is an instance of
        DB
        """
        return False

    def is_bool(self):
        """Tests wether the expression is an instance of
        Bool
        """
        return False

    def is_ev(self):
        """Tests wether the expression is an instance of
        EV
        """
        return False

    def is_tele(self):
        """Tests wether the expression is an instance of
        Tele
        """
        return False
