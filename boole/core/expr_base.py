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


##############################################################################
#
# Expressions and types: these implement the term language of a dependent,
# extensional, impredicative and classical type theory.
#
#
# The datatype is represented by:
#
# Expr := Type | Kind | Bool   | Const(string,Expr)  | DB(int) |
#         Pi(name,Expr,Expr)   | App(Expr,Expr,Expr) |
#         Abst(name,Expr,Expr) | Sig(Tele) |
#         Tuple([Expr,...,Expr],Type)      | Proj(int,Expr) | Ev(Tele) |
#         Forall(name,Expr,Expr)           | Exists(name,Expr,Expr) |
#         Eq(Expr,Expr)        | Box(Expr,Expr,Expr)
#
# Tele := Tele([name,...,name],[Expr,...,Expr])
#
###############################################################################


class BaseExpr(object):
    """The syntactic class of expressions and telescopes.
    """
    
    def __init__(self, ):
        """Sets the default info
        """
        self.info = info.DefaultInfo()
        
    def __getattr__(self, name):
        """
        return field contained in info
        if not already given by the expression.
        
        Arguments:
        - `name`: the name of the attribute.
        """
        try:
            return self.info[name]
        except KeyError:
            #TODO: is this the right thing?
            #raise AttributeError(name)
            return None


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

    def __rshift__(self, arg):
        """Call right_shift implemented in info
        """
        try:
            return self.info['__rshift__'](self, arg)
        except KeyError:
            mess = '`BaseExpr` object can not be right-shifted'
            raise TypeError(mess)


    def __eq__(self, arg):
        """Call right_shift implemented in info
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


    def accept(self, visitor, *args, **kwargs):
        """

        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        raise NotImplementedError()


class Expr(BaseExpr):
    """The class of types and expressions.
    """

    def __init__(self):
        """
        """
        self.info = info.DefaultInfo()

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

    def is_tuple(self):
        """Tests wether the expression is an instance of
        Tuple
        """
        return False

    def is_proj(self):
        """Tests wether the expression is an instance of
        Proj
        """
        return False

    def is_sig(self):
        """Tests wether the expression is an instance of
        Sig
        """
        return False

    def is_eq(self):
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
