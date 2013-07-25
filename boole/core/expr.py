#############################################################################
#
# expr.py
#
# description: types and expressions in Boole, all constructors inherit from
# the Expr class, except Tele, which inherits from BaseExpr
#
#
# Authors:
# Jeremy Avigad
# Cody Roux
#
#
##############################################################################


from expr_base import *

##############################################################################
#
# Expressions and types: these implement the term language of a dependent,
# extensional, impredicative and classical type theory, With subtyping.
#
#
# The datatype is represented by:
#
# Expr := Type | Kind | Bool   | Const(string,Expr)  | DB(int) |
#         Pi(name,Expr,Expr)   | App(Expr,Expr,Expr) |
#         Abst(name,Expr,Expr) | Sig(name,Expr,Expr) |
#         Pair(Expr,Expr,Type) | Fst(Expr) | Snd(Expr) |
#         Ev(Tele) |
#         Forall(name,Expr,Expr)           | Exists(name,Expr,Expr) |
#         Sub(Expr,Expr)       | Box(Expr,Expr,Expr)
#
# Tele := Tele([name,...,name],[Expr,...,Expr])
#
###############################################################################


class Const(Expr):
    """A constant declaration. Variables
    and constants are identified.
    """

    def __init__(self, name, type, **kwargs):
        """
        
        Arguments:
        - `name`: A name representing the constant
        - `type`: an expression representing its type
        - `checked`: a boolean indicating that the type
        has been checked to be well-kinded.
        """
        Expr.__init__(self)
        self.name = name
        self.type = type
        for k in kwargs:
            self.info[k] = kwargs[k]

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_const(self, *args, **kwargs)

    def to_string(self):
        return self.name

    def is_const(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_const():
            return self.name == expr.name
        else:
            return False


class DB(Expr):
    """A bound index represented by a De Bruijn variable.
    a De Bruijn variable generally does not to be initialized
    as it is incremented while moving through a term
    """
    
    def __init__(self, index):
        """
        """
        Expr.__init__(self)
        self.index = index

    def incr(self, inc):
        """Increment the index
        
        Arguments:
        - `inc`: integer specifying the increment.
        """
        self.index += inc

    def decr(self):
        """Decrement the index by 1
        """
        if self.index == 0:
            raise ExprError("Cannot decrement a DB\
            variable with index 0", self)
        else:
            self.index -= 1

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_db(self, *args, **kwargs)

    def to_string(self):
        return "DB({0!s})".format(self.index)

    def is_db(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_db():
            return self.index == expr.index
        else:
            return False


class Type(Expr):
    """The type of all small types
    """
    
    def __init__(self):
        """
        """
        Expr.__init__(self)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_type(self, *args, **kwargs)

    def to_string(self):
        return "Type()"

    def is_type(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        return expr.is_type()


class Kind(Expr):
    """The type of all large types
    """
    
    def __init__(self):
        """
        """
        Expr.__init__(self)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_kind(self, *args, **kwargs)

    def to_string(self):
        return "Kind()"
    
    def is_kind(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        return expr.is_kind()


class Bool(Expr):
    """The type of all propositions.
    """
    
    def __init__(self):
        """
        """
        Expr.__init__(self)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_bool(self, *args, **kwargs)

    def to_string(self):
        return "Bool()"

    def is_bool(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        return expr.is_bool()


class Bound(Expr):
    """An expression consisting of a binder,
    a domain, and a term which binds a variable of
    that domain.
    """
    
    def __init__(self, binder, dom, body):
        """
        
        Arguments:
        - `binder`: an element of the Binder class
        - `dom`: an expression denoting the domain of the variable
        - `body`: an expression with a bound variable.
        """
        Expr.__init__(self)
        self.binder = binder
        self.dom = dom
        self.body = body

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_bound(self, *args, **kwargs)

    def to_string(self):
        # Printing a bound expression involves
        # substituting the DB index by a constant
        # with the appropriate name.
        var = self.binder.var
        open_self = open_expr(var, self.dom, self.body)
        return "{0!s}({1!s},{2!s})".format(\
            self.binder.name, self.binder.var, open_self)

    def to_string_raw(self):
        return "{0!s}({1!s},{2!s},{3!s})".format(\
            self.binder.name, self.binder.var, self.dom, self.body)

    def is_bound(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_bound() and (self.binder.name == expr.binder.name):
            return self.dom.equals(expr.dom) and self.body.equals(expr.body)
        else:
            return False


class App(Expr):
    """Applications. Carries the proof of well-formedness
    """
    
    def __init__(self, conv, fun, arg):
        """
        
        Arguments:
        - `conv`: A term representing evidence that the application
        is well-typed.
        - `fun`: The functional part of the application.
        - `arg`: The argument part of the application.
        """
        Expr.__init__(self)
        self.conv = conv
        self.fun = fun
        self.arg = arg

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_app(self, *args, **kwargs)

    def to_string(self):
        """
        
        Arguments:
        - `self`:
        """
        return "App({0!s},{1!s},{2!s})".format(self.conv, self.fun, self.arg)

    def is_app(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_app():
            return self.fun.equals(expr.fun) and self.arg.equals(expr.arg)
        else:
            return False


class Pair(Expr):
    """Elements of Sigma types. They need to carry around their type,
    for type-checking to be decidable.
    """
    
    def __init__(self, fst, snd, type):
        """
        
        Arguments:
        - `fst`: an expression denoting the first component
        - `snd`: an expression denoting the second component
        - `type`: an expression
        """
        Expr.__init__(self)
        self.fst = fst
        self.snd = snd
        self.type = type

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_pair(self, *args, **kwargs)

    def to_string(self):
        return "Pair({0!s},{1!s},{2!s})".\
               format(self.fst, self.snd, self.type)
        
    def is_pair(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_pair():
            return self.fst.equals(expr.fst) and \
                   self.snd.equals(expr.snd) and \
                   self.type.equals(expr.type)
        else:
            return False


class Fst(Expr):
    """First projection for Sigma types
    """
    
    def __init__(self, expr):
        """
        
        Arguments:
        - `expr`: the expression to which is applied the projection.
        """
        Expr.__init__(self)
        self.expr = expr

    def accept(self, visitor, *args, **kwargs):
        """
    
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_fst(self, *args, **kwargs)

    def to_string(self):
        """
        
        Arguments:
        - `self`:
        """
        return "Fst({0!s})".format(self.expr)

    def is_fst(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_fst():
            return self.expr.equals(expr.expr)
        else:
            return False


class Snd(Expr):
    """Second projection for Sigma types
    """
    
    def __init__(self, expr):
        """
        
        Arguments:
        - `expr`: the expression to which is applied the projection.
        """
        Expr.__init__(self)
        self.expr = expr

    def accept(self, visitor, *args, **kwargs):
        """
    
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_snd(self, *args, **kwargs)

    def to_string(self):
        """
        
        Arguments:
        - `self`:
        """
        return "Snd({0!s})".format(self.expr)

    def is_snd(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_snd():
            return self.expr.equals(expr.expr)
        else:
            return False


class Ev(Expr):
    """Evidence type: provides evidence for a
    proposition (of type Bool)
    """
    
    def __init__(self, tele):
        """
        
        Arguments:
        - `tele`: a telescope of evidence for the proposition
        prop.
        - `prop`: a proposition whose evidence is supplied by self.
        binds NO variables.
        """
        Expr.__init__(self)
        self.tele = tele
        
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_ev(self, *args, **kwargs)

    def to_string(self):
        return "Ev({0!s})".format(self.tele)

    def is_ev(self):
        return True

    def equals(self, expr):
        """Structural equality. Does not compare telescopes!
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_ev():
            return True
        else:
            return False


class Sub(Expr):
    """The subtype relation. Makes sense regardless
    of the type of the expressions.
    """
    
    def __init__(self, lhs, rhs):
        """
        
        Arguments:
        - `lhs`: an expression
        - `rhs`: an expression
        """
        Expr.__init__(self)
        self.lhs = lhs
        self.rhs = rhs

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_sub(self, *args, **kwargs)

    def to_string(self):
        """
        
        Arguments:
        - `self`:
        """
        return "Sub({0!s}, {1!s})".format(self.lhs, self.rhs)

    def is_sub(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_sub():
            return (self.lhs.equals(expr.lhs)) and (self.rhs.equals(expr.rhs))
        else:
            return False


class Box(Expr):
    """Boxed epressions: a boxed expression
    carries a type and a witness that the type of
    the expression is a subtype of it.
    """
    
    def __init__(self, conv, expr, type):
        """
        
        Arguments:
        - `conv`: A witness to the equality between the type
        of expr and type
        - `expr`: The expression denoted by the box
        - `type`: The type assigned to expr
        """
        Expr.__init__(self)
        self.conv = conv
        self.expr = expr
        self.type = type
        
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_box(self, *args, **kwargs)

    def to_string(self):
        return "Box({0!s},{1!s},{2!s})".format(self.conv, self.expr, self.type)

    def is_box(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_box():
            return self.expr.equals(expr.expr)
        else:
            return False


##############################################################################
#
# The class of variable binders: this includes Pi, Abst, forall/exists
# and Sig
#
###############################################################################

class Binder(object):
    """The class of Expression binders.
    """
    
    def __init__(self, var):
        """
        
        Arguments:
        - `var`: a variable name
        """
        self.var = var

    def is_pi(self):
        return False

    def is_abst(self):
        return False

    def is_forall(self):
        return False

    def is_exists(self):
        return False

    def is_sig(self):
        return False


class Pi(Binder):
    """Dependent product
    """
    
    def __init__(self, var):
        Binder.__init__(self, var)
        self.name = "pi"
        
    def is_pi(self):
        return True

class Sig(Binder):
    """Dependent sum
    """
    
    def __init__(self, var):
        Binder.__init__(self, var)
        self.name = "sig"
        
    def is_sig(self):
        return True

        
class Abst(Binder):
    """Abstraction
    """
    
    def __init__(self, var):
        Binder.__init__(self, var)
        self.name = "abst"
        
    def is_abst(self):
        return True

 
class Forall(Binder):
    """Universal quantification
    """
    
    def __init__(self, var):
        Binder.__init__(self, var)
        self.name = "forall"
        
    def is_forall(self):
        return True


class Exists(Binder):
    """Existential quantification
    """
    
    def __init__(self, var):
        Binder.__init__(self, var)
        self.name = "exists"
        
    def is_exists(self):
        return True
        

###############################################################################
#
# The Tele class represents a telescope.
#
###############################################################################

class Tele(Expr):
    """A telescope is a (possible) list of names
    and expressions, each expression may depend on the
    previous ones.
    """
    
    def __init__(self, vars, types):
        """
        
        Arguments:
        - `vars`: the names of the variable associated to each expression.
        - `exprs`: a list of types. Each type binds a variable of
        the previous type.
        """
        Expr.__init__(self)
        self.info = info.DefaultInfo()
        self.vars = vars
        self.types = types
        self.len = len(self.types)
        assert(len(self.vars) == self.len)

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_tele(self, *args, **kwargs)

    def to_string(self):
        """
        
        Arguments:
        - `self`:
        """
        var_str = ','.join(self.vars)
        ty_str = ','.join(map(str, self.types))
        return "Tele([{0!s}],[{1!s}])".format(var_str, ty_str)

    def equals(self, tele):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if self.len == tele.len:
            eq_info = [t1.equals(t2)\
                       for (t1, t2) in zip(self.types, tele.types)]
            return reduce(lambda x, y: x and y, eq_info, True)
        else:
            return False

    def __str__(self):
        """Call the printer implemented in info
        """
        try:
            return self.info['__str__'](self)
        except KeyError:
            raise AttributeError('__str__')

    def __len__(self):
        return self.len

    def append(self, var, ty):
        """Add a variable and a type to the
        telescope. Side-effect free:
        returns a telescope
        
        Arguments:
        - `var`: a variable
        - `ty`: an expression
        """
        return Tele(self.vars + [var], self.types + [ty])

    def concat(self, tele):
        """Same as above, but for concatenation
        
        Arguments:
        - `tele`:
        """
        return Tele(self.vars + tele.vars, self.types + tele.types)

    def pop(self, i=None):
        """Pop the i-th (last by default)
        argument of a telescope
        return the pair (name, type)
        
        Arguments:
        - `i`: an integer
        """
        if i is None:
            return (self.vars.pop(), self.types.pop())
        else:
            return (self.vars.pop(i), self.types.pop(i))


def open_tele(tele, vars, checked=False):
    """Takes a telescope and returns a list of pairs
    (constant, type) where the subsequent types may depend
    on the constant.
    
    Arguments:
    - `tele`: a telescope
    """
    opened_ty = tele.types
    consts = []
    for i in range(0, tele.len):
        opened_ty[i] = subst_expr(consts, opened_ty[i], is_open=True)
        x = Const(vars[i], opened_ty[i], checked=checked)
        consts.append(x)
    return (consts, opened_ty)


def open_tele_default(tele):
    """Open a telescope with the default variables provided by
    the telescope definition.
    
    Arguments:
    - `tele`: a telescope
    """
    return open_tele(tele, tele.vars)


def open_tele_fresh(tele, checked=False):
    """Open a telescope with fresh variables
    
    Arguments:
    - `tele`: a telescope
    """
    fr_vars = [fresh_name.get_name(v) for v in tele.vars]
    return open_tele(tele, fr_vars, checked=checked)


###############################################################################
#
# The visitor class for Expr and Tele
#
###############################################################################


class ExprVisitor(object):
    """The visitor class for Expr and Tele
    """
    
    def __init__(self):
        """Do nothing by default.
        """
        pass

    def visit_const(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_db(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_type(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_kind(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_bool(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_bound(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_app(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_pair(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_fst(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_snd(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_ev(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_sub(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_box(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_tele(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit(self, expr, *args, **kwargs):
        """Call the appropriate method of self
        on expr depending on its form.
        
        Arguments:
        - `expr`: an expression
        """
        return expr.accept(self, *args, **kwargs)


###############################################################################
#
# Locally nameless representation utility functions:
# binding and freeing variables.
#
###############################################################################


class AbstractExpr(ExprVisitor):
    """Abstract an expression over a list
    of names, in the locally nameless approach. Return
    the updated expression. The names should be distinct.
    """
    
    def __init__(self, names):
        """

        Arguments:
        - `names`: a list of strings
        """
        ExprVisitor.__init__(self)
        self.names = names

    def visit_const(self, expr, depth):
        """
        
        Arguments:
        - `expr`: an expression.
        - `depth`: the number of binders crossed.
        """
        if expr.name in self.names:
            index = depth + self.names.index(expr.name)
            return DB(index)
        else:
            return expr

    def visit_db(self, expr, *args, **kwargs):
        return DB(expr.index)

    def visit_type(self, expr, *args, **kwargs):
        return Type()

    def visit_kind(self, expr, *args, **kwargs):
        return Kind()

    def visit_bool(self, expr, *args, **kwargs):
        return Bool()

    def visit_bound(self, expr, depth):
        """
        
        Arguments:
        - `expr`: an expression.
        - `depth`: the number of binders crossed.
        """
        dom = self.visit(expr.dom, depth)
        b_body = self.visit(expr.body, depth + 1)
        return Bound(expr.binder, dom, b_body)
        
    def visit_app(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return App(conv, fun, arg)

    def visit_pair(self, expr, *args, **kwargs):
        type = self.visit(expr.type, *args, **kwargs)
        fst = self.visit(expr.fst, *args, **kwargs)
        snd = self.visit(expr.snd, *args, **kwargs)
        return Pair(fst, snd, type)

    def visit_fst(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Fst(sub_expr)

    def visit_snd(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Snd(sub_expr)

    def visit_ev(self, expr, *args, **kwargs):
        tele = self.visit(expr.tele, *args, **kwargs)
        return Ev(tele)

    def visit_sub(self, expr, *args, **kwargs):
        lhs = self.visit(expr.lhs, *args, **kwargs)
        rhs = self.visit(expr.rhs, *args, **kwargs)
        return Sub(lhs, rhs)

    def visit_box(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        expr_cast = self.visit(expr.expr, *args, **kwargs)
        type = self.visit(expr.type, *args, **kwargs)
        return Box(conv, expr_cast, type)

    def visit_tele(self, expr, depth):
        types = []
        for i, e in enumerate(expr.types):
            abs_e = self.visit(e, depth + i)
            types.append(abs_e)

        return Tele(expr.vars, types)

    @info.same_info
    def visit(self, expr, *args, **kwargs):
        return expr.accept(self, *args, **kwargs)


def abstract_expr(vars, expr):
    """Abstract a list of variables in an
    expression.
    
    Arguments:
    - `var_list`: a list of variable names
    - `expr`: an expression
    """
    abstractor = AbstractExpr(vars)
    return abstractor.visit(expr, 0)


class SubstExpr(ExprVisitor):
    """Given a list of expressions e0,...,en
    instantiate the DB indices 0,...,n with those
    terms.
    """
    
    def __init__(self, exprs, is_open=None):
        """
        
        Arguments:
        - `exprs`: the expressions to instantiate.
        """
        ExprVisitor.__init__(self)
        self.exprs = exprs
        self.len = len(self.exprs)
        self.is_open = is_open
        
    def visit_const(self, expr, *args, **kwargs):
        if self.is_open:
            return expr
        else:
            ty = self.visit(expr.type, *args, **kwargs)
            return Const(expr.name, ty)

    def visit_db(self, expr, depth):
        if expr.index < depth:
            return DB(expr.index)
        elif expr.index < depth + self.len:
            return self.exprs[expr.index - depth]
        else:
            return DB(expr.index)
            # raise ExprError("Unbound DB variable", expr)
        
    def visit_type(self, expr, *args, **kwargs):
        return Type()

    def visit_kind(self, expr, *args, **kwargs):
        return Kind()

    def visit_bool(self, expr, *args, **kwargs):
        return Bool()

    def visit_bound(self, expr, depth):
        dom = self.visit(expr.dom, depth)
        b_expr = self.visit(expr.body, depth + 1)
        return Bound(expr.binder, dom, b_expr)

    def visit_app(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return App(conv, fun, arg)

    def visit_pair(self, expr, *args, **kwargs):
        type = self.visit(expr.type, *args, **kwargs)
        fst = self.visit(expr.fst, *args, **kwargs)
        snd = self.visit(expr.snd, *args, **kwargs)
        return Pair(fst, snd, type)

    def visit_fst(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Fst(sub_expr)

    def visit_snd(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Snd(sub_expr)

    def visit_ev(self, expr, *args, **kwargs):
        tele = self.visit(expr.tele, *args, **kwargs)
        return Ev(tele)

    def visit_sub(self, expr, *args, **kwargs):
        lhs = self.visit(expr.lhs, *args, **kwargs)
        rhs = self.visit(expr.rhs, *args, **kwargs)
        return Sub(lhs, rhs)

    def visit_box(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        expr_cast = self.visit(expr.expr, *args, **kwargs)
        type = self.visit(expr.type, *args, **kwargs)
        return Box(conv, expr_cast, type)

    def visit_tele(self, expr, depth):
        types = []
        for i, e in enumerate(expr.types):
            abs_e = self.visit(e, depth + i)
            types.append(abs_e)

        return Tele(expr.vars, types)

    @info.same_info
    def visit(self, expr, *args, **kwargs):
        return expr.accept(self, *args, **kwargs)


def subst_expr(exprs, expr, is_open=None):
    """Instantiate DB indices in expr according
    to expr_list
    
    Arguments:
    - `expr_list`: a list of expressions
    - `expr`: an expression
    """
    if is_open != None:
        subster = SubstExpr(exprs, is_open=is_open)
    else:
        subster = SubstExpr(exprs)
    return subster.visit(expr, 0)


def sub_in(exprs, vars, expr):
    """Replace constants with names given by vars
    by exprs in expr.
    
    Arguments:
    - `exprs`: a list of expressions
    - `vars`: a list of variable names
    - `expr`: an expression
    """
    return subst_expr(exprs, abstract_expr(vars, expr))


def open_expr(var, typ, expr, checked=None):
    """Return the opened version of an expression
    with a bound variable, by substituting
    the bound name with a constant of type
    typ.
    
    Arguments:
    - `var`: a variable name
    - `typ`: a type
    - `expr`: an expression with a bound
    variable
    - `checked`: marks weather typ has been
    checked for well-typedness
    """
    if checked == None:
        const = Const(var, typ, checked=True)
    else:
        const = Const(var, typ, checked=checked)
    return subst_expr([const], expr, is_open=True)


def open_bound_fresh(expr, checked=None):
    """Return the opened body of a bound expression
    using the variable from the binder to generate a fresh
    name, along with the variable name. The constant is marked as
    type-checked by default.
    
    Arguments:
    - `expr`: an instance of Bound
    """
    var = fresh_name.get_name(expr.binder.var)
    return (var, open_expr(var, expr.dom, expr.body, checked=checked))

###############################################################################
#
# Various utility functions.
#
###############################################################################


def root_app(expr):
    """Returns the pair (r, args)
    such that expr = r(*args)
    
    Arguments:
    - `expr`: an expression
    """
    root = expr
    args = []
    while root.is_app():
        args.append(root.arg)
        root = root.fun
        #The arguments were collected in reverse order
    args.reverse()
    return (root, args)


def root_pi(expr):
    """Returns the pair (r, [an,..,a0])
    such that expr = Pi(a0, Pi(.. Pi(an, r)..)
    
    Arguments:
    - `expr`: an expression
    """
    root = expr
    args = []
    while root.is_bound() and root.binder.is_pi():
        args.append(root.dom)
        _, root = open_bound_fresh(root)
    return (root, args)


def arg_i(expr, i):
    """Takes an expresion of the form f(a0,..., an)
    and returns ai, fails if the argument is not of the
    correct form.
    
    Arguments:
    - `expr`: an expression
    - `i`: an integer
    """
    _, args = root_app(expr)
    return args[i]


def is_eq(expr):
    """Returns True if the expression
    is of the form eq(e1, e2), False otherwise.
    
    Arguments:
    - `expr`:
    """
    root, args = root_app(expr)
    #There is an implicit type argument
    return root.is_const() and (root.name == '==') and (len(args) == 3)


def is_impl(expr):
    """Returns True if the expression
    is of the form impl(e1, e2), False otherwise.
    
    Arguments:
    - `expr`:
    """
    root, args = root_app(expr)
    return root.is_const() and root.name == '>=' and \
           len(args) == 2


def root_clause(expr):
    """Returns r such that expr is of the form
    forall(x1,...,forall(xn, p1 >= (p2 >= ... (pm >= r))))
    replacing xi with fresh variables
    
    Arguments:
    - `expr`: an expression
    """
    root = expr
    while root.is_bound() and root.binder.is_forall():
        _, root = open_bound_fresh(root)
    while is_impl(root):
        root = arg_i(root, 1)
    return root


def sig_to_tele(expr, open_bound):
    """Takes a sigma type S = Sig(x1:A1,Sig(x2:A2,...,An+1)..)
    and returns the telescope:
    [x1:A1,...,xn:An,h:An+1]
    
    Arguments:
    - `expr`: an expression
    - `open_bound`: a function which opens binders
    """
    sig_ty = expr
    tele = Tele([], [])
    while sig_ty.is_bound() and sig_ty.binder.is_sig():
        v, new_ty = open_bound(sig_ty)
        tele = tele.append(v, sig_ty.dom)
        sig_ty = new_ty
    hyp = fresh_name.get_name('hyp')
    return tele.append(hyp, sig_ty)


def unpack_sig(expr, open_bound):
    """Takes a sigma type S = Sig(x1:A1,Sig(x2:A2,...,An)..)
    and returns the dependent tuple
    (x1, (x2,(...,h)..) with xi : Ai and h : An
    
    Arguments:
    - `expr`: an expression
    """
    sig_ty = expr
    tup = []
    while sig_ty.is_bound() and sig_ty.binder.is_sig():
        v, new_ty = open_bound(sig_ty)
        c = Const(v, sig_ty.dom)
        tup.append((c, sig_ty))
        sig_ty = new_ty
    hyp = fresh_name.get_name('h')
    c = Const(hyp, sig_ty)
    if len(tup) == 0:
        return c
    else:
        ret = c
        while len(tup) != 0:
            fst, ty = tup.pop()
            ret = Pair(fst, ret, ty)
        return ret
