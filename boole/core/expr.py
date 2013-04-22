################################################################################
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
################################################################################




################################################################################
#
# Miscellaneous useful procedures
#
################################################################################

        
# this is used for functions that take a string, consisting either of
# a single name, or a list of names, e.g.
#
#   Int('x')
#   Int('x y z')
#   Int('x,y,z')
#
# It is modeled after Sage's SR.var
def _str_to_list(s):
    if ',' in s:
        return [item.strip() for item in s.split(',')]
    elif ' ' in s:
        return [item.strip() for item in s.split()]
    else:
        return [s]


# TODO: replace with a dictionary which counts the use
# of a single name.
class FreshGen(object):
    """Generate a fresh name according to a counter
    which should never be reset.
    """
    
    def __init__(self):
        """Initialize the index to 0.
        """
        self._index = 0

    def get_name(self, name = None):
        """Return an unused name
        """
        if name != None:
            pad = name
        else:
            pad = "_Boole"
        fresh_name = "{0!s}_{0!s}".format(pad, self._index)
        self._index += 1
        return fresh_name



fresh_name = FreshGen()




################################################################################
#
# Exceptions associated with expressions
#
################################################################################

        
class ExprError(Exception):
    """Errors for expressions
    """
    def __init__(self, mess, expr):
        Exception.__init__(self, mess)
        self.expr = expr


       


################################################################################
#
# Expressions and types: these implement the term language of a dependent,
# extensional, impredicative and classical type theory.
#
#
# The datatype is represented by:
#
# Expr := Type | Kind | Bool | Const(name) | DB(int) | Pi(name,Expr,Expr) |
#         App(Expr,Expr,Expr) | Abs(name,Expr,Expr) | Sig(Tele,Expr) |
#         Tuple(Expr,...,Expr) | Proj(int,Expr) | Ev(Tele,Expr) |
#         Forall(name,Expr,Expr) | Exists(name,Expr,Expr) |
#         Eq(Expr,Expr) | Box(Expr,Expr,Expr)
#
# Tele := Tele([name,...,name],[Expr,...,Expr])
#
################################################################################

class Expr(object):
    """The class of types and expressions.
    """
    
    def __init__(self):
        """
        """

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        raise NotImplemented()

        

class Const(Expr):
    """A constant declaration. Variables
    and constants are identified.
    """
    
    def __init__(self, name, type):
        """
        
        Arguments:
        - `name`:
        - `type`:
        """
        self.name = name
        self.type = type

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_const(self, *args, **kwargs)

        

class DB(Expr):
    """A bound index represented by a De Bruijn variable.
    a De Bruijn variable generally does not to be initialized
    as it is incremented while moving through a term
    """
    
    def __init__(self, index = 0):
        """
        """
        self.index = index

    def incr(self, inc=1):
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
        visitor.visit_db(self, *args, **kwargs)
                



class Type(Expr):
    """The type of all small types
    """
    
    def __init__(self):
        """
        """

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_type(self, *args, **kwargs)

        
class Kind(Expr):
    """The type of all large types
    """
    
    def __init__(self):
        """
        """
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_kind(self, *args, **kwargs)


class Bool(Expr):
    """The type of all propositions.
    """
    
    def __init__(self):
        """
        """
                
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_bool(self, *args, **kwargs)

class Bound(Expr):
    """An expression consisting of a binder,
    a domain, and a term which binds a variable of
    that domain.
    """
    
    def __init__(self, binder, dom, expr):
        """
        
        Arguments:
        - `binder`: an element of the Binder class
        - `dom`: an expression denoting the domain of the variable
        - `expr`: an expression
        """
        self.binder = binder
        self.dom = dom
        self.expr = expr
        

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_bound(self, *args, **kwargs)



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
        visitor.visit_const(self, *args, **kwargs)


class Sig(Expr):
    """Sigma types, takes a telescope as argument
    """
    
    def __init__(self, telescope, type):
        """
        
        Arguments:
        - `telescope`: A telescope of types.
        - `type`: A term which may depend on elements of the
        telescope. Binds n variables where n is the length of the
        telescope.
        """
        self.telescope = telescope
        self.type = type
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_sig(self, *args, **kwargs)


class Tuple(Expr):
    """Elements of Sigma types.
    """
    
    def __init__(self, exprs):
        """
        
        Arguments:
        - `expr_list`: a list of expressions
        """
        self.exprs = exprs

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_tuple(self, *args, **kwargs)


class Proj(Expr):
    """Projections for Sigma types
    """
    
    def __init__(self, index, expr):
        """
        
        Arguments:
        - `index`: an integer
        - `expr`: the expression to which is applied the projection.
        """
        self.index = index
        self.expr = expr

    def accept(self, visitor, *args, **kwargs):
        """
    
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_proj(self, *args, **kwargs)
        


class Ev(Expr):
    """Evidence type: provides evidence for a
    proposition (of type Bool)
    """
    
    def __init__(self, telescope, prop):
        """
        
        Arguments:
        - `telescope`: a telescope of evidence for the proposition
        prop.
        - `prop`: a proposition whose evidence is supplied by self.
        binds NO variables.
        """
        self.telescope = telescope
        self.prop = prop
        
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_ev(self, *args, **kwargs)



class Eq(Expr):
    """Equality between expression. Makes sense regardless
    of the type of the expressions.
    """
    
    def __init__(self, expr1, expr2):
        """
        
        Arguments:
        - `expr1`: an expression
        - `expr2`: an expression
        """
        self.lhs = expr1
        self.rhs = expr2

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_eq(self, *args, **kwargs)



class Box(Expr):
    """Boxed epressions: a boxed expression
    carries a type and a witness that the type of
    the expression is identical to it.
    """
    
    def __init__(self, conv, expr, type):
        """
        
        Arguments:
        - `conv`: A witness to the equality between the type
        of expr and type
        - `expr`: The expression denoted by the box
        - `type`: The type assigned to expr
        """
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
        visitor.visit_box(self, *args, **kwargs)


################################################################################
#
# The class of 1 variable binders: this includes Pi, Abs, forall/exists
# but excludes Sig.
#
################################################################################

class Binder(object):
    """The class of Expression binders.
    """
    
    def __init__(self):
        pass

    def is_pi(self):
        return False

    def is_abs(self):
        return False

    def is_forall(self):
        return False

    def is_exists(self):
        return False


class Pi(Binder):
    """Abstraction
    """
    
    def __init__(self, var):
        """
        
        Arguments:
        - `var`:
        """
        self.var = var
        
    def is_pi(self):
        return True
        
        
class Abs(Binder):
    """Abstraction
    """
    
    def __init__(self, var):
        """
        
        Arguments:
        - `var`:
        """
        self.var = var
        
    def is_abs(self):
        return True
        
class Forall(Binder):
    """Abstraction
    """
    
    def __init__(self, var):
        """
        
        Arguments:
        - `var`:
        """
        self.var = var
        
    def is_forall(self):
        return True
        
class Exists(Binder):
    """Abstraction
    """
    
    def __init__(self, var):
        """
        
        Arguments:
        - `var`:
        """
        self.var = var
        
    def is_exists(self):
        return True
        

        




################################################################################
#
# The Tele class represents a telescope.
#
################################################################################

class Tele(object):
    """A telescope is a (possible) list of names
    and expressions, each expression may depend on the
    previous ones.
    """
    
    def __init__(self, vars, types):
        """
        
        Arguments:
        - `vars`: the names of the variable associated to each expression.
        - `exprs`: a list of types. Each type binds a variable of the previous type.
        """
        self.vars = vars
        self.types = types
        self.len = len(self.types)


    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        visitor.visit_tele(self, *arg, **kwargs)




################################################################################
#
# The visitor class for Expr and Tele
#
################################################################################

class ExprVisitor(object):
    """
    """
    
    def __init__(self):
        """Do nothing by default.
        """
        pass

    def visit_const(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_db(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_type(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_kind(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_bool(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_binder(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_app(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_sig(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_tuple(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_proj(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_ev(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_eq(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_box(self, expr, *args, **kwargs):
        raise NotImplemented()

    def visit_tele(self, expr, *args, **kwargs):
        raise NotImplemented()


    def visit(self, expr, *args, **kwargs):
        """Call the appropriate method of self
        on expr depending on its form.
        
        Arguments:
        - `expr`: an expression
        """
        return expr.accept(self, *args, **kwargs)




################################################################################
#
# Locally nameless representation utility functions:
# binding and freeing variables.
#
################################################################################


# TODO: should this just perform a side effect on the expression?
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
        self.names = names

        
    def visit_const(self, expr, depth):
        """
        
        Arguments:
        - `expr`: an expression.
        - `depth`: the number of binders crossed.
        """
        if expr.name in self.names:
            index = depth + self.names.index(expr.name)
            return DB(index = index)
        else:
            return Const(expr.name, expr.type)
            

    def visit_db(self, expr, *args, **kwargs):
        return DB(index = expr.index)


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
        b_expr = self.visit(expr.expr, depth + 1)
        return Bound(expr.binder, dom, b_expr)
        

    def visit_app(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return App(conv, fun, arg)


    def visit_sig(self, expr, depth):
        """
        
        Arguments:
        - `expr`: an expression.
        - `depth`: the number of binders crossed.
        """
        tele = self.visit(expr.telescope, depth)
        shift = expr.telescope.len
        type = self.visit(expr.type, depth + shift)
        return Sig(tele, type)


    def visit_tuple(self, expr, *args, **kwargs):
        exprs = map(lambda x:self.visit(x, *args, **kwargs), expr.exprs)
        return Tuple(exprs)
        

    def visit_proj(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Proj(expr.index, sub_expr)


    def visit_ev(self, expr, *args, **kwargs):
        tele = self.visit(expr.tele, *args, **kwargs)
        prop = self.visit(expr.prop, *args, **kwargs)
        return Ev(tele, prop)
        

    def visit_eq(self, expr, *args, **kwargs):
        lhs = self.visit(expr.lhs, *args, **kwargs)
        rhs = self.visit(expr.rhs, *args, **kwargs)
        return Eq(lhs, rhs)


    def visit_box(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        expr = self.visit(expr.expr, *args, **kwargs)
        type = self.visit(expr.type, *args, **kwargs)
        return Box(conv, expr, type)


    def visit_tele(self, expr, depth):
        """
        
        Arguments:
        - `expr`: an expression.
        - `depth`: the number of binders crossed.
        """
        types = []
        for i, e in enumerate(expr.types):
            abs_e = self.visit(e, depth + i)
            types.append(abs_e)

        return Tele(expr.vars, types)





def abstract_expr(var_list, expr):
    """Abstract a list of variables in an
    expression.
    
    Arguments:
    - `var_list`: a list of variable names
    - `expr`: an expression
    """
    abstractor = AbstractExpr(var_list)
    return abstractor.visit(expr, 0)



class SubstExpr(ExprVisitor):
    """Given a list of expressions e0,...,en
    instantiate the DB indices 1,...,n with those
    terms.
    """
    
    def __init__(self, exprs):
        """
        
        Arguments:
        - `exprs`: the expressions to instanciate.
        """
        self.exprs = exprs
        self.len = len(self.exprs)
        
    def visit_const(self, expr, *args, **kwargs):
        return Const(expr.name, expr.type)

    def visit_db(self, expr, depth):
        if expr.index < depth:
            return DB(index = expr.index)
        elif expr.index < depth + self.len:
            return self.exprs[expr.index - depth]
        else:
            raise ExprError("Unbound DB variable", expr)
           
    def visit_type(self, expr, *args, **kwargs):
        return Type()

    def visit_kind(self, expr, *args, **kwargs):
        return Kind()

    def visit_bool(self, expr, *args, **kwargs):
        return Bool()

    def visit_bound(self, expr, depth):
        dom = self.visit(expr.dom, depth)
        b_expr = self.visit(expr.expr, depth + 1)
        return Bound(expr.binder, dom, b_epr)

    def visit_app(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return App(conv, fun, arg)

    def visit_sig(self, expr, depth):
        tele = self.visit(expr.telescope, depth)
        shift = expr.telescope.len
        type = self.visit(expr.type, depth + shift)
        return Sig(tele, type)

    def visit_tuple(self, expr, *args, **kwargs):
        exprs = map(lambda x:self.visit(x, *args, **kwargs), expr.exprs)
        return Tuple(exprs)

    def visit_proj(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Proj(expr.index, sub_expr)        

    def visit_ev(self, expr, *args, **kwargs):
        tele = self.visit(expr.tele, *args, **kwargs)
        prop = self.visit(expr.prop, *args, **kwargs)
        return Ev(tele, prop)

    def visit_eq(self, expr, *args, **kwargs):
        lhs = self.visit(expr.lhs, *args, **kwargs)
        rhs = self.visit(expr.rhs, *args, **kwargs)
        return Eq(lhs, rhs)

    def visit_box(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        expr = self.visit(expr.expr, *args, **kwargs)
        type = self.visit(expr.type, *args, **kwargs)
        return Box(conv, expr, type)

    def visit_tele(self, expr, *args, **kwargs):
        types = []
        for i, e in enumerate(expr.types):
            abs_e = self.visit(e, depth + i)
            types.append(abs_e)

        return Tele(expr.vars, types)


def subst_expr(expr_list, expr):
    """Instanciate DB indices in expr according
    to expr_list
    
    Arguments:
    - `expr_list`: a list of expressions
    - `expr`: an expression
    """
    subster = SubstExpr(expr_list)
    return subster.visit(expr, 0)


def sub_in(substitutor, var, substitutee):
    """Replace constants with name var by substitutor
    in substitutee
    
    Arguments:
    - `substitutor`: an expression
    - `var`: a variable name
    - `substitutee`: an expression
    """
    return subst_expr([substitutor], abstract_expr([var], substitutee))



def pi(var, dom, codom):
    """Create the term
    Pi x:A.B from its constituents
    
    Arguments:
    - `var`: a variable name
    - `dom`: an expression
    - `codom`: an expression possibly containing var
    """
    codom_abs = abstract_expr([var], codom)
    return Bound(Pi(var), dom, codom)

def abs_expr(var, dom, expr):
    """Create the term
    lambda x:A.t from its constituents
    
    Arguments:
    - `var`: a variable name
    - `dom`: an expression
    - `expr`: an expression possibly containing var
    """
    expr_abs = abstract_expr([var], expr)
    return Bound(Abs(var), dom, expr)

def forall(var, dom, prop):
    """Create the term
    forall x:A.P from its constituents
    
    Arguments:
    - `var`: a variable name
    - `dom`: an expression
    - `prop`: an expression possibly containing var
    """
    prop_abs = abstract_expr([var], prop)
    return Bound(Forall(var), dom, codom)

def exists(var, dom, prop):
    """Create the term
    exists x:A.P from its constituents
    
    Arguments:
    - `var`: a variable name
    - `dom`: an expression
    - `prop`: an expression possibly containing var
    """
    prop_abs = abstract_expr([var], prop)
    return Exists(Exists(var), dom, codom)

