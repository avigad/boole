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




##############################################################################
#
# Miscellaneous useful procedures
#
##############################################################################




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
        fresh = "{0!s}_{0!s}".format(pad, self._index)
        self._index += 1
        return fresh


fresh_name = FreshGen()



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

class Expr(object):
    """The class of types and expressions.
    """

    def __init__(self):
        """
        """
        pass

    def accept(self, visitor, *args, **kwargs):
        """

        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        raise NotImplementedError()

    def __str__(self):
        """Representation of an expression
        """
        return "<abstr>"

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


class Const(Expr):
    """A constant declaration. Variables
    and constants are identified.
    """

    def __init__(self, name, type, checked = False):
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
        self.checked = checked

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_const(self, *args, **kwargs)

    def __str__(self):
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
        return visitor.visit_db(self, *args, **kwargs)

    def __str__(self):
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

    def __str__(self):
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

    def __str__(self):
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

    def __str__(self):
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
    
    def __init__(self, binder, dom, expr):
        """
        
        Arguments:
        - `binder`: an element of the Binder class
        - `dom`: an expression denoting the domain of the variable
        - `expr`: an expression
        """
        Expr.__init__(self)
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
        return visitor.visit_bound(self, *args, **kwargs)

    def __str__(self):
        # Printing a bound expression involves
        # substituting the DB index by a constant
        # with the appropriate name.
        var = Const(self.binder.var, self.dom)
        open_expr = subst_expr([var], self.expr)
        return "{0!s}({1!s},{2!s},{3!s})".format(\
            self.binder.name, self.binder.var, self.dom, open_expr)

    def is_bound(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_bound() and (self.binder.name == expr.binder.name):
            return self.dom.equals(expr.dom) and self.expr.equals(expr.expr)
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

    def __str__(self):
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


class Sig(Expr):
    """Sigma types, takes a telescope as argument
    """
    
    def __init__(self, telescope):
        """
        
        Arguments:
        - `telescope`: A telescope of types.
        - `type`: A term which may depend on elements of the
        telescope. Binds n variables where n is the length of the
        telescope.
        """
        Expr.__init__(self)
        self.telescope = telescope

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_sig(self, *args, **kwargs)

    def __str__(self):
        #same deal as for bound expressions, the variables from
        # the telescope are substituted into the types that
        # depend on them.
        # TODO: this function is an ugly hack. Please rewrite.
        named_tel = open_tele_with_default(self.telescope)
        vars = []
        for (x, _) in named_tel:
            vars.append(x)
            
        def str_decl(d):
            return '({0!s}, {1!s})'.format(d[0], d[1])
        tel = ','.join(map(str_decl, named_tel))
        return "sig([{0!s}])".format(tel)

    def is_sig(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_sig():
            return self.telescope.equals(expr.telescope)
        else:
            return False

    def __len__(self):
        return len(self.telescope)


class Tuple(Expr):
    """Elements of Sigma types. Need to carry around their type.
    """
    
    def __init__(self, exprs, type):
        """
        
        Arguments:
        - `type`: an expression
        - `exprs`: a list of expressions
        """
        Expr.__init__(self)
        self.exprs = exprs
        self.type = type        

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_tuple(self, *args, **kwargs)

    def __str__(self):
        expr_str = map(str, self.exprs)
        expr_str = ','.join(expr_str)
        return "Tuple([{0!s}],{1!s})".format(expr_str, self.type)
        
    def is_tuple(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_tuple():
            eq_info = [e1.equals(e2) for (e1, e2) in\
                       zip(self.exprs, expr.exprs)]
            return reduce(lambda x, y: x and y, eq_info, True)
        else:
            return False



class Proj(Expr):
    """Projections for Sigma types
    """
    
    def __init__(self, index, expr):
        """
        
        Arguments:
        - `index`: an integer
        - `expr`: the expression to which is applied the projection.
        """
        Expr.__init__(self)
        self.index = index
        self.expr = expr

    def accept(self, visitor, *args, **kwargs):
        """
    
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_proj(self, *args, **kwargs)

    def __str__(self):
        """
        
        Arguments:
        - `self`:
        """
        return "Proj({0!s}, {1!s})".format(self.index, self.expr)

    def is_tuple(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_proj():
            return (self.index == expr.index) and (self.expr.equals(expr.expr))
        else:
            return False


class Ev(Expr):
    """Evidence type: provides evidence for a
    proposition (of type Bool)
    """
    
    def __init__(self, telescope):
        """
        
        Arguments:
        - `telescope`: a telescope of evidence for the proposition
        prop.
        - `prop`: a proposition whose evidence is supplied by self.
        binds NO variables.
        """
        Expr.__init__(self)
        self.telescope = telescope
        
    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_ev(self, *args, **kwargs)

    def __str__(self):
        return "Ev({0!s})".format(self.telescope)

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
        Expr.__init__(self)
        self.lhs = expr1
        self.rhs = expr2

    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_eq(self, *args, **kwargs)

    def __str__(self):
        """
        
        Arguments:
        - `self`:
        """
        return "{0!s} == {1!s}".format(self.lhs, self.rhs)

    def is_eq(self):
        return True

    def equals(self, expr):
        """Structural equality.
        
        Arguments:
        - `expr`: an expression
        """
        if expr.is_eq():
            return (self.lhs.equals(expr.lhs)) and (self.rhs.equals(expr.rhs))
        else:
            return False


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

    def __str__(self):
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
# The class of 1 variable binders: this includes Pi, Abst, forall/exists
# but excludes Sig.
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


class Pi(Binder):
    """Dependent product
    """
    
    def __init__(self, var):
        Binder.__init__(self, var)
        self.name = "pi"
        
    def is_pi(self):
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
        assert(len(self.vars) == self.len)


    def accept(self, visitor, *args, **kwargs):
        """
        
        Arguments:
        - `visitor`:
        - `*args`:
        - `**kwargs`:
        """
        return visitor.visit_tele(self, *args, **kwargs)


    def __str__(self):
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
            eq_info = [ t1.equals(t2) for (t1, t2) in zip(self.types, tele.types)]
            return reduce(lambda x, y: x and y, eq_info, True)
        else:
            return False

    def __len__(self):
        return self.len


def open_tele(tele, vars, checked=False):
    """Takes a telescope and returns a list of pairs
    (constant, type) where the subsequent types may depend
    on the constant.
    
    Arguments:
    - `tele`:
    """
    opened_ty = tele.types
    consts = []
    for i in range(0, tele.len):
        opened_ty[i] = subst_expr(consts, opened_ty[i])
        x = Const(vars[i], opened_ty[i], checked=checked)
        consts.append(x)
    return zip(consts, opened_ty)

def open_tele_with_default(tele):
    """Open a telescope with the default variables provided by
    the telescope definition.
    
    Arguments:
    - `tele`: a telescope
    """
    return open_tele(tele, tele.vars)


def open_tele_with_fresh(tele, checked=False):
    """Open a telescope with fresh variables
    
    Arguments:
    - `tele`: a telescope
    """
    fr_vars = [fresh_name.get_name(name = v) for v in tele.vars]
    return open_tele(tele, fr_vars, checked=checked)


###############################################################################
#
# The visitor class for Expr and Tele
#
###############################################################################

class ExprVisitor(object):
    """
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

    def visit_sig(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_tuple(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_proj(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_ev(self, expr, *args, **kwargs):
        raise NotImplementedError()

    def visit_eq(self, expr, *args, **kwargs):
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
            return DB(index)
        else:
            return Const(expr.name, expr.type)
            

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
        return Sig(tele)

    def visit_tuple(self, expr, *args, **kwargs):
        type = self.visit(expr.type, *args, **kwargs)
        exprs = [self.visit(x, *args, **kwargs) for x in expr.exprs]
        return Tuple(exprs, type)

    def visit_proj(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Proj(expr.index, sub_expr)

    def visit_ev(self, expr, *args, **kwargs):
        tele = self.visit(expr.tele, *args, **kwargs)
        return Ev(tele)

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
    instantiate the DB indices 1,...,n with those
    terms.
    """
    
    def __init__(self, exprs):
        """
        
        Arguments:
        - `exprs`: the expressions to instanciate.
        """
        ExprVisitor.__init__(self)
        self.exprs = exprs
        self.len = len(self.exprs)
        
    def visit_const(self, expr, *args, **kwargs):
        return Const(expr.name, expr.type)

    def visit_db(self, expr, depth):
        if expr.index < depth:
            return DB(expr.index)
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
        return Bound(expr.binder, dom, b_expr)

    def visit_app(self, expr, *args, **kwargs):
        conv = self.visit(expr.conv, *args, **kwargs)
        fun = self.visit(expr.fun, *args, **kwargs)
        arg = self.visit(expr.arg, *args, **kwargs)
        return App(conv, fun, arg)

    def visit_sig(self, expr, depth):
        tele = self.visit(expr.telescope, depth)
        return Sig(tele)

    def visit_tuple(self, expr, *args, **kwargs):
        type = self.visit(expr.type, *args, **kwargs)
        exprs = [self.visit(x, *args, **kwargs) for x in expr.exprs]
        return Tuple(exprs, type)

    def visit_proj(self, expr, *args, **kwargs):
        sub_expr = self.visit(expr.expr, *args, **kwargs)
        return Proj(expr.index, sub_expr)

    def visit_ev(self, expr, *args, **kwargs):
        tele = self.visit(expr.tele, *args, **kwargs)
        return Ev(tele)

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
        types = []
        for i, e in enumerate(expr.types):
            abs_e = self.visit(e, depth + i)
            types.append(abs_e)

        return Tele(expr.vars, types)


def subst_expr(exprs, expr):
    """Instanciate DB indices in expr according
    to expr_list
    
    Arguments:
    - `expr_list`: a list of expressions
    - `expr`: an expression
    """
    subster = SubstExpr(exprs)
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
    - `var`: a constant expr
    - `dom`: an expression
    - `codom`: an expression possibly containing var
    """
    name = var.name
    codom_abs = abstract_expr([name], codom)
    return Bound(Pi(name), dom, codom_abs)

def abst(var, dom, expr):
    """Create the term
    lambda x:A.t from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `dom`: an expression
    - `expr`: an expression possibly containing var
    """
    name = var.name
    expr_abs = abstract_expr([name], expr)
    return Bound(Abst(name), dom, expr_abs)

def forall(var, dom, prop):
    """Create the term
    forall x:A.P from its constituents
    
    Arguments:
    - `var`: a constant expr
    - `dom`: an expression
    - `prop`: an expression possibly containing var
    """
    name = var.name
    prop_abs = abstract_expr([name], prop)
    return Bound(Forall(name), dom, prop_abs)

def exists(var, dom, prop):
    """Create the term
    exists x:A.P from its constituents
    
    Arguments:
    - `var`: a variable name
    - `dom`: an expression
    - `prop`: an expression possibly containing var
    """
    name = var.name
    prop_abs = abstract_expr([name], prop)
    return Exists(Exists(name), dom, prop_abs)


def sig(*tele_var):
    """Create the term
    Sig(tele)
    using the named telescope tele_var
    
    Arguments:
    - `tele_var`: a list of pairs of contants and
    expressions.
    - `type`: an expression
    """
    # a bit risky: requires the expressions to be
    # free of "dangling" DB indices.
    # also: syntax is atrocious.
    vars = []
    types = []
    for (x, e) in tele_var:
        vars.append(x)
        types.append(e)
    names = [x.name for x in vars]
    types = [abstract_expr(names, e) for e in types]
    return Sig(Tele(names, types))


def true():
    """The true constant.
    """
    return Const('true', Bool())


def false():
    """The true constant.
    """
    return Const('false', Bool())


if __name__ == '__main__':


    unit = sig()

    dummy = Const('_', unit)

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

    
