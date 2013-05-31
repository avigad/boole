#############################################################################
#
# unif.py
#
# description: unification constraint solving
#
#
# Authors:
# Cody Roux
#
#
##############################################################################

import boole.core.expr as e
from boole.core.goals import *
import boole.core.info as info
import elab

###############################################################################
#
# Exceptions for unification
#
###############################################################################


class UnifError(Exception):
    """Unification errors.
    """
    
    def __init__(self, mess, expr):
        """
        
        Arguments:
        - `mess`: the error message
        - `expr`: the expression that gave rise to the error
        """
        Exception.__init__(self, mess)
        self.mess = mess
        self.expr = expr


###############################################################################
#
# Utility functions for subtituting or locating an mvar in a term.
#
###############################################################################

class SubMvar(e.ExprVisitor):
    """Replace all meta-variables by their
    value in a term.
    
    Arguments:
    - `undef`: if this flag is set to True,
    fail on unresolved meta-vars.
    """
    
    def __init__(self, undef=None):
        e.ExprVisitor.__init__(self)
        self.undef = undef
        
    def visit_const(self, expr):
        return expr

    def visit_db(self, expr):
        return expr

    def visit_type(self, expr):
        return expr

    def visit_kind(self, expr):
        return expr

    def visit_bool(self, expr):
        return expr

    def visit_bound(self, expr):
        dom = self.visit(expr.dom)
        body = self.visit(expr.body)
        return e.Bound(expr.binder, dom, body)

    def visit_app(self, expr):
        conv = self.visit(expr.conv)
        fun = self.visit(expr.fun)
        arg = self.visit(expr.arg)
        return e.App(conv, fun, arg)

    def visit_pair(self, expr):
        fst = self.visit(expr.fst)
        snd = self.visit(expr.snd)
        type = self.visit(expr.type)
        return e.Pair(fst, snd, type)

    def visit_fst(self, expr):
        return e.Fst(self.visit(expr.expr))

    def visit_snd(self, expr):
        return e.Snd(self.visit(expr.expr))

    def visit_ev(self, expr):
        return e.Ev(self.visit(expr.tele))

    def visit_sub(self, expr):
        lhs = self.visit(expr.lhs)
        rhs = self.visit(expr.rhs)
        return e.Sub(lhs, rhs)

    def visit_box(self, expr):
        conv = self.visit(expr.conv)
        expr1 = self.visit(expr.expr)
        type = self.visit(expr.type)
        return e.Box(conv, expr1, type)

    def visit_tele(self, expr):
        types = [self.visit(t) for t in expr.types]
        return e.Tele(expr.vars, types)

    def visit_mvar(self, expr):
        if expr.value is None:
            if self.undef == None:
                return expr
            else:
                mess = "Cannot find a value for {0!s}".format(expr)
                raise UnifError(mess, expr)
        else:
            return expr.value

    @info.same_info
    def visit(self, expr, *args, **kwargs):
        return expr.accept(self, *args, **kwargs)


def sub_mvar(expr, undef=None):
    """Replace all meta-variables by their
    value in a term.
    
    Arguments:
    - `undef`: if this flag is set to True,
    fail on unresolved meta-vars.
    """
    return SubMvar(undef=undef).visit(expr)


class MvarIsPresent(e.ExprVisitor):
    """Determine if a meta-variable name is present in a term.
    """
    
    def __init__(self, name=None):
        e.ExprVisitor.__init__(self)
        self.name = name
        
    def visit_const(self, expr):
        pass

    def visit_db(self, expr):
        pass

    def visit_type(self, expr):
        pass

    def visit_kind(self, expr):
        pass

    def visit_bool(self, expr):
        return expr

    def visit_bound(self, expr):
        self.visit(expr.dom)
        self.visit(expr.codom)

    def visit_app(self, expr):
        self.visit(expr.conv)
        self.visit(expr.fun)
        self.visit(expr.arg)

    def visit_pair(self, expr):
        self.visit(expr.fst)
        self.visit(expr.snd)
        self.visit(expr.type)

    def visit_fst(self, expr):
        self.visit(expr.expr)

    def visit_snd(self, expr):
        self.visit(expr.expr)

    def visit_ev(self, expr):
        self.visit(expr.tele)

    def visit_sub(self, expr):
        self.visit(expr.lhs)
        self.visit(expr.rhs)

    def visit_box(self, expr):
        self.visit(expr.conv)
        self.visit(expr.expr)
        self.visit(expr.type)

    def visit_tele(self, expr):
        for t in expr.types:
            self.visit(t)

    def visit_mvar(self, expr):
        if self.name != None:
            if expr.name == self.name:
                return True
        else:
            return True


def mvar_is_present(expr, mvar=None):
    if MvarIsPresent(name=mvar.name).visit(expr):
        return True
    else:
        return False


###############################################################################
#
# Tactics for solving unification-type goals
#
###############################################################################

class SubMvarGoal(Tactic):
    """Substitute all the meta-variables in the
    goal and the telescope
    """
    
    def __init__(self):
        Tactic.__init__(self, 'sub_mvar_goal')

    def solve(self, goal, context):
        tele = sub_mvar(goal.tele)
        prop = sub_mvar(goal.prop)
        return [Goal(tele, prop)]

sub_mvar_goal = SubMvarGoal()


class SolveMvar(Tactic):
    """If a goal is of the form X <= T
    or T <= X, with X not in T, give the value
    T to the meta-variable X.
    """
    
    def __init__(self):
        Tactic.__init__(self, 'solve_mvar')

    def solve(self, goal, context):
        """
        
        Arguments:
        - `goal`:
        - `context`:
        """
        prop = goal.prop
        if prop.is_sub():
            if isinstance(prop.lhs, elab.Mvar):
                mvar = prop.lhs
                tm = prop.rhs
                if not mvar_is_present(tm, mvar):
                    mvar.set_val(tm)
                    return []
                else:
                    mess = "occurs check: the variable {0!s} occurs in {1!s}"\
                    .format(mvar, tm)
                    raise TacticFailure(mess, self, goal)
                    
            elif isinstance(prop.rhs, elab.Mvar):
                mvar = prop.rhs
                tm = prop.lhs
                if not mvar_is_present(tm, mvar):
                    mvar.set_val(tm)
                    return []
                else:
                    mess = "occurs check: the variable {0!s} occurs in {1!s}"\
                    .format(mvar, tm)
                    raise TacticFailure(mess, self, goal)
                
            else:
                mess = "No top-level meta-variable in {0!s}".format(goal)
                raise TacticFailure(mess, self, goal)


solve_mvar = SolveMvar()

###############################################################################
#
# The main tactic for solving constraints with meta-vars
#
###############################################################################

# solve_mvars = sub_mvar_goal >> trywith(solve_mvar, trytac(destruct))

solve_mvars = sub_mvar_goal >> trivial >> trywith(solve_mvar, destruct)
