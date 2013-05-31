#############################################################################
#
# constr.py
#
# description: constraints and goals in Boole
#
#
# Authors:
# Cody Roux
#
#
##############################################################################


import conv
import expr
from expr_base import fresh_name

##############################################################################
#
# The basic Goal objects
#
##############################################################################


class Goal(object):
    """The type of constraints: represents a proof obligation
    is constituted of a context (a telescope) and a
    boolean representing the proposition.
    """
    
    def __init__(self, tele, prop):
        """
        
        Arguments:
        - `tele`: a telescope
        - `prop`: a proposition
        - `context`: a context potentially containing additional information
        """
        self.tele = tele
        self.prop = prop
        
    def __str__(self):
        if len(self.tele) ==  0:
            tele_string = ""
        else:
            tele_string = str(self.tele)
        return "{0!s} |- {1!s}".format(tele_string, self.prop)



##############################################################################
#
# Tacics: they act as goal transformers, taking a Goal as input and
# returning a (possibly empty) list of new goals, or failing
#
##############################################################################


def sub_goal(tele, lhs, rhs):
    """Returns list containing the goal expressing
    lhs <= rhs in the context tele
    
    Arguments:
    - `tele`: a telescope
    - `lhs`: an expression
    - `rhs`: an expression
    """
    return [Goal(tele, expr.Sub(lhs, rhs))]


def eq_goal(tele, lhs, rhs):
    """Returns the list of goals expressing
    lhs <= rhs and rhs <= lhs
    
    Arguments:
    - `tele`: a telescope
    - `lhs`: an expression
    - `rhs`: an expression
    """
    return sub_goal(tele, lhs, rhs) + sub_goal(tele, rhs, lhs)


class TacticFailure(Exception):
    """Raised when a tactic fails
    """
    
    def __init__(self, mess, tactic, goal):
        """
        
        Arguments:
        - `mess`: the error message
        - `tactic`: the tactic which generated the error
        - `goal`: the goal on which the tactic failed
        """
        full_mess = "In tactic {0!s}:\n{1!s}".format(tactic.name, mess)
        Exception.__init__(self, full_mess)
        self.mess = mess
        self.tactic = tactic
        self.goal = goal


class Tactic(object):
    """The class of goal transformers
    """
    
    def __init__(self, name):
        self.name = name
        
    def solve(self, goal, context):
        """Takes a goal and returns a list of goals
        
        Arguments:
        - `goal`: an instance of the Goal class
        - `context`: a context
        """
        raise TacticFailure("Undefined tactic {0!s}"\
                            .format(self.name), self, goal)

    def __show__(self):
        return self.name

    def __rshift__(self, tac):
        """Compose two tactics
        
        Arguments:
        - `tac`: a tactic
        """
        return comp(self, tac)


class Trivial(Tactic):
    """Solve trivial goals. Checks if the
    goal is equal to true, and otherwise checks if it is a
    trivial equality, or is in the hypotheses.
    
    """
    
    def __init__(self):
        Tactic.__init__(self, 'trivial')

    def solve(self, goal, context):
        prop = goal.prop
        hyps = goal.tele
        if prop.is_const() and prop.name == "true":
            return []
        elif prop.is_sub():
            #try for pointer equality first.
            if prop.lhs is prop.rhs:
                return []
            elif prop.lhs.equals(goal.prop.rhs):
                return []

        for h in hyps.types:
            if h.equals(prop):
                return []
        glob_hyps = context.hyps
        for h in glob_hyps:
            if glob_hyps[h].equals(prop):
                return []
        return [goal]


trivial = Trivial()


class Simpl(Tactic):
    """Solve goals by performing beta-reduction,
    then calling trivial.

    """

    def __init__(self):
        Tactic.__init__(self, 'simpl')

    def solve(self, goal, context):
        prop = goal.prop
        simp_goal = Goal(goal.tele, conv.par_beta(prop))
        return trivial.solve(simp_goal, context)


simpl = Simpl()


class Destruct(Tactic):
    """Make progress on goals of the form
    A <= B by induction on the type structure
    """
    
    def __init__(self):
        Tactic.__init__(self, 'destruct')

    #TODO: refactor this code
    def solve(self, goal, context):
        prop = goal.prop
        tele = goal.tele
        if prop.is_sub():
            # Sig(x:A,B) <= Sig(x:C,D) is simplified
            # to A <= C and B(x) <= D(x)
            lhs = prop.lhs
            rhs = prop.rhs
            if lhs.is_bound() and lhs.binder.is_sig()\
                   and rhs.is_bound and rhs.binder.is_sig():
                lhs_dom = prop.lhs.dom
                rhs_dom = prop.rhs.dom
                fr_var = fresh_name.get_name(lhs.binder.var)
                lhs_codom = expr.open_expr(fr_var, lhs_dom, lhs.body)
                #The lhs domain must be a subtype of the rhs domain
                #for this expression to make sense
                rhs_codom = expr.open_expr(fr_var, lhs_dom, rhs.body)
                dom_goal = sub_goal(tele, lhs_dom, rhs_dom)
                codom_goal = sub_goal(tele, lhs_codom, rhs_codom)
                return dom_goal + codom_goal
            elif lhs.is_bound() and rhs.is_bound() and \
                     lhs.binder.is_pi() and rhs.binder.is_pi():
                # Pi(x:A, B) <= Pi(x:C, D) is simplified to
                # A <= C and C <= A and B(x) <= D(x)
                var = fresh_name.get_name(lhs.binder.var)
                codom_l = expr.open_expr(var, lhs.dom, lhs.expr)
                #We use the same domain here, as they must be equal
                # anyways
                codom_r = expr.open_expr(var, lhs.dom, rhs.expr)
                dom_goals = eq_goal(tele, lhs.dom, rhs.dom)
                codom_goal = sub_goal(tele, codom_l, codom_r)
                return dom_goals + codom_goal
            elif lhs.is_app() and rhs.is_app():
                fun_eq = eq_goal(tele, lhs.fun, rhs.fun)
                arg_eq = eq_goal(tele, lhs.arg, rhs.arg)
                return fun_eq + arg_eq
            else:
                mess = "{0!s} and {1!s} are not of the same form"\
                       .format(prop.lhs, prop.rhs)
                raise TacticFailure(mess, self, goal)
            
        else:
            mess = "Goal {0!s} is not of the form A<=B"\
                   .format(goal)
            raise TacticFailure(mess, self, goal)

destruct = Destruct()


class trytac(Tactic):
    """Takes a tactic as input, and returns the
    tactic that tries to apply tac and does
    nothing if it fails
    """
    
    def __init__(self, tac):
        """
        
        Arguments:
        - `tac`: a tactic
        """
        Tactic.__init__(self, 'try {0!s}'.format(tac))
        self.tac = tac

    def solve(self, goal, context):
        try:
            return self.tac.solve(goal, context)
        except TacticFailure:
            return [goal]


class trywith(Tactic):
    """Takes two tactics tac1 and tac2 and tries to apply
    t1, and if it fails applies t2.
    """
    
    def __init__(self, tac1, tac2):
        """
        
        Arguments:
        - `tac1`: a tactic
        - `tac2`: a tactic
        """
        Tactic.__init__(self, 'try {0!s} with {1!s}'.format(tac1, tac2))
        self.tac1 = tac1
        self.tac2 = tac2

    def solve(self, goal, context):
        try:
            return self.tac1.solve(goal, context)
        except TacticFailure:
            return self.tac2.solve(goal, context)


class comp(Tactic):
    """Take two tactics as input, and return the tactic that calls
    the first on the goal, and the second on the resulting sub-goals.
    """
    
    def __init__(self, tac1, tac2):
        self.tac1 = tac1
        self.tac2 = tac2
        Tactic.__init__(self, '({0!s} >> {1!s})'.format(tac1, tac2))
        
    def solve(self, goal, context):
        new_goals = self.tac1.solve(goal, context)
        return [g for g1 in new_goals for g in self.tac2.solve(g1, context)]


class repeat(Tactic):
    """Take a tactic, and repeatedly apply it to a goal until solved
    or it raises an exception.
    """
    
    def __init__(self, tac):
        Tactic.__init__(self, "repeat {0!s}".format(tac))
        self.tac = tac
        
    def solve(self, goal, context):
        goals = [goal]
        while len(goals) != 0:
            goals = [gtac for g in goals\
                     for gtac in self.tac.solve(g, context)]
        return goals

##############################################################################
#
# Goals are a list of atomic Goal objects, which can call solvers on
# that list to transform themselves destructively.
# They are defined within a context and have a name.
#
##############################################################################


class Goals(object):
    """The class of proof obligations. Simply maintains a list of
    goals. The empty obligation is considered solved.
    """
    
    def __init__(self, name, context):
        """a Goals object has a name, a context
        and a list of goals.
        """
        self.name = name
        self.goals = []
        self.context = context

    def append(self, goal):
        """Add a goal to the proof obligations
        
        Arguments:
        - `constr`:
        """
        self.goals.append(goal)

    def is_solved(self):
        """Returns true if there are no obligations left.
        """
        return (len(self.goals) == 0)

    def __str__(self):
        """
        """
        goal_str = "Goals `{0!s}`:\n".format(self.name)
        for i, g in enumerate(self.goals):
            goal_str += "({0!s}) : {1!s}\n".format(i, g)
        return goal_str

    def __len__(self, ):
        return len(self.goals)

    def solve_with(self, tactic):
        """Remove the obligations which can
        be proven with the method.
        
        Arguments:
        - `tactic`: an instance of Tactic
        """
        new_goals = [g_new for g in self.goals\
                     for g_new in tactic.solve(g, self.context)]
        self.goals = new_goals


def empty_goals(name, context):
    """The empty proof obligation.
    Used e.g. to initialize the type inference.
    """
    return Goals(name, context)
