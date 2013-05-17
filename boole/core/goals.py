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
        #TODO: should this be a telescope?
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
        Exception.__init__(self, mess)
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
        raise TacticFailure("Undefined tactic", self, goal)
        

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
