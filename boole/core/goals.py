#############################################################################
#
# goals.py
#
# description: constraints and goals in Boole
#
#
# Authors:
# Cody Roux
#
#
##############################################################################


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
        """
        self.tele = tele
        self.prop = prop
        
    def __str__(self):
        if len(self.tele) == 0:
            tele_string = ""
        else:
            tele_list = zip(self.tele.vars, self.tele.types)
            tele_str_list = ["{0!s} : {1!s}".format(v, t)\
                             for v, t in tele_list]
            tele_string = "\n".join(tele_str_list)
        sep = '----------------------------------'
        return "{0!s}\n{1!s}\n{2!s}".format(tele_string, sep, self.prop)

    def __getitem__(self, hyp_name):
        """Returns the hypothesis with name
        hyp_name
        
        Arguments:
        - `hyp_name`: a string
        """
        i = self.tele.vars.index(hyp_name)
        return self.tele.types[i]
    

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
    
    def __init__(self, name, context, goals=None):
        """a Goals object has a name, a context
        and a list of goals.
        history is the list of pairs of previous goals and tactics.
        """
        self.name = name
        if goals is None:
            self.goals = []
        else:
            self.goals = goals
        self.context = context
        #TODO: use LIFO Queues?
        self.history = []

    def append(self, goal):
        """Add a goal to the proof obligations
        
        Arguments:
        - `constr`:
        """
        self.goals.append(goal)

    def __str__(self):
        """
        """
        goal_str = "Goals `{0!s}`:\n".format(self.name)
        if self.is_solved():
            return "No remaining goals!\n"
        else:
            for i, g in enumerate(self.goals):
                goal_str += "({0!s}) :\n{1!s}\n\n".format(i, g)
            return goal_str

    def __len__(self):
        return len(self.goals)

    def __getitem__(self, i):
        return self.goals[i]

    def is_solved(self):
        """Returns true if there are no obligations left.
        """
        return (len(self.goals) == 0)

    def solve_with(self, tactic):
        """Remove the obligations which can
        be proven with the method.
        
        Arguments:
        - `tactic`: an instance of Tactic
        """
        self.history.append((self.goals, tactic))
        self.goals = tactic.solve(self.goals, self.context)

    def interact(self, tactic):
        """Apply the tactic and print the goal
        
        Arguments:
        - `tactic`:
        """
        self.solve_with(tactic)
        print self

    def undo(self):
        """Revert to the previous goal state.
        """
        if not self.history:
            raise ValueError('No undo state!')
        else:
            g, _ = self.history.pop()
            self.goals = g

def empty_goals(name, context):
    """The empty proof obligation.
    Used e.g. to initialize type inference.
    """
    return Goals(name, context)
