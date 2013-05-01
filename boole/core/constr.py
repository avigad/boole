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


class Constr(object):
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
        return "{0!s} |- {1!s}".format(self.tele, self.prop)

    #TODO: rewrite this whole approach.
    def solve_with(self, method):
        """Attempt to determine if the constraint is true, using
        a given method. Returns a boolean.
        
        Arguments:
        - `method`: a string describing the method
        """
        if method == "trivial":
            if self.prop.is_const() and self.prop.name == "true":
                return True
            elif self.prop.is_eq():
                return self.prop.lhs.equals(self.prop.rhs)
            else:
                return False
        else:
            raise Exception("Unknown solver: {0!s}".format(method))
        




class Obl(object):
    """The class of proof obligations. Simply maintains a list of
    goals. The empty obligation is considered solved.
    """
    
    def __init__(self):
        """
        """
        self.goals = []


    def append(self, constr):
        """Add a constraint to the proof obligations
        
        Arguments:
        - `constr`:
        """
        self.goals.append(constr)

    def is_solved(self, ):
        """Returns true if there are no obligations left.
        """
        return (len(self.goals) == 0)

    def __str__(self, ):
        """
        """
        goal_str = ""
        for i, g in enumerate(self.goals):
            goal_str += "({0!s}) : {1!s}\n".format(i, g)
        return goal_str

    def solve_with(self, method):
        """Remove the obligations which can
        be proven with the method.
        
        Arguments:
        - `method`:
        """
        new_goals = []
        for g in self.goals:
            if g.solve_with(method):
                pass
            else:
                new_goals.append(g)
                
        self.goals = new_goals


def empty_obl():
    """The empty proof obligation.
    Used to initialize the type inference.
    """
    return Obl()
