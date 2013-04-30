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

def empty_obl():
    """The empty proof obligation.
    Used to initialize the type inference.
    """
    return Obl()



