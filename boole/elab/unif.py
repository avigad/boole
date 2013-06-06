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
# Tactics for solving unification goals
#
###############################################################################

class SubMvar(Tactic):
    """Substitute all the meta-variables in the
    goal and the telescope
    """
    
    def __init__(self):
        Tactic.__init__(self, 'sub_mvar')

    def solve(self, goal, context):
        tele = elab.sub_mvar(goal.tele)
        prop = elab.sub_mvar(goal.prop)
        return [Goal(tele, prop)]

sub_mvar = SubMvar()


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
                if not elab.mvar_is_present(tm, mvar):
                    mvar.set_val(tm)
                    return []
                else:
                    mess = "occurs check: the variable {0!s} occurs in {1!s}"\
                    .format(mvar, tm)
                    raise TacticFailure(mess, self, goal)
                    
            elif isinstance(prop.rhs, elab.Mvar):
                mvar = prop.rhs
                tm = prop.lhs
                if not elab.mvar_is_present(tm, mvar):
                    mvar.set_val(tm)
                    return []
                else:
                    mess = "occurs check: the variable {0!s} occurs in {1!s}"\
                    .format(mvar, tm)
                    raise TacticFailure(mess, self, goal)
                
            else:
                mess = "No top-level meta-variable in {0!s}".format(goal)
                raise TacticFailure(mess, self, goal)
        else:
            mess = "Goal {0!s} is not a disequality".format(goal)
            raise TacticFailure(mess, self, goal)


solve_mvar = SolveMvar()


class mvar_apply(Tactic):
    """Generate an equality between the current goal
    and the hypothesis and apply the unification tactic.
    """
    
    def __init__(self, hyp):
        """
        
        Arguments:
        - `hyp`: a term of type bool
        """
        Tactic.__init__(self, 'mvar_apply {0!s}'.format(hyp))
        self.hyp = hyp

    def solve(self, goal, context):
        tele = goal.tele
        prop = goal.prop
        unif_pb = Goal(tele, e.Sub(self.hyp, prop))
        return repeat(unif_step, fail=True).solve(unif_pb, context)


class instance(Tactic):
    """Generate an equality between the current goal of the form
    ClassName(t1,..,tn) and an instance inst of that class. fail if the
    goal is of the incorrect form or if no such instances exist.
    """
    
    def __init__(self, inst):
        """
        
        Arguments:
        - `cls`: the name of a type class
        - `inst`: the name of an instance declaration
        """
        Tactic.__init__(self, 'instance {0!s}'\
                        .format(inst))
        self.inst = inst

    def solve(self, goal, context):
        prop = goal.prop
        root, _ = e.root_app(prop)
        if root.info.is_class:
            if self.inst in context.class_instances:
                inst_ty = context.class_instances[self.inst]
                return mvar_apply(inst_ty).solve(goal, context)
            else:
                mess = "Instance {0!s} not found in context {1!s}"\
                       .format(self.inst, context)
                raise TacticFailure(mess, self, goal)
        else:
            mess = "Expression {0!s} is not a class"\
                   .format(root)
            raise TacticFailure(mess, self, goal)


class Instances(Tactic):
    """Tries to apply every instance in the context,
    and fails if none solve the goal.
    """
    
    def __init__(self):
        Tactic.__init__(self, "instances")

    def solve(self, goal, context):
        insts = context.class_instances
        for k in insts:
            try:
                return now(instance(k)).solve(goal, context)
            except TacticFailure:
                pass
        mess = "No class instances for goal {0!s}".format(goal)
        raise TacticFailure(mess, self, goal)

instances = Instances()

###############################################################################
#
# The main tactics for solving constraints with meta-vars
#
###############################################################################


unif_step = sub_mvar >> trivial >> (solve_mvar | instances | destruct)

unify = repeat(unif_step)
