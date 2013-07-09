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
from boole.core.tactics import *
import elab


###############################################################################
#
# A class of Mvar stacks to manage backtracking
#
###############################################################################

class MvarStk(object):
    """A wrapper for a list of
    Mvar lists.
    """
    
    def __init__(self):
        self.stacks = []
        
    def new(self):
        """Add a stack to the list
        """
        self.stacks.append([])

    def free(self):
        """Remove the assignment of all meta-variables
        in the last stack, then remove it.
        """
        for exp in self.stacks[-1]:
            exp.clear()
        self.stacks = self.stacks[:-1]

    def push(self, mv):
        """Add a meta-variable to the last
        stack
        
        Arguments:
        - `mv`: a Mvar
        """
        self.stacks[-1].append(mv)

    def clear(self):
        """Clear the whole stack of stacks.
        """
        self.stacks = []


mvar_stack = MvarStk()

###############################################################################
#
# Tactics for solving unification goals
#
###############################################################################


def sub_fun(goal, context):
    """Substitute all the meta-variables in the
    goal and the telescope
    """
    tele = elab.sub_mvar(goal.tele)
    prop = elab.sub_mvar(goal.prop)
    return [Goal(tele, prop)]

sub_mvar = tac_from_fun('sub_mvar', sub_fun)


class DestructMvar(Destruct):
    
    def __init__(self, ):
        Destruct.__init__(self)
        self.open_expr = elab.open_expr


destruct = DestructMvar()


class SolveMvar(Tactic):
    """If a goal is of the form X <= T
    or T <= X, with X not in T, give the value
    T to the meta-variable X.
    """
    
    def __init__(self):
        Tactic.__init__(self, 'solve_mvar')

    def solve(self, goals, context):
        """
        
        Arguments:
        - `goal`:
        - `context`:
        """
        if len(goals) == 0:
            return []
        else:
            goal, tail = (goals[0], goals[1:])
            prop = goal.prop
            if prop.is_sub():
                if isinstance(prop.lhs, elab.Mvar):
                    mvar = prop.lhs
                    tm = prop.rhs
                elif isinstance(prop.rhs, elab.Mvar):
                    mvar = prop.rhs
                    tm = prop.lhs
                else:
                    mess = "No top-level meta-variable in {0!s}".format(goal)
                    raise TacticFailure(mess, self, goals)
                if not elab.mvar_is_present(tm, mvar):
                    mvar.set_val(tm)
                    mvar_stack.push(mvar)
                    return tail
                else:
                    mess = "occurs check: the variable {0!s} occurs in {1!s}"\
                           .format(mvar, tm)
                    raise TacticFailure(mess, self, goals)
            else:
                mess = "Goal {0!s} is not a disequality".format(goal)
                raise TacticFailure(mess, self, goals)


solve_mvar = SolveMvar()


#TODO: unsound with xi in empty domain
class mvar_apply(Tactic):
    """Takes a hypothesis of the form
    forall(x1,...,xn, p1 >= ... pn >= p)
    and applies it to the goal r, generating
    the goal
    p[sub] >= r
    with [sub] sending each xi to a fresh meta-variable.
    """
    
    def __init__(self, hyp):
        Tactic.__init__(self, 'mvar_apply')
        self.hyp = hyp

    def solve(self, goals, context):
        if len(goals) == 0:
            return []
        else:
            goal, tail = (goals[0], goals[1:])
            prop = goal.prop
            hyps = goal.tele
            hyp = self.hyp
            while hyp.is_bound() and hyp.binder.is_forall():
                _, hyp = elab.mvar_open_bound_fresh(hyp)
            new_goals = []
            while e.is_impl(hyp):
                new_goals.append(Goal(hyps, e.arg_i(hyp, 0)))
                hyp = e.arg_i(hyp, 1)
            return sub_goal(hyps, hyp, prop) + new_goals + tail


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

    def solve(self, goals, context):
        if len(goals) == 0:
            return []
        else:
            prop = goals[0].prop
            root, _ = e.root_app(prop)
            if root.info.is_class:
                if self.inst in context.class_instances:
                    inst_ty = context.class_instances[self.inst]
                    return mvar_apply(inst_ty).solve(goals, context)
                else:
                    mess = "Instance {0!s} not found in context {1!s}"\
                           .format(self.inst, context)
                    raise TacticFailure(mess, self, goals)
            else:
                mess = "Expression {0!s} is not a class"\
                       .format(root)
                raise TacticFailure(mess, self, goals)


class Instances(Tactic):
    """Recusively tries to apply every instance in the context,
    and fails if none solve the goal.
    """
    
    def __init__(self):
        Tactic.__init__(self, "instances")

    def solve(self, goals, context):
        if len(goals) == 0:
            return []
        else:
            insts = context.class_instances
            for k in insts:
                try:
                    mvar_stack.new()
                    return now(par(sub_mvar)\
                               >> instance(k)\
                               >> par(unify)\
                               >> par(trytac(self))\
                               >> par(unify))\
                           .solve(goals, context)
                except TacticFailure:
                    mvar_stack.free()
            goal_str = map(str, goals)
            mess = "No class instances for goal {0!s}".format(goal_str)
            raise TacticFailure(mess, self, goals)

instances = Instances()

###############################################################################
#
# The main tactics for solving constraints with meta-vars
#
###############################################################################


unif_step = sub_mvar >> simpl(elab.par_beta) >> par(trivial) >> (solve_mvar | destruct)


unify = repeat(unif_step)
