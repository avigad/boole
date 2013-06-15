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


class DestructMvar(Destruct):
    
    def __init__(self, ):
        Destruct.__init__(self)
        self.open_expr = elab.open_expr


destruct = DestructMvar()


class ClearMvar(Tactic):
    """Clear the values of all the meta-variables in the goal and
    telescope
    """
    
    def __init__(self):
        Tactic.__init__(self, 'clear_mvar')

    def solve(self, goal, context):
        tele = elab.clear_mvar(goal.tele)
        prop = elab.clear_mvar(goal.prop)
        return [Goal(tele, prop)]
        

clear_mvar = ClearMvar()


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


#TODO: unsound with xi in empty domain
class mvar_apply(Tactic):
    """Takes a hypothesis of the form
    forall(x1,...,xn, p1 ==> ... pn ==> p)
    and applies it to the goal r, generating
    the goal
    p[sub] ==> r
    with [sub] sending each xi to a fresh meta-variable.
    """
    
    def __init__(self, hyp):
        Tactic.__init__(self, 'mvar_apply')
        self.hyp = hyp

    def solve(self, goal, context):
        prop = goal.prop
        hyps = goal.tele
        hyp = self.hyp
        while hyp.is_bound() and hyp.binder.is_forall():
            _, hyp = elab.mvar_open_bound_fresh(hyp)
        new_goals = []
        #TODO: add requirement that hyp.lhs is a Bool
        while hyp.is_sub():
            new_goals.append(Goal(hyps, hyp.lhs))
            hyp = hyp.rhs
        return sub_goal(hyps, hyp, prop) + new_goals


def mvar_unif(hyp):
    return mvar_apply(hyp) >> repeat(unif_step)


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
                return mvar_unif(inst_ty).solve(goal, context)
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
                clear_mvar.solve(goal, context)
        mess = "No class instances for goal {0!s}".format(goal)
        raise TacticFailure(mess, self, goal)

instances = Instances()

###############################################################################
#
# The main tactics for solving constraints with meta-vars
#
###############################################################################


unif_step = sub_mvar >> trivial >> (solve_mvar | destruct)


def resolve(k):
    return now(trytac(instance(k)) >> unify)

# unif_step = sub_mvar >> trivial >> (solve_mvar | instances | destruct)

unify = repeat(unif_step)


def resolve_goals(g):
    """Call resolve for each possible type-class and try to
    solve the proof obligations
    
    Arguments:
    - `g`: an instance of the goal class
    """
    insts = g.context.class_instances
    # g.solve_with(unify)
    for k in insts:
        try:
            g.solve_with(resolve(k))
            break
        except TacticFailure:
            g.solve_with(clear_mvar)
    g.solve_with(unify)
