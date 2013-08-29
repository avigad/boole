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
from boole.core.tactics import Tactic, TacticFailure, \
     tac_from_fun, sub_goal, \
     now, par, trytac, simpl, trivial, repeat
import boole.core.tactics as tac
import elab


###############################################################################
#
# A class of Mvar stacks to manage backtracking
#
###############################################################################

class MvarStk(object):
    """A wrapper for a list of
    Mvar lists.
    The list represents a set of instanciations of meta-varaibles,
    which can be `undone` by freeing the variables involved in the last
    round of instanciations.
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


class unfold(tac.unfold):

    def __init__(self, *names):
        tac.unfold.__init__(self, *names)
        self.sub_in = elab.sub_in


class DestructMvar(tac.Destruct):
    
    def __init__(self, ):
        tac.Destruct.__init__(self)
        self.open_expr = elab.open_expr


destruct = DestructMvar()


def get_sub(goals):
    """Get the goals of the form T <= U from
    a list of goals
    
    Arguments:
    - `goals`: a list of goals
    """
    return filter(lambda g: g.prop.is_sub(), goals)


class OccursCheck(Exception):
    """Raised if there is an occurs check during unification
    """
    
    def __init__(self, mvar, term):
        """
        
        Arguments:
        - `mvar`: a meta-variable
        - `term`: an expression
        """
        Exception.__init__(self)
        self.mvar = mvar
        self.term = term
        


def split(mvar, goals):
    """Takes a list of constraints of the form
    T <= X, X <= U, and V <= W and seperates them into a triple of lists.
    
    Arguments:
    - `mvar`:
    - `goals`:
    """
    lt = []
    gt = []
    other = []
    for c in goals:
        assert(c.prop.is_sub())
        if c.prop.rhs is mvar:
            if not elab.mvar_is_present(c.prop.lhs, mvar):
                lt.append(c)
            else:
                raise OccursCheck(mvar, c.prop.lhs)
        elif c.prop.lhs is mvar:
            if not elab.mvar_is_present(c.prop.rhs, mvar):
                gt.append(c)
            else:
                raise OccursCheck(mvar, c.prop.rhs)
        else:
            other.append(c)
    return (lt, gt, other)


#TODO: compute the intersection of the two telescopes
def cross(l_goals, r_goals):
    """Takes a list of constraints T <= X and a list
    of constraints X <= U and returns the set of constraints
    T <= U for every U and T.
    We take the empty telescope.
    
    Arguments:
    - `l_goals`: a list of goals of the form T <= X
    - `r_goals`: a list of goals of the form X <= U
    """
    return [Goal(elab.nullctxt(), e.Sub(c.prop.lhs, d.prop.rhs))\
            for c in l_goals for d in r_goals]


def max_type(types, ctxt):
    """Get the maximum of a list of types. Since it
    can be undecidable to compare types in general, we
    take T <= U iff it can be proven using
    destruct >> trivial. Return None if no maximum is found.
    
    Arguments:
    - `types`: a list of types
    - `ctxt`: a goal context
    """
    for t in types:
        max_list = [Goals(elab.nullctxt(), e.Sub(u, t))\
                    for u in types]
        max_goal = Goals('max_goal', ctxt, goals=max_list)
        max_goal.solve_with(par(trivial))
        if max_goal.is_solved():
            return t
    return None


def min_type(types, ctxt):
    """Get the minimum of a list of types. Since it
    can be undecidable to compare types in general, we
    take T <= U iff it can be proven using
    destruct >> trivial. Return None if no minimum is found.
    
    Arguments:
    - `types`: a list of types
    - `ctxt`: a goal context
    """
    for t in types:
        min_list = [Goals(elab.nullctxt(), e.Sub(t, u))\
                    for u in types]
        min_goal = Goals('min_goal', ctxt, goals=min_list)
        min_goal.solve_with(par(trivial))
        if min_goal.is_solved():
            return t
    return None
    


class SolveMvars(Tactic):
    """Instanciate the meta-variables in a manner that satisfies the
    inequality constraints.
    Removes solved constraints from the
    goals. The base inequalities come from the global context only!
    """
    
    def __init__(self, ):
        Tactic.__init__(self, 'solve_mvars')

    def solve(self, goals, context):
        ineq_goals = Goals('sub', context, goals=get_sub(goals))
        #TODO: is this enough?
        ineq_goals.solve_with(par(repeat(par(destruct))) >> trivial)
        if ineq_goals.is_solved():
            return []
        else:
            ineqs = ineq_goals.goals
            c = ineqs[0]
            assert(c.is_sub())
            if not (c.lhs.is_mvar() or c.rhs.is_mvar()):
                mess = "Unsolvable constraint {0!s}".format(c)
                raise TacticFailure(self, mess)
            else:
                if c.lhs.is_mvar:
                    m = c.lhs
                else:
                    m = c.rhs
                assert(m.is_mvar())
                lt, gt, other = split(m, ineqs)
                m_elim = cross(lt, gt) + other
                self.solve(m_elim, context)
                raise NotImplemented()
                
                

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
                    mess = "No top-level meta-variable in {0!s}".format(goal.prop)
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


#FIXME: unsound with xi in empty domain
class mvar_apply(Tactic):
    """Takes a hypothesis of the form
    forall(x1,...,xn, implies([p1,... pn], p))
    and applies it to the goal r, generating
    the goal
    p[sub] <= r
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
            while hyp.is_forall():
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
        - `inst`: the name of an instance declaration
        """
        Tactic.__init__(self, 'instance {0!s}'\
                        .format(inst))
        self.inst = inst
        self.root = e.root_app(e.root_clause(inst))[0]

    def solve(self, goals, context):
        if len(goals) == 0:
            return []
        else:
            prop = goals[0].prop
            root, _ = e.root_app(prop)
            if root.info.is_class and self.root.equals(root):
                return mvar_apply(self.inst).solve(goals, context)
            else:
                mess = "Expression {0!s} is not an instance of {1!s}"\
                       .format(root, self.root)
                raise TacticFailure(mess, self, goals)


#TODO: succeed if only "complicated" goals remain, without
# uninstantiated Mvars.
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
            hyps = goals[0].tele.types
            hyp_insts = [i for i in hyps if e.root_app(i)[0].info.is_class]
            ctxt_insts = [i for i in context.class_instances.itervalues()]
            for inst in hyp_insts + ctxt_insts:
                try:
                    mvar_stack.new()
                    return now(par(sub_mvar)\
                               >> instance(inst)\
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
