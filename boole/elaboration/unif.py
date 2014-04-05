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
import boole.elaboration.elab as elab
import boole.core.conv as conv


###############################################################################
#
# Possible exceptions during unification
#
###############################################################################


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


class UnsolvabeConstr(Exception):
    """Raised if an equality is deemed unsolvable,
    typically for higher-order unification problems.
    """
    
    def __init__(self, constr):
        """
        
        Arguments:
        - `constr`:
        """
        Exception.__init__(self)
        self.constr = constr


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

    def __str__(self):
        return "\n".join(
            [", ".join(map(str, s)) for s in self.stacks])

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


def sub_in_goal(goal):
    """Substitute all the meta-variables in
    a goal
    
    Arguments:
    - `goal`:
    """
    tele = elab.sub_mvar(goal.tele)
    prop = elab.sub_mvar(goal.prop)
    return Goal(tele, prop)


class SubMvar(Tactic):
    
    def __init__(self):
        
        Tactic.__init__(self, "sub_mvar")

    def solve(self, goals, context):
        return [sub_in_goal(g) for g in goals]


sub_mvar = SubMvar()


def get_sub(goals):
    """Split a list of goals into the inequalities
    and the others.
    
    Arguments:
    - `goals`: a list of goals
    """
    ineqs, other = [], []
    for g in goals:
        if g.prop.is_sub():
            ineqs.append(g)
        else:
            other.append(g)
    return ineqs, other


def split(mvar, goals):
    """Takes a meta variable X, a list of constraints of the form
    T <= X, X <= U, and V <= W and seperates them into a triple of lists.
    
    Arguments:
    - `mvar`: A meta variable
    - `goals`: a list of goals
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
    return [Goal(e.nullctxt(), e.Sub(c.prop.lhs, d.prop.rhs))\
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
        max_list = [Goal(e.nullctxt(), e.Sub(u, t))\
                    for u in types]
        max_goal = Goals('max_goal', ctxt, goals=max_list)
        max_goal.solve_with(par(trytac(sub_tac)))
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
        min_list = [Goal(e.nullctxt(), e.Sub(t, u))\
                    for u in types]
        min_goal = Goals('min_goal', ctxt, goals=min_list)
        min_goal.solve_with(trivial)
        if min_goal.is_solved():
            return t
    return None


def solve_ineqs(goals):
    """Solve a goal set consisting of subtyping constraints,
    possibly containing meta-variables.
    
    Arguments:
    - `goals`: a goal set
    """
    goals.solve_with(trivial >>
                          repeat(destruct >> trivial)
                          >> par(trytac(sub_tac)))
    if goals.is_solved():
        return goals
    else:
        ineqs = goals.goals
        c = ineqs[0].prop
        assert(c.is_sub())
        #destruct>>trivial was unable to solve the constraint
        if not (c.lhs.is_mvar() or c.rhs.is_mvar()):
            #in this case, we have a higher-order unification problem, and
            #we just give up in hopes of finding an instance later (e.g. using
            #a type class)
            if e.root_app(c.lhs)[0].is_mvar() or \
                   e.root_app(c.rhs)[0].is_mvar():
                return goals
            else:
                raise UnsolvabeConstr(c)
        else:
            if c.lhs.is_mvar():
                m = c.lhs
            else:
                m = c.rhs
            assert(m.is_mvar())

            lt, gt, other = split(m, ineqs)

            if len(lt) == 1 and len(gt) == 0:
                m.set_val(lt[0].prop.lhs)
                m_elim = other
            elif len(lt) == 0 and len(gt) == 1:
                m.set_val(gt[0].prop.rhs)
                mvar_stack.push(m)
                m_elim = other
            elif len(lt) == 1 and len(gt) == 1 and \
                     (lt[0].prop.lhs is gt[0].prop.rhs):
                m.set_val(lt[0].prop.lhs)
                mvar_stack.push(m)
                m_elim = other
            else:
                m_elim = cross(lt, gt) + other

            elim_goals = Goals('solve_ineqs', goals.context, goals=m_elim)
            solve_ineqs(elim_goals)

            lt = map(sub_in_goal, lt)
            gt = map(sub_in_goal, gt)

            if len(lt) != 0:
                lbs = [ineq.prop.lhs for ineq in lt]
                glb = max_type(lbs, goals.context)
                if not (glb is None):
                    m.set_val(glb)
                    mvar_stack.push(m)
                else:
                    #Try the first possible solution
                    m.set_val(lbs[0])
                    mvar_stack.push(m)
            elif len(gt) != 0:
                ubs = [ineq.prop.rhs for ineq in gt]
                lub = min_type(ubs, goals.context)
                if not (lub is None):
                    m.set_val(lub)
                    mvar_stack.push(m)
                else:
                    #Try the first possible solution
                    m.set_val(ubs[0])
                    mvar_stack.push(m)
            else:
                assert(False)
        goals.solve_with(sub_mvar >> trivial)
        if goals.is_solved():
            return goals
        else:
            return solve_ineqs(goals)


class SolveMvars(Tactic):
    """Instanciate the meta-variables in a manner that satisfies the
    inequality constraints.
    Removes solved constraints from the
    goals. The base inequalities come from the global context only!
    """
    
    def __init__(self):
        Tactic.__init__(self, 'solve_mvars')

    def solve(self, goals, context):
        ineqs, other = get_sub(goals)
        ineq_goals = Goals('sub', context, goals=ineqs)
        try:
            ineq_goals = solve_ineqs(ineq_goals)
        except UnsolvabeConstr as excep:
            mess = "Unsolvable constraint: {0!s}".format(excep.constr)
            raise TacticFailure(mess, self, goals)
        #If there are unsolved ineq_goals, we put them at the end, in
        #the hopes that solving other will instanciate meta-variables
        #and provide a solution to ineq_goals
        sub_out = Goals('out', context, goals=other + ineq_goals.goals)
        sub_out.solve_with(sub_mvar >> trivial)
        return sub_out.goals

solve_mvars = SolveMvars()


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
                if isinstance(prop.lhs, e.Mvar):
                    mvar = prop.lhs
                    tm = prop.rhs
                elif isinstance(prop.rhs, e.Mvar):
                    mvar = prop.rhs
                    tm = prop.lhs
                else:
                    mess = "No top-level meta-variable in {0!s}"\
                           .format(goal.prop)
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


class FastSolveMvar(Tactic):
    """If the goal is of the form ?X <= T or
    T <= ?X with ?X a meta-variable, give the
    value T to ?X
    """
    
    def __init__(self):
        Tactic.__init__(self, 'fast_solve_mvar')

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
                if prop.lhs.is_mvar():
                    prop.lhs.set_val(prop.rhs)
                    mvar_stack.push(prop.lhs)
                    return tail
                elif prop.rhs.is_mvar():
                    prop.rhs.set_val(prop.lhs)
                    mvar_stack.push(prop.rhs)
                    return tail
                else:
                    mess = "{0!s} does not contain a head meta-variable!"\
                           .format(goal)
                    raise TacticFailure(mess, self, goals)
            else:
                mess = "{0!s} is not of the form T <= U!"\
                       .format(goal)
                raise TacticFailure(mess, self, goals)


fast_solve_mvar = FastSolveMvar()


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
        Tactic.__init__(self, 'mvar_apply({0!s})'.format(hyp))
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


class fast_apply(Tactic):
    """Calls mvar_apply, then calls fast_unify
    """
    
    def __init__(self, hyp):
        Tactic.__init__(self, "fast_apply({0!s})".format(hyp))
        self.hyp = hyp

    def solve(self, goals, context):
        return (mvar_apply(self.hyp) >> fast_unify).solve(goals, context)


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
                return fast_apply(self.inst).solve(goals, context)
            else:
                mess = "Expression {0!s} is not an instance of {1!s}"\
                       .format(root, self.root)
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
            hyps = goals[0].tele.types
            hyp_insts = [i for i in hyps if e.root_app(i)[0].info.is_class]
            ctxt_insts = context.to_list_rec('class_instances')
            for inst in hyp_insts + ctxt_insts:
                try:
                    mvar_stack.new()
                    return now(sub_mvar\
                               >> instance(inst)\
                               >> unify\
                               >> par(trytac(self))\
                               >> unify)\
                           .solve(goals, context)
                except TacticFailure:
                    mvar_stack.free()
            goal_str = goals[0].prop
            mess = "No class instances for goal {0!s}".format(goal_str)
            raise TacticFailure(mess, self, goals)

instances = Instances()

###############################################################################
#
# The main tactics for solving constraints with meta-vars
#
###############################################################################


unify = sub_mvar >> \
        par(simpl(conv.par_beta)) >> \
        trivial >> \
        par(trytac(sub_tac)) >> \
        solve_mvars

fast_unify_step = sub_mvar >> \
                  trivial >> \
                  repeat(destruct >> trivial) >> \
                  fast_solve_mvar

fast_unify = repeat(fast_unify_step)
