#
# A /quick and dirty/ Boole -> LADR (Prover9) interface.
# This translation only works for (multisorted) first-order Boole formulas.
# Since LADR is unsorted, we
#
#   - Introduce an LADR predicate symbol of the form `IsAT' for each
#      Boole type `T' used in the goal formula,
#   - Adjoin hypotheses to each goal stating that all `sorts' are
#      nonempty, and that functions return the proper `codomain.'
#
# TODO:
#
#  - Redo /all/ of this using a general FOL class, rather than simply
#    constructing LADR-specific formula strings. This will be far more
#    elegant than the extremely dirty string manipulation done below.
#    Once we do this, we'll be able to target LADR, TPTP, and other FO
#    formats just by writing `FOL -> _' converters.
#
#  - Extend to support the importing of Mace4 models.
#    (* I need to understand how this works for Z3 currently.)
#
#  - Extend to output TPTP and use the SystemOnTPTP remote prover
#    module I've written.
#
#  G. Passmore - 11-Nov-2013
#

from boole.elab.terms import *
import boole.core.typing as ty
import boole.core.tactics as tac
import boole.interfaces.ineq_interface as ineq
from boole.core.expr import open_bound_fresh_consts

import pipes
import tempfile

#
# You must set this to your LADR bin path.
#
# Q: Is there a global `settings' module for Boole we can use to store
# this sort of thing?
#

#ladr_bin_path = "/Users/grant/Research/Provers/LADR/LADR-2009-11A/bin/"
ladr_bin_path = "/usr/bin/"

from fractions import Fraction

################################################################################
#
# Exceptions associated with LADR interface
#
################################################################################

class LADR_Interface_Error(Exception):
    """Class of all possible type errors
    """

    def __init__(self, mess = ''):
        """
        Arguments:
        -`mess`: a string that represents the error message
        """
        Exception.__init__(self, mess)

class LADR_Unexpected_Expression(LADR_Interface_Error):
    """Raised when there is a problem translating an expression
    """

    pass

_built_in_ladr_funs = {
    eq.name: (lambda args: "(" + args[0] + " = " + args[1] + ")"),
    And.name: (lambda args: "(" + args[0] + " & " + args[1] + ")"),
    Or.name: (lambda args: "(" + args[0] + " | " + args[1] + ")"),
    implies.name:
        (lambda args: "(" + args[0] + " -> " + args[1] + ")"),
    Not.name: (lambda args: "(- " + args[0] + ")"),
}

################################################################################
#
# Convert Boole expressions to LADR expressions
#
################################################################################


class Boole_to_LADR:
    """
    Boole to LADR, constructing an LADR string.

    For example:

    C = Boole_to_LADR()
    print C(x + y)
    print C(f(x))

    """

    def __init__(self):
        self.sort_preds = {} # A dictionary mapping Boole types to
                             # LADR predicate symbols.
        self.closure_preds = {} # A dictionary mapping Boole functions
                                # to a closure statement of the
                                # functions w.r.t. their domains and
                                # codomains.

    def reset(self):
        self.sort_preds = {}
        self.closure_preds = {}

    # Is a function symbol a predicate?

    def is_predicate(self, t):
        codom, _ = root_pi(t)
        return codom.equals(Bool)

    # Given a Boole function, construct a valid LADR function string
    # corresponding to it.

    def ladr_fun_name(self, f, predicate=False):
        s = f.name
        if predicate:
            if s[0].isupper():
                return s
            else:
                return 'P' + s
        else:
            if s[0].islower():
                return s
            else:
                return 'f' + s

    # Given k, construct list of LADR variable strings of the form
    # ['x1', ..., 'xk'].

    def ladr_var_block(self, k):
        o = []
        for i in range(k):
            o += ['x' + str(i+1)]
        return o

    # Given a Boole function, construct a domain closure statement for
    # its corresponding LADR predicates for its domain and codomain.

    def ensure_fun_closure(self, fun):
        if fun.name in self.closure_preds.keys():
            return self.closure_preds[fun.name]
        else:
            etype, _ = ty.infer(fun)
            codom, doms = root_pi(etype)
            # We state that the output of the function satisfies the
            # codomain predicate.
            codom_pred = self.ladr_sort_pred(codom)
            d_n = len(doms)
            v_block = self.ladr_var_block(d_n)
            q_open = ''
            for v in v_block:
                q_open += "(all " + v + ' '
            vs = ", ".join(v_block)
            q_close = ')'*d_n
            f = self.ladr_fun_name(fun)
            s = q_open + codom_pred + '(' + f + '(' + vs + '))' + q_close
            print "\n--\nClosure axiom for function: \n\n" + s + "\n--"
            self.closure_preds[fun.name] = s
            return s

    def handle_function(self, fun, args):
        """
        fun: Boole function symbol to apply
        args: LADR expressions, already translated
        """
        # note the different calling conventions
        if fun.name in _built_in_ladr_funs.keys():
            # built-in function symbol (a logical connective)
            ladr_fun = _built_in_ladr_funs[fun.name]
            return ladr_fun(args)
        else:
            # an LADR function symbol
            etype, _ = ty.infer(fun)
            if self.is_predicate(etype):
                ladr_fun = (lambda a: self.ladr_fun_name(fun, predicate=True) \
                            + "(" + ",".join(a) + ")")
            else:
                # We must make sure to construct a `closure' statement
                # for this function w.r.t. its domain (represented as
                # an LADR predicate).
                self.ensure_fun_closure(fun)
                ladr_fun = (lambda a: self.ladr_fun_name(fun) + "(" + ",".join(a) + ")")
            return ladr_fun(args)

    # Given a Boole type, give an LADR predicate symbol string
    # corresponding to the sort of that variable or constant.

    def ladr_sort_pred(self, t):
        t = t.name
        if t in self.sort_preds.keys():
            self.sort_preds[t]
        else:
            pre = 'IsAn' if str(t)[0].lower() in ['a','e','i','o','u'] else 'IsA'
            self.sort_preds[t] = pre + str(t)
        return self.sort_preds[t]

    # Return an LADR formula asserting that all Boole sorts used in a
    # goal are nonempty. We must do this for all sorts used, else,
    # when given an unsatisfiable sentence, instead of deriving empty
    # clause, resolution will derive precisely the statements that the
    # sorts must be empty.

    def sorts_nonempty_fml(self):
        fs = ['(exists x ' + s + '(x))' for _, s in self.sort_preds.iteritems()]
        s = ' & '.join(fs)
        if s != '':
            print "\n--\nDomain nonemptiness axiom:\n\n" + s + "\n--"
        return s

    # Return an LADR formula asserting that functions return their
    # codomain sorts.

    def funs_closure_fml(self):
        s = ' & '.join([s for _, s in self.closure_preds.iteritems()])
        return s

    # Given a list of zipped (consts x ladr_strs_of_consts), construct
    # a domain constraint conjunction for them.

    def ladr_sort_conj(self, cs):
        s = (' & '.join(map(lambda c: self.ladr_sort_pred(c[0].type) + "(" + str(c[1]) + ")",
                            cs)))
        return s

    def __call__(self, expr, vars_lst=[], var=False):
        if expr.is_const():
            etype, _ = ty.infer(expr)
            if self.is_predicate(etype):
                if expr.name[0] == 'P':
                    return expr.name
                else:
                    return ("P" + expr.name)
            else:
                if var or expr.name in vars_lst:
                    # LADR vars must begin with chars 'u'-'z'.
                    if expr.name[0] in ['u', 'v', 'w', 'x', 'y', 'z']:
                        return expr.name
                    else:
                        return ("x" + expr.name)
                else:
                    # LADR consts must begin with chars 'a'-'t'
                    if ord(expr.name[0]) < 117: # chr(117) == 'u'
                        return expr.name
                    else:
                        return ("c" + expr.name)
        elif expr.is_app():
            fun, args = root_app_implicit(expr)
            args = [self.__call__(a, vars_lst=vars_lst) for a in args]
            return self.handle_function(fun, args)
        elif expr.is_forall():
            vlist, body = open_bound_fresh_consts(expr)
            ladr_vars = [v.name for v in vlist]
            # ladr_vars_strs is needed to convert all Boole vars into
            # a syntactic format supported by LADR.
            ladr_vars_strs = [self(v, var=True) for v in vlist]
            ladr_body = self(body, vars_lst = ladr_vars)
            ladr_sorting = self.ladr_sort_conj(zip(vlist, ladr_vars_strs))
            #print ladr_sorting
            return ("all " + (" all ".join(ladr_vars_strs)) + " " \
                    + '((' + ladr_sorting + ") -> " + ladr_body + ')')
        elif expr.is_exists():
            vlist, body = open_bound_fresh_consts(expr)
            ladr_vars = [v.name for v in vlist]
            ladr_vars_strs = [self(v, var=True) for v in vlist]
            ladr_body = self(body, vars_lst=ladr_vars)
            ladr_sorting = self.ladr_sort_conj(zip(vlist, ladr_vars_strs))
            return ("exists " + (" exists ".join(ladr_vars_strs)) + " " \
                    + '((' + ladr_sorting + ') & ' + ladr_body + ')')
        else:
            raise LADR_Unexpected_Expression


################################################################################
#
# A class interface to the LADR solver
#
################################################################################

class LADR_Solver():

    def __init__(self, language = None):
        self.boole_to_ladr = Boole_to_LADR()

    def reset(self):
        self.boole_to_ladr.reset()

    def mk_ladr_goal(self, f):
        g = self.boole_to_ladr(f)
        n = self.boole_to_ladr.sorts_nonempty_fml()
        c = self.boole_to_ladr.funs_closure_fml()
        if len(n) > 0 and len(c) > 0:
            encoding_prefix = '(' + n + ' & ' + c + ')' + ' -> '
        elif len(n) > 0:
            encoding_prefix = '(' + n + ')' + ' -> '
        elif len(c) > 0:
            encoding_prefix = '(' + c + ')' + ' -> '
        else:
            encoding_prefix = ''
        s = "formulas(goals).\n" + encoding_prefix + g + ".\nend_of_list."
        return s

    def prove(self, f):
        self.reset() # We currently hold no context between prover calls
        s = self.mk_ladr_goal(f)
        print "\n--\nFinal LADR input formula:\n\n" + s + "\n--"
        p = pipes.Template()
        p.append(ladr_bin_path + "prover9", "--")
        #p.append(ladr_bin_path + "interpformat portable", "--")
        p.debug(False)
        t = tempfile.NamedTemporaryFile(mode='r')
        f = p.open(t.name, 'w')
        try:
            f.write(s)
        finally:
            f.close()
            t.seek(0)
            ms_str = t.read()
            if True:
                print "Prover output:\n", ms_str
                t.close()
            return ("============================== PROOF =================================" in ms_str)

################################################################################
#
# Using Mace4 models as groups in Sage.
#
################################################################################

#
# Given a group model, construct a permutation group from it (Cayley's Theorem).
#
# As above, a group model uses `f : G*G -> G', 'e : G' with carrier
# set "DOMAIN".
#

def group_perms(m, verbose=False):

    G = m["DOMAIN"]
    e = m["e"]
    f = m["f"]

    def cycle_of_g_at_h(g, h):
        # get the permutation given by left multiplication
        # by g, beginning at h.
        cycle = (h,)
        a = f(g, h)
        while (a != h):
            cycle += (a,)
            a = f(g, a) # left multiplication by g
        return cycle

    perms = []
    c = 0
    for g in G:
        G_to_cover = G
        g_perm = []
        while (G_to_cover != []):
            new_cycle = cycle_of_g_at_h(g, G_to_cover[0])
            g_perm = g_perm + [new_cycle]
            G_to_cover = filter((lambda g: g not in new_cycle), G_to_cover)
        perms = perms + [g_perm]
        if verbose:
            print "- Permutation for g[" + str(c) + "] constructed:", g_perm
            if (g == e):
                print "- Note that g[" + str(c) +"] is the identity (should correspond to identity permutation!)."
        c += 1
    return perms

#
# Given a group model, construct a Sage permutation group from it.
# We use the list of permutations constructed by group_perms.
#

def sage_perm_group_from_m(m, gens_small=False):
    d = m["DOMAIN"]
    perms = group_perms(m)
    G = PermutationGroup(perms, domain=d)
    if gens_small:
        return PermutationGroup(G.gens_small(), domain=d)
    else:
        return G

#
# Given a Sage group object, construct a FOL model.
#

def model_of_group(g):
    return {"DOMAIN": g.list(),
            "e" : g.identity(),
            "f" : (lambda x, y: x*y),
            "inv" : (lambda x: x^-1)}


################################################################################
#
# Test these out
#
################################################################################

if __name__ == '__main__':

    G = deftype('G')
    x,y,z = G('x y z')
    e = G('e')
    p = Bool('p')
    q = Bool('q')
    i = (G >> G)('i')
    f = (G >> (G >> G))('f')
    P = (G >> Bool)('P')

    T = Boole_to_LADR()
    S = LADR_Solver()

    print "--\nSome FOL fun:\n"
    S.prove(implies(And(p, q), And(q, q)))
    S.prove(Or(p, Not(p)))
    S.prove(implies(forall([x], P(x)), exists([x], P(x))))
    S.prove(implies(forall([x], P(x)), forall([y], P(y))))

    print "--\n A little group theory:\n"

    goal = (implies(And(forall([x], f(x, i(x)) == e),
                        forall([x,y,z], f(x, f(y, z)) == f(f(x, y), z)),
                        forall([x], f(x, e) == x),
                        forall([x], f(x, x) == e)),
                    forall([x,y], f(x,y) == f(y,x))))

    print "--\nGoal:\n\n" + str(goal) + "\n--"

    print "Attempting proof..."
    S.prove(goal)
