###############################################################################
#
# coq_interface.py
#
# description: interface between Boole and Coq
#
###############################################################################

import operator


from boole import *
from boole.elaboration.terms import root_app_implicit
from boole.core.expr import open_bound_fresh, ExprVisitor,\
     Pi, Sig, Abst, Forall, Exists, root_app
import boole.core.typing as ty
import boole.config

from uuid import uuid4

import subprocess
import tempfile
from os import devnull

coq_path = boole.config.coq_bin
session_id = uuid4().time_low
filename = "coq_{0!s}_{1!s}.v".format(current_ctxt().name, session_id)
out_file = "coq_{0!s}_{1!s}.out".format(current_ctxt().name, session_id)


###############################################################################
#
# Exceptions associated with Coq
#
###############################################################################


class CoqError(Exception):
    """Class of all possible type errors
    """
    
    def __init__(self, mess=''):
        """
        Arguments:
        -`mess`: a string that represents the error message
        """
        Exception.__init__(self, mess)


class TransError(Exception):
    """The class of errors which occur during translation
    """
    
    def __init__(self, mess, tm):
        Exception.__init__(self, mess)
        self.tm = tm

###############################################################################
#
# These dictionaries gives the Coq translations of the built-in symbols,
# built-in sorts, and String functions for building constants of the built-in
# sorts.
#
###############################################################################


coq_fun = {
    eq.name: (lambda args: "({0!s} = {1!s})".format(args[0], args[1])),
    And.name: (lambda args: "({0!s} /\ {1!s})".format(args[0], args[1])),
    Or.name: (lambda args: "({0!s} \/ {1!s})".format(args[0], args[1])),
    implies.name:
        (lambda args: "({0!s} -> {1!s})".format(args[0], args[1])),
    Not.name: (lambda args: "~{0!s}".format(args[0])),
    add.name: (lambda args: "({0!s} + {1!s})".format(args[0], args[1])),
    mul.name: (lambda args: "({0!s} * {1!s})".format(args[0], args[1])),
    minus.name: (lambda args: "({0!s} - {1!s})".format(args[0], args[1])),
    uminus.name: (lambda args: "-{0!s}".format(args[0])),
    div.name: (lambda args: "({0!s} / {1!s})".format(args[0], args[1])),
    lt.name: (lambda args: "({0!s} < {1!s})".format(args[0], args[1])),
    le.name: (lambda args: "({0!s} <= {1!s})".format(args[0], args[1])),
    true.name: "True",
    false.name: "False"
    }

coq_not_implemented = [mod.name, power.name]

coq_sort = {
    Int.name: "Z",
    Real.name: "R",
    Bool.name: "Prop",
    Type.name: "Type"
    }

#We use the "explicit" notation for binders, i.e.
# ex (fun (x : A) => (P x)) instead of exists x, P x
coq_binder = {
    "pi": "piT",
    "sig": "sigT",
    "abst": "",
    "forall": "all",
    "exists": "ex"
    }

imports = ["ZArith", "Reals"]

#What's the right choice here?
scope = "R_scope"

piT_def = ("piT", "{A : Type} (B : A -> Type)", "forall (x : A), B x")

defs = [piT_def]


def build_app(f, args):
    """Build the syntactic application of a (currified) function to
    its arguments
    
    Arguments:
    - `f`: a string
    - `args`: a string
    """
    app = str(f)
    for a in args:
        app = "({0!s} {1!s})".format(app, a)
    return app

###############################################################################
#
# Convert Boole expressions to Coq
#
###############################################################################


class BooleToCoq(ExprVisitor):
    """Convert a Boole expression to an coq one with the same meaning.
    """
    
    def __init__(self):
        ExprVisitor.__init__(self)

    def visit_const(self, expr, *args, **kwargs):
        if expr.name in coq_fun:
            return coq_fun[expr.name]
        if expr.name in coq_sort:
            return coq_sort[expr.name]
        if expr.name in coq_not_implemented:
            raise TransError('function {0!s} not implemented'\
                             .format(expr.name), expr)
        else:
            return expr.name

    def visit_db(self, expr, *args, **kwargs):
        raise TransError("Cannot translate a DB term", expr)

    def visit_type(self, expr, *args, **kwargs):
        return coq_sort[Type.name]

    def visit_kind(self, expr, *args, **kwargs):
        raise TransError("Cannot translate Kind", expr)

    def visit_bool(self, expr, *args, **kwargs):
        return coq_sort[Bool.name]
    
    def visit_bound(self, expr, *args, **kwargs):
        var, body = open_bound_fresh(expr)
        coq_body = self.visit(body, *args, **kwargs)
        coq_dom = self.visit(expr.dom, *args, **kwargs)
        coq_bnder = coq_binder[expr.binder.name]
        return "{0!s} (fun ({1!s} : {2!s}) => {3!s})"\
               .format(coq_bnder, var, coq_dom, coq_body)

    def visit_app(self, expr, *args, **kwargs):
        f, ts = root_app_implicit(expr)
        coq_ts = [self.visit(t, *args, **kwargs) for t in ts]
        if f.name in coq_fun:
            return coq_fun[f.name](coq_ts)
        else:
            coq_f = self.visit(f, *args, **kwargs)
            return build_app(coq_f, coq_ts)

    def visit_pair(self, expr, *args, **kwargs):
        coq_fst = self.visit(expr.fst, *args, **kwargs)
        coq_snd = self.visit(expr.snd, *args, **kwargs)
        return "(existT {0!s} {1!s})".format(coq_fst, coq_snd)

    def visit_fst(self, expr, *args, **kwargs):
        coq_expr = self.visit(expr.expr, *args, **kwargs)
        return "(projT1 {0!s})".format(coq_expr)

    def visit_snd(self, expr, *args, **kwargs):
        coq_expr = self.visit(expr.expr, *args, **kwargs)
        return "(projT2 {0!s})".format(coq_expr)

    def visit_ev(self, expr, *args, **kwargs):
        return "I"

    def visit_sub(self, expr, *args, **kwargs):
        coq_lhs = self.visit(expr.lhs, *args, **kwargs)
        coq_rhs = self.visit(expr.rhs, *args, **kwargs)
        return "({0!s} = {1!s})".format(coq_lhs, coq_rhs)

    def visit_box(self, expr, *args, **kwargs):
        return self.visit(expr.expr, *args, **kwargs)

    def visit_mvar(self, expr, *args, **kwargs):
        raise TransError("Cannot translate a meta-variable", expr)

    def visit_tele(self, expr, *args, **kwargs):
        """
        
        Arguments:
        - `*args`:
        - `**kwargs`:
        """
        raise TransError("Cannot translate a telescope", expr)


def boole_to_coq(expr):
    """
    
    Arguments:
    - `expr`:
    """
    return BooleToCoq().visit(expr)


def coq_import(i):
    """Coq: import module with name i
    
    Arguments:
    - `i`:
    """
    return "Require Import {0!s}.\n".format(i)


def make_imports():
    out = ""
    for i in imports:
        out += coq_import(i)
    return out


def coq_scope(s):
    """Coq: create scope s
    
    Arguments:
    - `s`:
    """
    return "Open Scope {0!s}.\n".format(s)


def make_scope():
    return coq_scope(scope)


def coq_def(name, params, body):
    """Coq definition
    
    Arguments:
    - `name`: name of the defined function
    - `params`: strings representing the parameters
    - `body`: the body of the definition
    """
    return "Definition {0!s} {1!s} := {2!s}.\n".format(name, params, body)


def make_defs():
    out = ""
    for name, params, body in defs:
        out += coq_def(name, params, body)
    return out


def coq_param(name, type):
    """Coq parameter
    
    Arguments:
    - `name`: name of the variable
    - `type`: type of the variable
    """
    return "Parameter {0!s} : {1!s}.\n".format(name, type)


def coq_axiom(name, type):
    """Coq axiom
    
    Arguments:
    - `name`: name of the axiom
    - `type`: type of the axiom
    """
    return "Axiom {0!s} : {1!s}.\n".format(name, type)


def coq_prop(name, type, coq_tac=None):
    """Create a proposition in Coq, the
    theorem is admitted by default
    
    Arguments:
    - `name`: name of the proposition
    - `type`: statement of the proposition
    """
    if coq_tac:
        tac = coq_tac
        finish = "Qed"
    else:
        tac = "idtac"
        finish = "Admitted"
    return "Proposition {0!s} : {1!s}.\nProof.\n{2!s}.\n{3!s}.\n"\
           .format(name, type, tac, finish)


def boole_to_coq_goal(goals):
    """Create a string representing the translation of a goal
    list in coq
    
    Arguments:
    - `goals`: an instance of Goals
    """
    sub_goals = []
    for g in goals.goals:
        hyps = ""
        for i in range(len(g.tele)):
            hyp_i = boole_to_coq(g.tele.types[i])
            hyps += " ({0!s} : {1!s})".format(g.tele.vars[i], hyp_i)
        concl = boole_to_coq(g.prop)
        coq_g = "(forall {0!s}, {1!s})".format(hyps, concl)
        sub_goals.append(coq_g)
    return " /\ ".join(sub_goals)
        

def is_coq_builtin(name):
    """Return true if name is in one of the special dictionaries.
    
    Arguments:
    - `name`:
    """
    return (name in coq_fun) or \
           (name in coq_sort) or \
           (name in coq_not_implemented)


def create_coq_file():
    """Creates a .v file with a name corresponding to the
    current session.
    """
    tac = "intuition"
    with open(filename, 'w') as f:
        f.write(make_imports())
        f.write(make_scope())
        f.write(make_defs())
        for k in current_ctxt().decls:
            if not is_coq_builtin(k) and k not in current_ctxt().defs:
                k_decl = boole_to_coq(current_ctxt().decls[k].type)
                f.write(coq_param(k, k_decl) + "\n")
        for k in current_ctxt().defs:
            if not is_coq_builtin(k):
                k_def = boole_to_coq(current_ctxt().defs[k])
                f.write(coq_def(k, "", k_def) + "\n")
        for k in current_ctxt().goals:
            k_goal = boole_to_coq_goal(current_ctxt().goals[k])
            f.write(coq_prop(k, k_goal,coq_tac=tac) + "\n")
        print "Wrote output to file " + filename
        print


coq_errors = ["Error"]

def goal_error(name):
    """Adds a string which occurs in the
    output of coq if a goal is admitted.
    
    Arguments:
    - `name`: a goal name
    """
    return "*** [ {0!s}".format(name)


#TODO: debug! (the error file is not read
def check_coq_file():
    """Adds a printing command to the coq file,
    and checks that the file compiles without error
    or unresolved goals.
    """
    out_err = coq_errors
    with open(filename, 'r') as coq_src:
        with open(out_file, 'w') as coq_out:
            tmp = tempfile.TemporaryFile(mode='r+')
            s = coq_src.read()
            tmp.write(s)
            tmp.write('Print All.\n')
            tmp.seek(0)
            coq_out.seek(0)
            chk = subprocess.call([coq_path],\
                                  stdin=tmp, stdout=coq_out,\
                                  stderr=open(devnull, 'w'))
    with open(out_file, 'r') as coq_out:
        coq_out.seek(0)
        for k in current_ctxt().goals:
            out_err.append(goal_error(k))
        for line in coq_out:
            for e in out_err:
                if e in line:
                    print 'There was a problem while checking the file:'
                    print filename
                    print line
                    print 'output in', out_file
                    return False
        return (chk == 0)


if __name__ == '__main__':

    x, y, z = Real("x y z")

    defthm('test1', forall(x, x + 0 == x))
    defthm('test2', forall([x, y, z], x + y + z == z + (y + x)))

    create_coq_file()

    print check_coq_file()
