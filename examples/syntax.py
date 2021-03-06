# -*- coding: utf-8 -*-

#############################################################################
#
# syntax.py
#
# description: examples of syntax
#
#
# Authors:
# Cody Roux
#
#
#
##############################################################################

import boole.core.expr as expr

from boole import *


def test1():
    
    p, q = Bool('p q')

    X = deftype('X')

    el = defvar('el', X)

    One = defclass('One', [X, el], true)

    definstance('One_int', One(Int, 1), triv())

    one_inst = defconst('one_inst', One(X, el))
    
    one = defexpr('one', abst([X, el, one_inst], el), \
                  pi([X, el, one_inst], X, impl=True))


    test = defexpr('test', 3 + one())

    test_def = get_def('test')
    
    plus_def = get_def('+')

    one_def = get_def('one')

    print conv.beta_norm(expr.sub_in([plus_def, one_def], ['+', 'one'], test_def))
    print

    x = Real('x')
    y = Real('y')
    z = Real('z')

    i = Int('i')
    j = Int('j')
    k = Int('k')

    x_y_z = defexpr('x_y_z', x * y * z)
    
    int_ops = defexpr('int_ops', 3 * i < j * 2)

    poly = defvar('poly', pi(X, X >> (X >> X), impl=True))

    poly_z = defexpr('poly_z', poly(z))

    nat = deftype('nat')
    
    nat_sub_real = defsub('nat_sub_real', nat <= Real)

    A = deftype('A')
    B = deftype('B')
    op_a = defconst('op_a', A >> (A >> A))
    op_b = defconst('op_b', B >> (B >> B))

    p1 = defvar('p1', A*B)
    p2 = defvar('p2', A*B)

    op_pair = \
            abst([p1, p2], pair(op_a(p1[0], p2[0]), op_b(p1[1], p2[1])))

    definstance('Mul_prod', \
                forall([A, op_a, B, op_b], \
                implies([Mul(A, op_a), Mul(B, op_b)],\
                        Mul(A*B, op_pair))), \
                triv())


    test3 = defexpr('test3', pair(3, 3.0) * pair(2, 2.0))

    test3_def = get_def('test3')

    mul_def = get_def('*')

    print
    print conv.beta_norm(expr.sub_in([mul_def], ['*'], test3_def))
    print
    
    test4 = defexpr('test4', pair(3.0, pair(3.0, 3)) * pair(2.0, pair(2.0, 2)))

    test4_def = get_def('test4')

    print
    print conv.beta_norm(expr.sub_in([mul_def], ['*'], test4_def))
    print

    test5 = defexpr('test5', pair(pair(3.0, 3), pair(3, 3)) * pair(pair(2.0, 2), pair(2, 2)))

    test5_def = get_def('test5')

    print
    print conv.beta_norm(expr.sub_in([mul_def], ['*'], test5_def))
    print

    n = Int('n')
    
    Vec = defconst('Vec', pi(n, Type))

    succ = defconst('succ', Int >> Int)

    nil = defconst('nil', Vec(0))

    cons = defconst('cons', pi(n, Real >> (Vec(n) >> Vec(succ(n))), impl=True))

    sum_vec = defconst('sum_vec', pi(n, Vec(n) >> (Vec(n) >> Vec(n)), impl=True))

    add_nil = defhyp('add_nil', sum_vec(nil, nil) == nil)

    v1 = defvar('v1', Vec(n))

    v2 = defvar('v2', Vec(n))

    a = defvar('a', Real)

    b = defvar('b', Real)

    add_cons_eq = sum_vec(cons(a, v1), cons(b, v2)) == cons(a+b, sum_vec(v1, v2))

    add_cons = defhyp('add_cons', forall([n, a, b, v1, v2], add_cons_eq))

    rev = defconst('rev', pi(n, Vec(n) >> Vec(n), impl=True))

    v3 = defvar('v3', Vec(3))

    rev_3 = defexpr('rev_3', rev(v3))

    w = Real('w')
    t = Real('t')

    abs_plus = defexpr('abs_plus', abst(t, t + w))

    sub_test = defexpr('sub_test', abs_plus(i))

    p = pair(x, y)

    proj_x_y_0 = defthm('proj_x_y_0', p[0] == x)

    get_def(proj_x_y_0.name).show_proof()

    prop = defexpr('prop', And(true, Or(true, false)))
    
    p = (Real * Real)('p')

    fa = forall(p, (p[0] + p[1]) == (p[1] + p[0]))

    plus_commut_stmt = defexpr('plus_commut_stmt', fa, type=Bool)
    
    plus_commut = defexpr('plus_commut', triv(), fa)

    goal = current_ctxt().next_goal()

    print goal

    goal.interact(tactics.unpack('p', names=['x', 'y']))

    goal.interact(tactics.simpl(conv.par_beta))


def test2():
    
    x = Real('x')
    y = Real('y')
    z = Real('z')
    i = Int('i')
    j = Int('j')
    k = Int('k')
    p = Bool('p')
    q = Bool('q')
    r = Bool('r')
    
    Beatles, (John, Paul, George, Ringo) = \
        defenum('Beatles', ['John', 'Paul', 'George', 'Ringo'])
    
    check(x * y - y * x)
    check(i * j - (j % i) + j / k)
    check((x ** y) / (x ** 2.0) + z ** 3.0)
    check(And(p, Not(q), implies([p, q], Not(r))))
    check(And(x * y == y * x, x + y != y + x, Not(x > 2.0)))
    check(implies(Or(x > 0.0, y > 0.0), x ** 2.0 + y ** 2.0 > 0.0))
    check(forall([x, y], x * y == y * x))
    check(forall([x,y], exists(z, And(x < z, z < y))))
    check(Beatles)
    check(John)


if __name__ == '__main__':

    set_verbose()
    
    test1()     # cody's tests
    test2()    # jeremy's tests

    x, y = Real('x y')
    new = defexpr('new', x*x + 2*y == 3)
