# -*- coding: utf-8 -*-

#############################################################################
#
# order_2.py
#
# description: Axiomatization of groups of order 2 and some experiments
#
#
# Authors:
# Cody Roux
#
#
##############################################################################

from boole import *
import boole.core.tactics as tac
import boole.interfaces.ladr_interface as ladr
import boole.core.expr as expr


set_verbose()

## We work in a fresh context
push_ctxt('group')

# ## The following definitions define the basic structure
# # for a generic group
G = deftype('G')

G_mul = defconst('G_Mul', G >> (G >> G))

G_one = defconst('G_one', G)

G_inv = defconst('G_inv', G >> G)

i = G_inv

g = G('g')

## We can define multiplication and unit class instances
# for G
definstance('G_Mul', Mul(G, G_mul), triv())

definstance('G_One', One(G, G_one), triv())

## And express the axioms of a group
defhyp('unit_l', forall(g, one() * g == g))

defhyp('unit_r', forall(g, g * one() == g))

g1, g2, g3 = G('g1 g2 g3')

defhyp('assoc', forall([g1, g2, g3], (g1 * g2) * g3 == g1 * (g2 * g3)))

defhyp('inv_l', forall(g, i(g) * g == one()))

defhyp('inv_r', forall(g, g * i(g) == one()))

## Let's add an axiom that states every element is of
# order 2:
defhyp('order_2', forall(g, g * g == one()))

## It turns out that every group of order 2 is commutative!
h = G('h')

defthm('commut', forall([g,h], g * h == h * g))

goal = current_ctxt().next_goal()

## We can call an automated prover to show this
goal.interact(ladr.prover9_tac(unfold=['*', 'one']))

