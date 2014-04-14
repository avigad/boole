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

## We can do the same for order 3, but the theorem isn't true!

set_verbose()

push_ctxt('group')

G = deftype('G')

G_mul = defconst('G_Mul', G >> (G >> G))

G_one = defconst('G_one', G)

G_inv = defconst('G_inv', G >> G)

i = G_inv

g = G('g')

definstance('G_Mul', Mul(G, G_mul), triv())
    
definstance('G_One', One(G, G_one), triv())

defhyp('unit_l', forall(g, one() * g == g))

defhyp('unit_r', forall(g, g * one() == g))

g1, g2, g3 = G('g1 g2 g3')

defhyp('assoc', forall([g1, g2, g3], (g1 * g2) * g3 == g1 * (g2 * g3)))

defhyp('inv_l', forall(g, i(g) * g == one()))

defhyp('inv_r', forall(g, g * i(g) == one()))

defhyp('order_3', forall(g, g * g * g == one()))

h = G('h')

defthm('commut', forall([g,h], g * h == h * g))

goal = current_ctxt().next_goal()

# ## Oops!
# goal.interact(ladr.prover9_tac(unfold=['*', 'one']))

## We can try to find a counter-example to our goal with the
# mace4 model builder
goal.interact(ladr.mace4_tac(unfold=['*', 'one'], size=27))

