--------------------------------------------------------------------------------

# Boole To-Do List

--------------------------------------------------------------------------------

## Short term

- Use "M[x] = ..." or "M['x'] = ..." for model assignment?

- Settle on case conventions for predicates and functions

- Settle on conventions for naming classes, including error messages

- Check the order of operations with <, &, >>, etc. -- they may not act
  as expected

- Debug and develop tests


## General

- Better infrastructure for translations (to codify structure and avoid
  repetitions)

- Configuration files (for Sage, Z3, and other external packages)

- Better printing of expressions, e.g. avoiding extra parens


## Expressions

- Do away with Star types, and "And" and "Sum", etc.? Make these abbreviations
  for iterated binary operations?

- Develop better handling for various types of polymorphism.

- Other types

    * list types

    * strings

    * records?

- Bounded quantification

- "Some" operator

- Definitions

- Latex output

- Parser and pretty printer

- Add a "Distinct" predicate to language, à la Z3?


## Models 

- Develop classes of semantic objects (ints, reals, functions) rather than
  using Python objects

- Why is evaluation slow?

- Quickcheck - testing with random variables


## Z3 Interface

- Models - translate functions

- Solver - manage settings, etc.


## Sage Interface

- Better understand Sage handling of ints and floats

- Use domains in symbolic expression package

- Understand treatment of functions (use arities, domain information?)

- Understand assumptions in symbolic expression package

- What to do with enumerated types?


## Other interfaces

- LADR (Prover 9 and Mace)

- SMT

- TPTP

- Isabelle

- Coq

- Quickcheck


## Docs

- Reference manual

- Tutorial

- IPython?


## Reasoner

- Develop notion of 'goal'

    * local hypotheses (named)

    * main assertion

- Develop 'proof', 'proof state'
 
- Develop tactic language

    * apply hypothesis or background fact

    * rewrite with hypothesis or background fact

    * insert background fact

    * send to external tool


## Database

- Need to manage lists of theorems and definitions

- Search

- Think about name spaces


## Boole add-ons

- Inequality reasoner


## Boole clients

- Euclid

- Tarski (based on Tarski's World)




 
