--------------------------------------------------------------------------------

# Boole To-Do List

--------------------------------------------------------------------------------

## Short term

- Debug and develop tests

- Notion of value attached to a constant or an expression
  in general

- Better syntactic "candy": colored keywords, unicode lambda and pi...

## General

- Better infrastructure for translations (to codify structure and avoid
  repetitions)

- Configuration files (for Sage, Z3, and other external packages)

- Better printing of expressions, e.g. avoiding extra parens


## Expressions

- Do away with Star types, and "And" and "Sum", etc.? Make these abbreviations
  for iterated binary operations?

- Other types

    * list types

    * strings

    * records?

- Bounded quantification

- "Some" operator

- Latex output

- Parser and pretty printer

- Add a "Distinct" predicate to language, à la Z3?


## Models 

- Develop classes of semantic objects (ints, reals, functions) rather than
  using Python objects

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

- Develop 'proof state'; should proofs be treated as lists or as trees?
  should tactics operate on single goals (composed with list monad), or
  directly on lists?
 
- Develop tactic language

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




 
