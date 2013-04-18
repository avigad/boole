--------------------------------------------------------------------------------

# The Boole Reasoning Assistant

--------------------------------------------------------------------------------


Expressions
===========

These are described in `expr.py`.


Languages
---------

A language stores defined symbols. Boole keeps a special `built_in_language` 
for built-in symbols, and also keeps track of a default language,
`default_language` which is initialized to `global_language`. 
Define a new language with 

>    `L = Language()`

and set it to the default with

>    `set_default_language(L)`

Typing `set_default_language()` with no argument reverts to the global language. Use

>    `L.show()`

to list the elements of `L`.


Types
-----

Boole recognizes some basic type constructors:

- BaseType, for example, `BaseType('MyType')`
- EnumType
- ProdType, for example, `ProdType(Int, Int, Bool)`, which can also be written `(Int * Int* Bool)`
- FunType

`BaseType`s and `EnumType`s are keyed by their names, which are also used when
translating expressions between systems.

Built-in types include

- `Int`
- `Real`
- `Num`
- `Bool`

Ad-hoc polymorphism.


Expressions
-----------

Note that `type()` is a built-in Python method that returns the type of an object. To get the Boole type of an expression `e`, use `e.etype()`.


Models
======





The Sage Interface
==================



The Z3 Interface
================

