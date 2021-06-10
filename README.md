# Group Identification

 - Afonso Ribeiro, 86752, afonsoribeiro@tecnico.ulisboa.pt
 - Baltasar Dinis, 89416, baltasar.dinis@tecnico.ulisboa.pt
 - João Borges, 89482, joao.p.l.borges@tecnico.ulisboa.pt

# Implemented Features

## Extend STLC
    1.
    - `ty` datatype has been extended, `Ty_NonDet`
    - `tm` datatype has been extended, `tm_nondet`
    - 2 new notations have been defined for `ty` and `tm`
    - Complete the formalizations of substitution, reduction, and the typing relation
    2.
    - Existing examples work
    - `ChoiceTest1` and `ChoiceTest2` were added
    3.
    - Solved the exercises `STLCE_progress`, `STLCE_subst_preserves_typing`, and `STLCE_preservation`

## Typechecking algorithm
    1. `typechecker_extensions` has been finished, including the function `type_check`
    2. Examples were added for the new cases in `type_check`
    3. `type_checking_sound` and `type_checking_complete` have been proven

## Operational Semantics as a Coq function
    1. `stepf` was implemented
    2. `sound_stepf` and `complete_stepf` have been proven

# Extras


