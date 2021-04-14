# Group Identification

 - Afonso Ribeiro, 86752, afonsoribeiro@tecnico.ulisboa.pt
 - Baltasar Dinis, 89416, baltasar.dinis@tecnico.ulisboa.pt
 - João Borges, 89482, joao.p.l.borges@tecnico.ulisboa.pt

# Implemented Features

## Extend Imp
    - `com` datatype has been extended
    - A new notation has been defined
    - The relational semantics have been extended
    - Examples `ceval_example_choice1`, `ceval_example_choice2` and `ceval_example_choice3` have been proved using the relational semantics.
    - Examples `ceval_example_choice1`, `ceval_example_choice2` and `ceval_example_choice3` have been proved using the relational semantics.

## Properties of Non-deterministic choice
The following properties have been proven.
    - `choice_idempotence`
    - `choice_comm`
    - `choice_assoc`
    - `choice_seq_distr_1`
    - `choice_seq_distr_2`
    - `choice_congruence`

## Step-Indexed Evaluator

`ceval_step` has been extended to handle non-deterministic choice.

The following properties have been proven.  (TODO)
    - `ceval_step__ceval`
    - `ceval_step_more`
    - `ceval__ceval_step`
    - `ceval_and_ceval_step_coincide`

# Extras
TODO: Identify and describe additional work that you have done,
      so that it can be considered for extra credits.
