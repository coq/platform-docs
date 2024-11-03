(** * Bidirectionality Hints

  *** Summary

  An explanation of bidirectionlity hints.
  After presenting the requisite background on bidirectional typing and
  existential variables in Coq, we will see how bidirectionality hints affect
  type checking of function applications, and we will illustrate with simple
  examples.

  *** Contents

  - 1. Bidirectional typing
  - 2. Existential variables
  - 3. Bidirectionality hints
  - 4. Examples

*)

(**
The following function signature will be our running example:
[[
Parameter f : forall (x : A), B x -> C x.
]]

To start, we must understand the basics of how type checking works in Coq.

** Bidirectional typing

Coq uses bidirectional typing, an approach to type systems that interleaves
type checking with type inference. A bidirectional type system replaces the
usual typing judgement [e : T] with two judgements: _type checking_
[e ↓ T] where [T] is an input and _type inference_ [e ↑ T]
(also called _type synthesis_ in the literature) where [T] is an output.
Making inputs and outputs explicit enables an algorithmic interpretation of the
typing rules: a bidirectional type system is a way to present a type checking
and a type inference algorithm.

Function application is usually associated with a rule for type inference ([↑]):

[[[
f ↑ forall (x : A), B x -> C x
a ↓ A     b ↓ B a
----------------- app-syn
  f a b ↑ C a
]]]

We can read that typing rule as follows:

- 1. _infer_ the type of the function [f] ([f ↑ forall (x : A), B x -> C x]),
    usually from the context;
- 2. _check_ the arguments [a], [b] with the argument types [A], [B a] that we just inferred
    ([a ↓ A], [b ↓ B a]);
- 3. output the result type [C a] as the _inferred_ type for [f a b]
     ([f a b ↑ C a]).

What if we want to check with a type, rather than infer it?
The subsumption rule turns inference ([↑]) into checking ([↓]):
to check that [e] has type [T] ([e ↓ T]),
infer a type [T’] ([e ↑ T’]), then *unify* [T’] with [T]
([T’ ≡ T]).

[[[
e ↑ T’     T’ ≡ T
----------------- syn-check
      e ↓ T
]]]

The two rules above combine into the following rule for checking an application [f a b]:

[[[
f ↑ forall (x : A), B -> C x
a ↓ A     b ↓ B a    C a ≡ T
---------------------------- (1)
         f a b ↓ T
]]]

To check whether [f a b] has a given type [T]:

- 1. infer the type of [f];
- 2. check the arguments [a], [b] with their respective types [A], [B a];
- 3. unify [C a] and [T].

** Existential variables

To a first approximation, the unification judgement ([T’ ≡ T]) denotes
an equivalence relation between types.

This story is further complicated in Coq by the presence of
{{https://coq.inria.fr/doc/V8.20.0/refman/language/extensions/evars.html} existential variables}.
To avoid fully spelling out all terms in Coq, you can write
holes ([_]) instead to let them be inferred. They are replaced with fresh
existential variables with names like [?u] right before type checking.
Existential variables will then be instantiated during unification [?u ≡ T].

Thus, the typing rules above are interpreted statefully: there is a global set of
bindings for existential variables [?u := M] which is read and updated during
unification. In particular, the order in which unification judgements [T’ ≡ T]
are evaluated matters.

For example, consider the following two unification requests:
[[
?u ≡ true
0 ≡ if ?u then 0 else 1
]]

Unifying [?u ≡ true] first allows the second unification to succeed since
[if true 0 else 1] reduces to [0]. In contrast, unifying [0 ≡ if ?u then 0 else 1]
will fail if we haven't instantiated [?u] yet, because [if ?u then 0 else 1]
is stuck.

** Bidirectionality hints

Bidirectionality hints indicate when unification with the result type should happen
during type-checking of a function application. By default, that happens
at the end, after having type-checked all of the arguments. This corresponds
to the type checking rule above.

A bidirectionality hint moves that unification step earlier,
Bidirectionality hints are declared using the [Arguments] command,
as a [&] symbol. For example:
[[
Arguments f _ & _.
]]

The hint [f _ & _] makes unification happen after type checking the first
argument, resulting in the following type checking rule:

[[[
f ↑ forall (x : A), B x -> C x
a ↓ A     C a ≡ T     b ↓ B a
----------------------------- (2)
         f a b ↓ T
]]]
*)

(** ** Examples *)

Section Example.

(** Let us demonstrate the difference with two examples: one does not require the hint, the other does.
  Both use the same definitions for the types [A], [B], and [C] below, where [B] and [C] pattern match
  on the first argument [x : A]: *)

Let A : Type := bool.
Let B (x : A) : Type := if x then bool else nat.
Let C : A -> Type := B.

Variable f : forall (x : A), B x -> C x.

(** *)

Section Example1.

(** The expression [f _ (0 : B false) : nat] type checks without
bidirectionality hints, but fails with the hint [f _ & _]. *)

(** We replace the hole in the first argument with a fresh existential variable [?x].
With no bidirectionality hint, type checking [f _ (0 : B false) ↓ nat] proceeds as follows:
- 1. check the first argument [?x ↓ bool]: it is a hole so checking succeeds without doing anything;
- 2. check the second argument [(0 : B false) ↓ B ?x]: the type annotation gives us the inferred type `B false`,
    which is unified with the checked type `B ?x`, and we unify `false` with `?x`;
- 3. unify [C ?x ≡ nat]: it succeeds because we previously unified `?x` with `false`.
 *)

(* No bidirectionality hint. *)
Check (f _ (0 : B false) : nat).

(** With a bidirectionality hint, type checking proceeds as follows:
- 1. check the first argument [?x ↓ bool] (same as before, do nothing);
- 2. unify [C ?x ≡ nat], that is [(if ?x then bool else nat) ≡ nat],
    which fails because [?x] is still unknown. *)

(* Add bidirectionality hint. *)
Arguments f _ & _.
Fail Check (f _ (0 : B false) : nat).

(** *)

End Example1.

(** *)

Section Example2.

(** The expression [f _ 0 : C false] type checks with the hint
[f _ & _] but fails without. *)

(** With no bidirectionality hint:
- 1. check the first argument [?x ↓ bool] (same as before, do nothing);
- 2. check the second argument [0 ↓ B ?x]: it is a constant so it has an inferred type `nat`,
    which is unified with the checked type [B ?x], and that fails because `?x` is still unknown. *)

(* No bidirectionality hint. *)
Fail Check (f _ 0 : C false).

(** With the bidirectionality hint:
- 1. check the first argument [?x ↓ bool] (same as before, do nothing);
- 2. unify [C ?x ≡ C false], which unifies [?x ≡ false];
- 3. check the second argument [0 ↓ B ?x]: it has an inferred type `nat`,
    which is unified with the checked type [B ?x],
    and that succeeds we previously unified `?x` with `false`. *)

(* Add bidirectionality hint. *)
Arguments f _ & _.
Check (f _ 0 : C false).

(** *)

End Example2.

(** *)

End Example.
