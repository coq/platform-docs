(** * Prop, SProp and hProp

  *** Summary

  An explanation of the differences and subtleties of Prop, SProp and hProp

  *** Contents
  - 1. Overview and first definitions
  - 2. Impredicativity and propositional resizing


*)

(** * 1. Overview an first definitions
Being an hProp (homotopic proposition or mere proposition)
  is a internal predicate, usually defined as follows*)

Definition ishProp A := forall x y : A, x = y.

Definition hProp := { A : Type & ishProp A }.

(** An hProp is a Type with at most one element **)

(** SProp (strict propositions) and Prop (propositions) are both sorts of the language,
  meaning elements can appear on the right side of ":" *)

Parameter P : SProp.
Parameter p q : P.

Parameter P' : Prop.
Parameter p' q' : P'.

(** You can also form elements through inductive definition *)

Inductive and (A B : Prop) : Prop :=
  | conj : A -> B -> and A B.
Inductive sand (A B : SProp) : SProp :=
  | sconj : A -> B -> sand A B.

(** Sprop results from a syntaxic approach to hProp,
  types with at most one elements **)

Inductive SPPBox {P : SProp} : Prop :=
  | SPPbox (p : P) : SPPBox.

Check (eq_refl : eq (SPPbox q) (SPPbox p)).
(* Since there is no coercion from SProp to Type,
  we add a conversion manually to use equality *)

Fail Check (eq_refl : eq q' p').


(** Reflexivity is not a proof of equality of proofs of a proposition,
 while it is for (boxed) proofs of a strict proposition.
 In general, the former have no proof of equality at all,
 and while equality can always be shown for homotopic proposition,
 the proof is not usually reflexivity *)

(** Prop is meant to be remove when extracting a program.
  Its most notable property is singleton elimination.
  In principle, a sort can only be eliminated in itself,
  that is, for an inductive I defined in a sort T,
  a pattern matching on I will only work to create a term in a type of sort T.
  However Rocq implements large elimination, meaning Types can be eliminated in all sorts,
  and singleton elimination, meaning if an inductive in Prop has "less than one" constructor,
  it can be eliminated in Type. *)

Inductive ex_singleton0 : Prop :=. (* having no constructor is few enough *)

Inductive ex_singleton1 : Prop :=
  | cons1 : ex_singleton1. (* having a single one as well *)

Inductive ex_not_singleton0 : Prop :=
  | cons00 : ex_not_singleton0
  | cons01 : ex_not_singleton0.  (* having two constructors is too much *)

Inductive ex_not_singleton1 : Prop :=
  | cons10 : bool -> ex_not_singleton1. (* so is it the case when they are package up as one *)

Inductive ex_not_singleton2 : Prop :=
  | cons20 : unit -> ex_not_singleton2.

 (* An type as an argument to the constructor is forbidden,
  even if it only has one constructor *)

Inductive ex_singleton2 : Prop :=
  | cons2 : P' -> ex_singleton2. (* A Prop is fine however *)

Inductive ex_singleton3 : Prop :=
  | cons3 : P -> ex_singleton3. (* So is a SProp *)

Inductive ex_singleton4 : Prop :=
  | cons4 : P -> P -> P' -> ex_singleton4. (* And so is a mix *)

(** Note that Prop also eliminates in SProp in all cases *)
(** SProp also has a form of singleton elimination *)

Inductive ex_Ssingleton : SProp :=. (* This is the only case in Rocq *)

(** 2. Impredicativity and propositional resizing *)

(** Another notable feature of Prop and SProp is impredicativity,
  which Type doesn't implement *)

Parameter A : Type.
Parameter B : A -> SProp.
Parameter B' : A -> Prop.

Check (forall a : A, B a) : SProp.
Check (forall a : A, B' a) : Prop. (* Only the sort of the codomain matter *)

Universe i j.
Constraint i < j.
Parameter C : Type@{j}.
Parameter T : C -> Type@{i}.

Fail Check (forall c: C, T c) : Type@{i}.

(** This makes it possible to create the following inductive proposition,
  which enjoys singleton elimination *)

Inductive Acc X R (x : X) : Prop :=
  | Acc_intro : (forall y, R x y -> Acc X R y) -> Acc X R x.

(** hProp can also enjoy a form of impredicativity, through the form of propositional resizing.
  Propositional resizing is an Axiom which states that hProp whose type live in some universe,
  are equivalent to a hProp which lives in Set, the lowest universe level *)

