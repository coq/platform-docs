(** * Tutorial Equations : Dealing with indexed inductive types

  *** Summary:

  [Equations] is a plugin for Coq that offers a powerful support
  for writing functions by dependent pattern matching.
  In this tutorial, we focus on the facilities provided by [Equations] to
  define function by dependent pattern matching on indexed inductive types,
  and reason about them.

  In Section 1, we discuss indexed inductive types on the particularities
  of defining and reasoning about functions defined by pattern matching over
  them.
  In section 2, we discuss the no confusion property and how it enables to
  automatically discard impossible cases for indexed inductive types.
  In section 3, we discuss the particularity that indexed types have
  to particularise indices when matching, and issues that can arise.

  *** Table of content
  - 1. Reasoning about indexed inductive types
  - 2. The No-Confusion property
  - 3. Unifying Indices and Inaccessible Patterns

  *** Prerequisites:

  Needed:
  - We assume basic knowledge of Coq, of and defining functions by recursion
  - We assume basic knowledge of the plugin Equations, e.g, as presented
    in the tutorial Equations : Basics

  Not needed:
  - We discuss here indexed inductives but we recall the concept so previous
    knowledge about them is not needed

  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name coq-equations

*)

From Equations Require Import Equations.

 (** ** 1. Reasoning about indexed inductive types

    Indexed inductive types are particular kind of inductive definitions
    that consist in defining not one single inductive type but a family
    of linked inductive types.
    The most well-known example of indexed inductive types are vectors.
    Given a fixed parameter [A : Type], vectors define a familly of inductive
    types [vec A n : Type] indexed by natural numbers [n : nat] representing
    the lengths of the vectors.
    Vectors have two constructor.
    The first constructor [vnil : vec A 0] represent the empty vector,
    logically of size [0].
    Given an element [a:A] and a vector [v : vec A n] of size [n], the
    second constructor [vcons] constructs a vector of size [n+1]
    [vcons a n v : vec A (S n)], intuitively by adding [a] at the beginning of [v].
*)

Inductive vec A : nat -> Type :=
  | vnil  : vec A 0
  | vcons : A -> forall (n : nat), vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

(** The difference between a parameter and an indice is that a parameter is
    constant over all the constructors, whereas an indice changes in the
    constructor.
    For instance, in the definition of vectors the type [A] is a parameter
    as it is constant in all the constructors, but [n:nat] is an indice as
    [vcons] relates two different types of the family, [vec A n] and [vec A (S n)].

    Reasoning about indexed inductive types like vectors is a bit more
    involved than for basic inductive types like lists as the indices can
    matter.
    Noticeably pattern matching on constructors of indexed inductive types
    like [vec n A] may particularise the indices.
    For instance, matching a vector [v : vec A n] to [vnil] forces the
    value [n] to be [0] and to [vcons] to be of the form [S m] for some integer [m].
    Consequently, when writing a function on an indexed inductive type,
    we must also specify the form of the indices when pattern matching.

    For instance, consider the definition of [vmap] and [vapp] :
*)

Equations vmap {A B} (f : A -> B) (n : nat) (v : vec A n) : vec B n :=
vmap f 0 vnil := vnil ;
vmap f (S n) (vcons a n v) := vcons (f a) n (vmap f n v).


Equations vapp {A} (n : nat) (v : vec A n) (m : nat) (v' : vec A m) : vec A (n+m) :=
vapp 0 vnil m v' :=  v';
vapp (S n) (vcons a n v) m v' := vcons a (n+m) (vapp n v m v').


(** Reasoning on indexed inductive is not very different than reasoning
    on regular inductive types except that we have to account for indices,
    which can in some cases cause some overheads.

    For basic properties as below, it makes no differences:
*)

Definition vmap_comp {A B C} (f : A -> B) (g : B -> C) (n : nat) (v : vec A n) :
           vmap g n (vmap f n v) = vmap (fun a => g (f a)) n v.
Proof.
  funelim (vmap f n v); simp vmap.
  - reflexivity.
  - f_equal. apply H.
Qed.

Lemma vmap_cong {A B n} (f f': A -> B) (v : vec A n) (Heq : forall (a:A), f a = f' a)
      : vmap f n v = vmap f' n v.
Proof.
  funelim (vmap f n v); simp vmap.
  - reflexivity.
  - now rewrite Heq, (H f').
Qed.

(** However, it can make some differences when operations on indices are
    involved as indices are relevant for simplification.
    For instance, if we try to prove that [vmap] respects [vapp] as below,
    in the [vcons] case simplification fails to simplify [vmap f (S n + m) ...].
    The reason is that the simplification rule associated to [vcons] is
    [vmap f (S n) (vcons a n v) = vcons (f a) n (vmap f n v)].
    Hence, [simp] can not simplify [vmap] until [S n + m] has been
    simplified to [S (n+m)] using [cbn].
    It then behaves as usual.
 *)

Definition vmap_vapp {A B} (n m : nat) (f : A -> B) (v : vec A n) (v' : vec A m) :
           vmap f (n+m) (vapp n v m v') = vapp n (vmap f n v) m (vmap f m v').
Proof.
  funelim (vmap f n v); simp vapp.
  - reflexivity.
  - (* Here we can see [simp] fails to simplify [vmap f (S n + m) ...] as
      [S n + m] is not of the form [S x] for some [x : nat].              *)
    simp vmap.
    (* We need to first simplify [+] using [cbn] :                         *)
    cbn.
    (* We can now simplify *)
    simp vmap vapp. now rewrite H.
Abort.

(** In practice, indices are mostly inferable, so it is usually possible to
    make them implicit.
    It has the advantage to make the code much more concise.
    For instance, for [vec], it enables to write much shorter definitions
    of [vmap] and [vapp]:
*)

Arguments vcons {_} _ {_} _.

Equations vmap' {A B n} (f : A -> B) (v : vec A n) : vec B n :=
vmap' f vnil := vnil ;
vmap' f (vcons a v) := vcons (f a) (vmap' f v).

Equations vapp' {A n m} (v : vec A n) (v' : vec A m) : vec A (n+m) :=
vapp' vnil v' :=  v';
vapp' (vcons a v) v' := vcons a (vapp' v v').

(** Setting indices to be implicit also makes them implicit in proofs.
    Doing so is not an issue even in the case of [vmap_vapp] where
    we need to simplify indices to reduce.
    If we think a term should have been reduced but hasn't been because of
    indices, we can always make them temporally explicit to check.
    We can do so by defining an alias for the functions using the tactic
    [set (name_function_ex := @(name_function _ _ _))] with an underscore
    for the arguments we do not want to make explicit.
    After inspecting the goal, you can just erase the tactic or unfold
    the notations.
    As an example, let's reprove [vmap_vapp] :
*)

Definition vmap_vapp {A B n m }(f : A -> B) (v : vec A n) (v' : vec A m) :
           vmap' f (vapp' v v') = vapp' (vmap' f v) (vmap' f v').
Proof.
  funelim (vmap' f v).
  - reflexivity.
  - simp vapp'.
    (* If we think [vmap' f (vcons a ...)] should have been simplified,
       we can set an alias to check if the indice is of the form [S x]  *)
     set (vmap'_ex := @vmap' _ _).
     (* After inspecting the goal, you can just erase the tactic
        or unfold the alias                                           *)
     cbn. unfold vmap'_ex.
    (* It is now possible to simplify *)
    simp vmap' vapp'. f_equal. apply H.
Abort.


(** ** 2. The No-Confusion property

    Having information directly part of typing, like the length for vector,
    can have advantages.
    Most noticeably, it can be used to exclude invalid cases.
    For instance, consider the function tail that returns the last element.
    In the case of list, the [tail] function had to return a term of type
    [option A] as were no insurance that the input would not be the empty list.
    This is not necessary for vectors as we can use the indice to ensure
    there is at least one element by defining tail as a function of type
    [vec A (S n) -> vec A n].
    This can be implemented very directly with Equations as Equations can
    deduce on its own that the [vnil] case is impossible :
*)

Equations vtail {A n} (v : vec A (S n)) : vec A n :=
vtail (vcons a v) := v.

(** Similarly, we can give a very short definition of a function computing
    the diagonal of a square matrix of size [n * n] represented as a
    vector of vector [v : vector (vector A n) n)].
    On the empty matrice it returns the empty list.
    On a matrice [(vcons (vcons a v) v')] of size [(S n) x (S n)] representing

    [[
              | a |     v     |
              |---------------|
              |       v'      |
              |               |
    ]]

    it returns [a] added to the diagonal of vmap [vtail v'], that is
    [v'] where the first column has been forgotten.
    Note, that in this case, pattern match on [n] needs to be added to help
    Coq see it is strictly decreasing.
*)

Equations diag {A n} (v : vec (vec A n) n) : vec A n :=
diag (n:=O) vnil := vnil ;
diag (n:=S _) (vcons (vcons a v) v') := vcons a (diag (vmap vtail _ v')).

(** To do so, the pattern-matching compiler behind [Equations] uses unification
   with the theory of constructors to discover which cases need to be
   considered and which are impossible.
   This powerful unification engine running under the hood permits to write
   concise code where all uninteresting cases are handled automatically.
   Importantly, it relies on the property of no-confusion, that is
   that two different constructors of an inductive can not be equal,
   here for [nat], [0 = S n -> False].
   The no confusion property can be generated automatically by [Equations]
   using the command [Derive].
*)

Derive NoConfusion for nat.

(** You may notice that we have derive the no confusion property for [nat]
    after defining [tail] and [diag], even though it supposed the be necessary.
    This is because it is already defined for [nat] by default, so
    there was actually no need to do derive it in this particular case.

    Thanks to [funelim], reasoning for this kind of programs is as usual
    to the difference that, as for function definitions, we only need to
    deal with the cases that are possible:
*)

Arguments vmap {_ _} _ {_} _.

Definition vmap_diag {A B n} (f : A -> B) (v : vec (vec A n) n) :
           vmap f (diag v) = diag (vmap (fun v' => vmap f v') v).
Proof.
  (* We start by induction, simplify and use the induction hypothesis *)
  funelim (diag v); simp vmap diag. 1: easy. rewrite H. f_equal.
  (* We simplify the goal by collapsing the different [vmap] using [vmap_comp],
     and notice the proof boils down to commutativity if [vtail] and [vmap] *)
  rewrite ! vmap_comp. f_equal. apply vmap_cong.
  (* There is left to prove by function elimination on [vtail] or [vmap]  *)
  intro v2. funelim (vtail v2). simp vmap vtail. reflexivity.
Qed.


(* TALK ABOUT NO CONFUSION FOR VEC *)

Derive Signature NoConfusion NoConfusionHom for vec.


(** ** 3. Unifying Indices and Inaccessible Patterns

    A particularity of indexed inductive type is that during pattern-matching
    indices may be particularises to values like variables or terms of
    the form [(f (...))], where [f] is not a constructor of an inductive type
    like [O] or [S].

    The most well-known of example of that is equality [| eq A x : A -> Prop |]
    that is _parameterized_ by a value [x] of type [A] and _indexed_
    by another value of type [A].
    Its single constructor states that equality is reflexive, so the only way
    to build an object of [eq x y] is if [x] is definitionally equal to the
    variable [y].

    [[
      Inductive eq (A : Type) (x : A) : A -> Prop :=
      | eq_refl : eq A x x.
    ]]

    Pattern-matching on the equality then unifies the indice [y] with the
    parameter [x], that is to a variable.
    Consequently, we have determined the _value_ of the pattern [y], and it is
    no longer a candidate for refinement with available constructors like
    [0] or [S n].
    Such a pattern is said to be "inaccessible", and needs to be indicated
    by writing [?(t)] to tell Equations not to refine it.

    As an example, to prove the symmetry of equality we pattern
    match on an equality [H : x = y], which unify [y] the variable [x]
    that we indicate by writing [eq_sym x ?(x) eq_refl].
    The goal now being [x = x], it now holds by [eq_refl].
*)

Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym x ?(x) eq_refl := eq_refl.

(** In practice, when the values determined are variable as in [eq_sym],
    the inaccessibility annotation is optional and we can simply write [x]
    rather than [?(x)].
*)

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans x x x eq_refl eq_refl := eq_refl.

(** For an example, where the [?(t)] notation is needed consider this inductive
    definition of the image.
    It has one constructor that for all elements [a:A] generates an element
    in its image by [f], [Imf f (f a)].
    Intuitively, it means that there is an object in [Imf f x] provided
    that [x] is of the form [f a] for some [a].
*)

Inductive Imf {A B} (f : A -> B) : B -> Type
  := imf (a : A) : Imf f (f a).

(** Pattern-matching on [im : Imf f t] particularise [t] to be of the form
    [f a] for some [a].
    As [f] is not a constructor, [f a] is inaccessible and we need to write
    as [?(f a)] in the pattern matching to prevent [Equations] to refine [f]
    with available constructors.
    In this case, it is essential as [f a] is not a variable.
    As an example, we can write a function returning the [a] associated
    to on object in the image :
*)

Equations inv {A B} (f : A -> B) (t : B) (im : Imf f t) : A :=
inv f ?(f s) (imf f s) := s.
