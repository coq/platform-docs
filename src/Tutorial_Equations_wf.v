(** * Well-founded Recursion using Equations

  *** Summary

  [Equations] is a plugin for %\cite{Coq}% that offers a powerful support
  for writing functions by dependent pattern matching.
  In this tutorial, we focus on the facilities provided by Equations to
  define function using well-founded recursion and reason about them.

  In section 1, we explain the interrests and the principle of well-founded recursion.
  We then explain in section 2, how to define functions and how to reason about
  them using well-founded recursion and [Equations].
  In some cases, applying well-founded recursion can fail because information
  relevant to termination gets lost during recurion.
  In section 3, we discuss two such cases an how to go around the issues.

  *** Table of content

  - 1. Introduction to well-founded recursion
    - 1.1 The syntactic guard condition is limited
    - 1.2 Well-founded recursion
    2. Well-founded recursion and Equations
      2.1 Using a size argument
      2.2 Using a mesure
      2.3 Using a lexicographic order
      2.4 Using a custom well-founded relation
      2.5 Using the subterm relation ???
  - 3. Different tricks to work with well-founded recursion
    - 3.1 The inspect method
    - 3.2 map thing ???

  *** Prerequisites

  Needed:
  - We assume basic knowledge of Coq, and of defining functions by recursion
  - We assume basic knowledge of the Equations plugin and of obligations, e.g,
    as presented in the tutorials Equations: Basics and Equations: Obligations

  Not needed:
  - This tutorial discusses well-founded recursion but no prior knowledge
    about it is required: we will explain the concept
  - To simplify proofs involving arithmetics, we use the automation
    tactics [lia] and [auto with arith], but they can be used as black boxes

  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name coq-equations

*)

From Equations Require Import Equations.
From Coq Require Import List Arith Lia.
Import ListNotations.

Axiom to_fill : forall A, A.
Arguments to_fill {_}.


(** ** 1. Introduction to well-founded recursion

    For Coq to be consistent, all functions must be terminating.
    To ensure they are, Coq checks that they satisfy a complex syntactic
    criterion named the guard condition.
    Very roughly, the guard condition basically checks that all recursive call
    are performed on syntactically smaller instance.
    Though, while practical and powerful, this syntactic criterion is by nature
    limited and not complete: it can happen that functions can be proven terminating
    using size and mathematical arguments even though the guard fails to them as such.


    *** 1.1 The syntactic guard condition is limited

    A commen pitfall is when a recursive call is ofuscated, that is when
    it is not performed directly on a subterm [x], but on a subterm to which a
    function has been applied [f x], preventing the syntactic guard
    from checking that it is still indeed smaller.

    For instance, consider the function [nubBy] that given an equality
    test recursively filters out the duplicates of a list.
    The recursive call is not performed on the recursive argument [l] but
    on the list [filter (fun y => negb (eq x y)) l]. This prevent the syntactic
    from checking it is indeed smaller, and is hence rejected.
    Yet, we can prove that [filter] does not increase the size of a list, and hence
    that the recursive call is indeed performed on a "smaller" instance than [l]
    and that [nubBy] is terminating.
*)

Fail Equations nubBy {A} (eq : A -> A -> bool) (l : list A) : list A :=
nubBy eq []        => [];
nubBy eq (a :: l) => a :: nubBy eq (filter (fun b => negb (eq a b)) l).

(** Furthermore, it can also happen that the recursive structure of a definition
    do not follow the inductive structure of any datatypes, but instead
    fully rely on semantic arguments to decide which recursive call to
    perform, logically preventing the guard condition from checking it.

    A prime example is the Euclidean algorithm computing the gcd of
    [x] and [y] assuming that [x > y].
    It performs recursion on [x mod y] which is not a subterm of
    any recursively smaller arguments, as [gcd] does not match any inputs.
    It is well-founded and terminating for [lt], as we have tested
    that [y > 0] and we can prove that [x mod y < y].
    Consequently, there is no hope for a syntactic guard to accept [gcd] as
    its definition fully relies on theoretic reason to ensure termination.
*)

Fail Equations gcd (x y : nat) (H : x > y) : nat :=
gcd x y H with Nat.eq_dec y 0 => {
  | left _ => x
  | right _ => gcd y (x mod y)
}.


(** *** 1.2 Well-founded recursion

    It would be limiting if this kind of functions could not be defined.
    Fortunately, they can be using well-founded recursion.

    ### TODO MAKE CLEAN ###


    Informally, well-founded recursion bascially amounts to justifying termination by:
    - providing a "well-founded" relation [R : A -> A -> Prop], intuitively an
      order like [<] on natural numbers for which it is impossible to deacrease infinitely
    - proving that all the recursive calls are performed on smaller arguments according
      [R]

    More formally, a relation [R : A -> A -> Prop] is "well-founded" when


    Given a well-founded relation [R : A -> A -> Prop], defining a function
    [f] by well-founded recursion on [a : A] consists in defining [f] assuming that
    [f] is defined for all [a'] smaller than [a], that is such that [R a' a].
    When particularised to natural numbers and [<], this concept is sometimes
    known as "strong recursion / induction": when defining [f n] one assumes
    that [f] is defined/proven for all smaller natural numbers [n' < n].

    There are several methods to define functions by well-founded recursion using Coq.
    They all have their pros and cons, but as a general rules defining functions
    and reasoning using well-founded recursion can be tedious.

    For instance, consider the [Fix] construction of the standard library,
    which is a direct type theoretic definition of the concept of well-founded recursion:

    [[
      Fix : ∀ [A : Type] [R : A -> A -> Prop], well_founded R ->
            ∀ P : A -> Type, (∀ x : A, (∀ y : A, R y x -> P y) -> P x) ->
            ∀ x : A, P x
    ]]

    We can use it to define [gcd] as:
*)

Lemma gcd_oblig: forall (a b: nat) (NE: b <> 0), lt (a mod b) b.
Proof.
Admitted.

Definition gcd_Fix (x y : nat) : nat :=
  Fix lt_wf (fun _ => nat ->  nat)
      (fun (b: nat) (gcd_Fix: forall b', b' < b -> nat -> nat) (a: nat) =>
          match Nat.eq_dec b 0 with
          | left EQ => a
          | right NE => gcd_Fix (a mod b) (gcd_oblig a b NE) b
          end)
      y x.


(** However, doing so has several disadvantages.
    The function is much less transparent than a usual definition by [Fixpoint]
    as:
    - there is an explicit fixpoint combinator [Fix] in the definition
    - it forced us to use curryfication and the order of the arguments has changed
    - explicit proofs appear in the definition of the function,
      here through [gcd_oblig], as we must prove that recursive calls
      are indeed smaller.
    It can also make it harder to reason about the function, as the recursion scheme is no
    longer trivial.
    Moreover, as we had to use curryfication in our definition, we may need
    the axiom of function extensionally to reason about [gcd_Fix].

    Consequently, Equations provide a built-in mechanism to help us
    write functions and reason by well-founded recursion.
*)


(** ** 2. Well-founded recursion and Equations

    To define a function by well-founded recursion with Equations, one must add
    after the type of the function [by wf x R], where [x] is the term
    decreasing, and [R] the well-founded relation for which [x] decreases.

    For instance, the function [nubBy] terminates as the size of the list decrease
    in each recursive call according to the usual strict order [<] on [nat], [lt] in Coq.
    We hence, need to write [wf (size l) l] to define it by well-founded recursion:

    [[
    Equations nubBy {A} (eq : A -> A -> bool) (l : list A) : list A by wf (size l) lt  :=
    ]]

    Equations will then automatically:
    - 1. Search for a proof that [R] is well-founded, using type classes (a database)
         specific to [Equations] suitably named [WellFounded]
    - 2. It will then create an obligation to prove that each recursive call
         is performed on decreasing arguments, try to prove it automatically,
         and if it cannot do it on its own leave it to us to prove

    This allows to separate the proofs that the recursive call are smaller
    from the definition of the function, making it easier to read and define
    while dealing automatically with trivial cases.
    Moreover, it enables us to prove arguments directly in the proof mode using
    tactics.

    ** 2.1 Using a size argument

    Given an equality test, [nubBy] recursively filters out the duplicates
    of a list and only keeps the first occurrence of each element.
    It is terminating as the recursive call is performed on
    [filter (fun y => negb (eq x y)) xs] which is smaller than [xs] as
    [filter] can only remove elements.
    Consequently, to define [nubBy] by well-founded recursion, we need to
    add [wf (length l) lt].
*)

Equations? nubBy {A} (eq : A -> A -> bool) (l : list A) : list A by wf (length l) lt :=
nubBy eq []        => [];
nubBy eq (a :: l) => a :: nubBy eq (filter (fun b => negb (eq a b)) l).
Proof.
  eapply Nat.le_lt_trans.
  - apply filter_length_le.
  - auto with arith.
Qed.


(** Reasoning on functions defined by well-founded recursion with
    obligations is no different than when there is none.
    Using function elimination ([funelim]) we can prove our properties
    without having to redo the well-founded recursion.

    As examples, we show how to prove in a few lines that [nubBy] do
    remove all duplicates.
*)

Lemma In_nubBy {A} (eq : A -> A -> bool) (l : list A) (a : A)
               : In a (nubBy eq l) -> In a l.
Proof.
  funelim (nubBy eq l); simp nubBy; cbn.
  intros [Heq | H0].
  - rewrite Heq. left; reflexivity.
  - specialize (H _ H0). apply filter_In in H as [Inal eqa].
    right; assumption.
Qed.

Lemma nubBy_nodup {A} (eq : A -> A -> bool) (l : list A) :
      (forall x y, (eq x y = true) <-> (x = y)) -> NoDup (nubBy eq l).
Proof.
  intros Heq; funelim (nubBy eq l).
  - simp nubBy. constructor.
  - specialize (H Heq). simp nubBy. constructor.
    -- intros Hi.
       apply In_nubBy in Hi.
       apply filter_In in Hi as [_ Hneqx].
       specialize (Heq a a); destruct Heq as [_ Heqx].
       specialize (Heqx eq_refl); rewrite Heqx in Hneqx.
       inversion Hneqx.
    -- assumption.
Qed.

(** ** 2.2 Using a mesure

    For an example, consider a [gcd] function that does not require the assumption that
    [x > y] as below, by first checking if [x] or [y] is [0], and otherwise
    compare [x] and [y], and recall [gcd] with [x - y] or [y - x] depending
    which is the greater.
    It is terminating as the sum [x + y] is decreasing for the usual
    well-founded order on [nat], accounted for by [wf (x + y) lt]. *)

Equations? gcd (x y : nat) : nat by wf (x + y) lt :=
gcd 0 x := x ;
gcd x 0 := x ;
gcd x y with gt_eq_gt_dec x y := {
| inleft (left _) := gcd x (y - x) ;
| inleft (right refl) := x ;
| inright _ := gcd (x - y) y }.
Proof.
lia. lia.
Abort.

(** For further examples of how functional elimination works on well-founded
    recursion and how useful it is on complex definitions, we will now show a
    few properties of [gcd].
*)

Lemma gcd_same x : gcd x x = x.
Proof.
  funelim (gcd x x); try lia. reflexivity.
Qed.

Lemma gcd_spec0 a : gcd a 0 = a.
Proof.
  funelim (gcd a 0); reflexivity.
Qed.

Lemma mod_minus a b : b <> 0 -> b < a -> (a - b) mod b = a mod b.
Proof.
  intros.
  replace a with ((a - b) + b) at 2 by lia.
  rewrite <- Nat.Div0.add_mod_idemp_r; auto.
  rewrite Nat.Div0.mod_same; auto.
Qed.

Lemma gcd_spec1 a b: 0 <> b -> gcd a b = gcd (Nat.modulo a b) b.
Proof.
  funelim (gcd a b); intros.
  - now rewrite Nat.Div0.mod_0_l.
  - reflexivity.
  - now rewrite (Nat.mod_small (S n) (S n0)).
  - simp gcd; rewrite Heq; simp gcd.
    rewrite refl, Nat.Div0.mod_same.
    reflexivity.
  - simp gcd; rewrite Heq; simp gcd.
    rewrite H; auto. rewrite mod_minus; auto.
Qed.



(** ** 2.3 Using a lexicographic order

    Let's now consider the Ackerman function which is decreasing according to
    the usual lexicographic order on [nat * nat], [(<,<)] which is accessible
    as [<] is, and the lexicographic combination of well-founded relations is too.
    You can define the lexicographic order and automatically derive a proof
    it is well-founded using the function [Equations.Prop.Subterm.lexprod].
    As we can see, with this order, once again no obligations are left to prove as
    Coq can prove on its own that [(m, (ack (S m) n)) <lex (S m, S n)] and
    [(S m, n) <lex (S m, S n)].
*)

Equations ack (m n : nat) : nat by wf (m, n) (Equations.Prop.Subterm.lexprod _ _ lt lt) :=
ack 0 n := S n;
ack (S m) 0     := ack m 1;
ack (S m) (S n) := ack m (ack (S m) n).


(** In principle, we should be able to reason about [ack] as usual using [funelim].
    Unfortunately, in this case, [funelim] runs for very long if it terminates.
    You can check it out by uncommenting the timed-out [funelim] below:
*)

Definition ack_min {m n} : n < ack m n.
Proof.
  (* timeout 5 (funelim (ack m n)). *)
Abort.

(** The reason is that [funelim] does much more than just applying [ack_elim].
    In particular, it does diverse generalisation and simplification that pose
    problem here.
    This a known issue and it is currently being investigated and fixed.

    There are two main solutions to go around similar issue depending on your case.

    If your pattern is fully generic, i.e. of the form [ack m n], you can
    apply the [ack_elim] lemma directly.
    Though note, that in this case you may need to generalise the goal by hand,
    in particular by equalities (e.g. using the remember tactic) if the function
    call being eliminated is not made of distinct variables.
*)
Definition ack_min {m n} : n < ack m n.
Proof.
  apply ack_elim; intros.
  - constructor.
  - auto with arith.
  - eapply Nat.le_lt_trans; eassumption.
Qed.

(** However, if your pattern is partially specialised like [ack 1 n],
    it is better to finish reproducing the pattern using [induction].
    Indeed, [ack_elim] "reproduces" the full pattern, that is, it generalise [1]
    and tries to prove [ack m n = 2 + n] by induction, creating cases like
    [ack (S m) n] which clearly are not warranted here.
*)

Definition ack1 {n} : ack 1 n = 2 + n.
Proof.
  (* If we apply [ack_elim], we get unwarranted cases *)
  apply ack_elim.
  Restart.
  (* So we reproduce the pattern with induction *)
  induction n. all: simp ack.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.



 (** ** 2.4 Using a custom well-founded relation *)

 (* ### TODO ### *)

(** ** 2.5 Using the subterm relation *)



(** ** 3. Different methods to work with well-founded recursion

    When defining a function, it can happen that we loose information
    relevant to termination when matching a value, and that we then get
    stuck trying to prove termination.
    In this section, we discuss two such example an methods to go around the issue.

    *** 3.1 The inspect method

    Working with a particular well-founded order [lt], it may happen that
    we have a choice function [f : A -> option A] that for any [(a :A)]
    return a strictly smaller element if there is one.
    This situation is axiomatised by the following context :
*)

Section Inspect.

  Context {A : Type} {lt : A -> A -> Prop} `{WellFounded A lt}
          (f : A -> option A) (decr_f : forall n p, f n = Some p -> lt p n).

(** In this case, given an element (a : A), we may be interested in
    computing the associated decreasing chain of elements starting from
    [a].
    Naively, we would like to do so as below.
    That is check if there is an element smaller than [a] by matching [f a]
    with a with clause, if there is one [Some p] then return [p] added to the
    chain starting with [p], i.e., our recursive call [f_sequence p], and otherwise
    stop the computation.
*)

  Equations? f_sequence (a : A) : list A by wf a lt :=
  f_sequence a with (f a) := {
    | Some p => p :: f_sequence p;
    | None => nil
    }.
  Proof.
    apply decr_f.
    (* What to do now ? *)
  Abort.

(** Unfortunately, as we can see, doing so we generate an unprovable
    obligation as we do not remember information about the call to [f n] being
    equal to [Some p] in the recursive call [f_sequence p].

    To go around this issue and remember the origin of the pattern,
    we can wrap our match with the [inspect] function, which simply packs a
    value with a proof of an equality to itself.
    In other words, given an element [(a : A)], [inspect (a)] returns the
    elements [(a, eq_refl) : {b : A | a = b}].
*)

  Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

  Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

(** In our case, wrapping with [inspect] means matching first on
    [inspect (f a)] then on the first component which is by definition [f a],
    rather than directly on the term [f a].
    This may seem pointless as if one destruct [f a] in an equality
    [f a = f a], one would surely get [Some p = Some p] and learn nothing?
    The trick here is that [inspect (f a)] returns an object of type
    [{b : A | f a = b}], type in which [f a] is a fixed constant.
    Consequently, destructing the first component, in our case [f a],
    will only affect the right-hand side of the equality, and we will
    indeed get the desired equality [f a = Some p].
    As it can be seen below it works perfectly, and Coq is even able to
    prove the call is terminating on its own leaving us no obligations
    to fill.
*)

  Equations f_sequence (a : A) : list A by wf a lt :=
    f_sequence a with inspect (f a) := {
      | Some p eqn: eq1 => p :: f_sequence p;
      | None eqn:_ => List.nil
      }.

End Inspect.


(** 2.2 ### TODO ###
*)