(** * Well-founded Recursion using Equations

  *** Summary

  [Equations] is a plugin for %\cite{Coq}% that offers a powerful support
  for writing functions by dependent pattern matching.
  In this tutorial, we focus on the facilities provided by Equations to
  define function using well-founded recursion and reason about them.

  In section 1, we explain the interests and the principle of well-founded recursion.
  We then explain in section 2, how to define functions and how to reason about
  them using well-founded recursion and [Equations].
  In some cases, applying well-founded recursion can fail because information
  relevant to termination gets lost during recursion.
  In section 3, we discuss two such cases a how to go around the issues.

  *** Table of content

  - 1. Introduction to well-founded recursion
    - 1.1 The syntactic guard condition is limited
    - 1.2 Well-founded recursion
    2. Well-founded recursion and Equations
      2.1 Using a size argument
      2.2 Using a measure
      2.3 Using a lexicographic order
      2.4 Using a custom well-founded relation
  - 3. Different tricks to work with well-founded recursion
    - 3.1 The inspect method
    - 3.2 Improving recursion hypotheses

  *** Prerequisites

  Needed:
  - We assume basic knowledge of Coq, and of defining functions by recursion
  - We assume basic knowledge of the Equations plugin and of obligations, e.g,
    as presented in the tutorials Equations: Basics and Equations: Obligations

  Not needed:
  - This tutorial discusses well-founded recursion but no prior knowledge
    about it is required: we will explain the concept
  - To simplify proofs involving arithmetic, we use the automation
    tactics [lia] and [auto with arith], but they can be used as black boxes

  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name coq-equations

*)

From Equations Require Import Equations.
From Coq Require Import List Arith Lia.
Import ListNotations.


(** ** 1. Introduction to well-founded recursion

    For Coq to be consistent, all functions must be terminating.
    To ensure there are, Coq checks that they satisfy a complex syntactic
    criterion named the guard condition.
    Very roughly, the guard condition basically checks that all recursive call
    are performed on syntactically smaller instance.
    Though, while practical and powerful, this syntactic criterion is by nature
    limited and not complete: it can happen that functions can be proven terminating
    using size and mathematical arguments even though the guard fails to them as such.


    *** 1.1 The syntactic guard condition is limited

    A common pitfall is when a recursive call is obfuscated, that is when
    it is not performed directly on a subterm [x], but on a subterm to which a
    function has been applied [f x], preventing the syntactic guard
    from checking that it is still indeed smaller.

    For instance, consider the function [nubBy] that given an equality
    test recursively filters out the duplicates of a list.
    The recursive call is not performed on the recursive argument [l] but
    on the list [filter (fun y => negb (eq x y)) l]. This prevents the syntactic
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

    **** Informally

    It would be limiting if this kind of functions could not be defined.
    Fortunately, they can be using well-founded recursion.

    Informally, defining a function [f] by well-founded recursion basically
    amounts to a usual definition expect that we justify termination by:
    - Providing a "well-founded" relation [R : A -> A -> Prop], informally a relation
      for which there is no infinitely decreasing sequence.
      For instance, the strict order on [nat], [< : nat : -> nat -> nat] is well-founded
      as starting from [m] it impossible to decrease infinitely, there is a point
      at which you must reach [0].
    - Proving that all the recursive calls are performed on smaller arguments
      according to [R]

    This enables us to justify termination of our function [f] as it is impossible
    to decrease forever and all recrusive call are smaller, so whatever the input [f]
    must terminate at a point or another.

  **** More Formally

    Defining a well-founded relation by "no having infinitely decreasing sequence"
    is not very useful as #TODO
    Consequently, in type theory, we use a slighlty stronger notion, that is
    "accessibility", to define a well-founded relations [R : A -> A -> Prop].
    An element [a : A] is accessible for [R], denoted [Acc R a] when for
    all [a' : A] smaller than [a], [a'] is itself accessible.
    Intuitevely, it ensures constructively that they are no decreasing sequence
    as the only ways for an element [a] to be accessible are that:
    - 1. There are no elements smaller than [a], so you cannot decrease further
    - 2. All elements smaller than [a] are accessible, so there are no infinitely
         decreasing sequence from them, and hence from [a].
*)
Print Acc.


(** We then say a relation is well-founded, when forall (a : A), [R] is
    accessible at [a], i.e. [Acc R a].
    It ensures that wherever we start at, we can not decrease forever.
*)

Print well_founded.

(** Given a well-founded relation [R : A -> A -> Prop], defining a function
    [f] by well-founded recursion on [a : A] consists in defining [f] assuming that
    [f] is defined for all [a'] smaller than [a], that is such that [R a' a].
    When particularised to natural numbers and [<], this concept is sometimes
    known as "strong recursion / induction": when defining [f n] one assumes
    that [f] is defined/proven for all smaller natural numbers [n' < n].

    **** In practice

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

    The function is much less transparent than a usual definition by [Fixpoint] as:
    - there is an explicit fixpoint combinator [Fix] in the definition
    - it forced us to use curryfication and the order of the arguments has changed
    - explicit proofs appears directly in the definition of the function (though Program can help)

    Moreover, behind the scene the function is defined by recursion on the
    accessibility proof, which forces us in turn to do a recursion on the
    accessibility proof to reason about the function.
    It makes harder to reason about the function, as the recursion
    scheme no longer follow the intuitive definition.
    Furthermore, as we had to use curryfication in our definition, we may need
    the axiom of function extensionally to reason about [gcd_Fix].


    Considering this different defaults, Equations provides a built-in mechanism
    to help us write functions and reason by well-founded recursion.
*)


(** ** 2. Well-founded recursion and Equations

    To define a function by well-founded recursion with Equations, one must add
    after the type of the function [by wf x R], where [x] is the term
    decreasing, and [R] the well-founded relation for which [x] decreases,
    and then define the function as usual.

    For instance, the function [nubBy] terminates as the size of the list decrease
    in each recursive call according to the usual strict order [<] on [nat], [lt] in Coq.
    We hence, need to write [wf (size l) l] to define it by well-founded recursion:

    [[
    Equations nubBy {A} (eq : A -> A -> bool) (l : list A) : list A by wf (length l) lt :=
    nubBy ... := usual_def;
    nubBy ... := usual_def.
    ]]

    Equations will then automatically:
    - 1. Search for a proof that [R] is well-founded, using type classes (a database)
         specific to [Equations] suitably named [WellFounded]
    - 2. It will then create an obligation to prove that each recursive call
         is performed on decreasing arguments, try to prove it automatically,
         and if it cannot do it on its own leave it to us to prove

    This allows to write our definition transparently and directly as we would like to.
    In particular, it enables to separete the proofs that the recursive call are smaller
    from the definition of the function, making it easier to read and define
    while dealing automatically with trivial cases.

    In the following, we assume basic knowledge of obligations as discussed
    in the (short) tutorial Equations: obligations.

    ** 2.1 Using a size argument

    The most basic method to define a function by well-founded recursion is to
    define a size function, and to prove that the size decrease with each
    recursive call for the usual strict order [<] on natural numbers.

    This method is already enough to define the function [nubBy], that
    recursively filters out the duplicates of a list, by well-founded recursion.
    Indeed, the size of a list is its length, and the only recursive call
    performed by [nubBy] is on [filter (fun y => negb (eq x y)) l].
    As [filter] can only remove elements, its length is indeed strictly smaller
    than [l], and the function is terminating.

    To define [nubBy] using [Equations] and well-founded recursion, it suffices to
    add [wf (length l) lt] after typing to indicate on which term, here [length l], and
    for which well-founded relation, here [< := lt], we are doing the well-founded recursion on.
    An obligation corresponding to proving that the recursive call is smaller,
    that is [length (filter (fun y => negb (eq x y)) l) < length l], is created.
    As [Equations] cannot solve on its own, it then left to us to solve.
    Using the keyword [Equations?], it is automatically unshelved,
    and we simply have to prove it using tactics.
*)

Equations? nubBy {A} (eq : A -> A -> bool) (l : list A) : list A by wf (length l) lt :=
nubBy eq []        => [];
nubBy eq (a :: l) => a :: nubBy eq (filter (fun b => negb (eq a b)) l).
Proof.
  eapply Nat.le_lt_trans.
  - apply filter_length_le.
  - auto with arith.
Qed.


(** Compared to other methods, reasoning on functions defined with well-founded
    recursion with [Equations], is no different than on regular functions.
    Using function elimination ([funelim]) we can prove our properties directly
    according to the pattern of our definition.
    In particular, we do not have to do proofs by recursion on the proof
    that the relation is well-founded.
    It is important as it enables to completely hide well-founded recursion
    from the users and to reason about our function directly as we think about it.

    This is a very powerful method that, for instance, enables us to prove in a
    few lines that [nubBy] does remove all duplicates;
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
       apply filter_In in Hi as [Hl Hneqx].
       specialize (Heq a a); destruct Heq as [_ Heqx].
       specialize (Heqx eq_refl); rewrite Heqx in Hneqx.
       inversion Hneqx.
    -- assumption.
Qed.

(** ** 2.2 Using a measure

    The size method described above is particular case of a more general scheme
    that consist in using a measure: that is a function depending on
    the arguments to [nat], so that it decrease in each recursive call.

    For an example, consider a [gcd] function that does not require the assumption
    that [x > y], by first checking if [x] or [y] is [0], and otherwise
    compare [x] and [y], and recall [gcd] with [x - y] or [y - x] depending
    which is the greater.
    We cannot prove it is terminating either by looking if [x] or [y] decrease
    (the size of a number is the number itself) as we do not know up-ahead which
    of [x] or [y] is bigger.
    However, we can use that the measure [x + y] is decreasing for the usual
    well-founded order on [nat], as if [x] and [y] are strictly greater than [0],
    than [x + y > x + (y - x) = y] and [x + y > y + (x - y) = y].

    We can define [gcd] by well-founded recursion by adding [wf (x + y) lt].
    We then get two obligations corresponding to the recursive goals, which
    are basic arithmetic goals and can be solved using [lia].

*)

Equations? gcd (x y : nat) : nat by wf (x + y) lt :=
gcd 0 x := x ;
gcd x 0 := x ;
gcd x y with gt_eq_gt_dec x y := {
| inleft (left _) := gcd x (y - x) ;
| inleft (right refl) := x ;
| inright _ := gcd (x - y) y }.
Proof.
  all: lia.
Defined.

(** For further examples of how functional elimination works on well-founded
    recursion and how useful it is on complex definitions, we will now show a
    few properties of [gcd].
*)

Lemma gcd_same x : gcd x x = x.
Proof.
  funelim (gcd x x). all: try lia. reflexivity.
Qed.

Lemma gcd_spec0 a : gcd a 0 = a.
Proof.
  funelim (gcd a 0). all: reflexivity.
Qed.

Lemma mod_minus a b : b <> 0 -> b < a -> (a - b) mod b = a mod b.
Proof.
Admitted.

Lemma gcd_spec1 a b: 0 <> b -> gcd a b = gcd (Nat.modulo a b) b.
Proof.
  funelim (gcd a b); intros.
  - now rewrite Nat.Div0.mod_0_l.
  - reflexivity.
  - now rewrite (Nat.mod_small (S n) (S n0)).
  - rewrite <- Heqcall.
    rewrite refl, Nat.Div0.mod_same.
    reflexivity.
  - rewrite <- Heqcall. rewrite H; auto.
    rewrite mod_minus; auto.
Qed.


(** ** 2.3 Using a lexicographic order

    Not all definitions can be proven terminating using a measure and the strict order [<] on [nat].
    In some cases, it is more practical to use a different well-founded order.
    In particular, when a function involves recursion on different arguments but
    not all recursive arguments are smaller at once, it can be practical to use a
    lexicographic order [<lex].
    Given two order [<A : A -> A -> Prop] and [<B : B -> B -> Prop],
    [(a,b) <lex (a',b')] iff [a <A a'] or [a = a'] and [b <B b'].
    It is practical, as it suffices for one argument to decrease for the recursive
    call to be smaller.
    Moreover, [<lex] is well-founded as soon as [<A] and [<B] are.

    A classical example where it is useful, is to define the Ackerman function.
    Indeed, is terminating as the recursive call are all smaller for the
    lexicographic order, which is essential to deal with the last case:
    - [(m,0) <lex (S m, 0)] as [m < S m]
    - [(m, ack (S m) n) <lex (S m, S n)] as [m < S m]
    - [(S m, n) <lex (S m, S n)] as [S m = S m] and [n < S n]

    To define [ack] by well-founded recursion, it suffices to add [(lexprod _ _ lt lt)].
    The function [lexprod] builds the lexicographic order and derive a proof
    that it is well-founded provided that both order are.
    As we can see, with this order, the obligations generated turns out to be
    simple enough to be automatically dealt with by [Equations].
*)

Equations ack (m n : nat) : nat by wf (m, n) (lexprod _ _ lt lt) :=
ack 0 n := S n;
ack (S m) 0     := ack m 1;
ack (S m) (S n) := ack m (ack (S m) n).


(** In principle, we should be able to reason about [ack] as usual using [funelim].
    Unfortunately, in this particular case, [funelim] runs forever which you can
    check out below.
    It is a known issue currently being fixed due to oversimplification being done
    by [funelim].
*)

Definition ack_min {m n} : n < ack m n.
Proof.
  Fail timeout 5 (funelim (ack m n)).
Abort.

(** There are two main solutions to go around similar issues depending on your case.

    If your pattern is fully generic, i.e. of the form [ack m n], you can apply
    functional elimination directly by [apply ack_elim].
    Though note, that in this case you may need to generalise the goal by hand,
    in particular by equalities (e.g. using the remember tactic) if the function
    call being eliminated is not made of distinct variables.
*)
Definition ack_min {m n} : n < ack m n.
Proof.
  apply ack_elim; intros; eauto with arith.
Qed.

(** However, if your pattern is partially specialised like [ack 1 n],
    it can be better to finish reproducing the pattern using [induction].
    Indeed, [ack_elim] "reproduces" the full pattern, that is, it generalises [1]
    to [m] and tries to prove [ack m n = 2 + n] by induction, creating cases like
    [ack (S m) n] which clearly are not warranted here.
*)

Definition ack1 {n} : ack 1 n = 2 + n.
Proof.
  (* If we apply [ack_elim], we get unwarranted cases *)
  apply ack_elim; intros.
  Restart.
  (* So we reproduce the pattern with induction *)
  induction n; simp ack.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.


(** ** 2.4 Using a custom well-founded relation

    In some cases, there is no basic order that easily enables to define a
    function by well-founded recursion.
    In this case, it can be interesting to:
    - 1. Define your own relation [R : A -> A -> Prop]
    - 2. Prove it is well-founded [wf_R : well_founded R]
    - 3. Declare it as an instance so that Equations can find it with
         [Instance name : WellFounded R := wf_R].

    For instance, suppose we have an infinite sequence [f : nat -> bool] of booleans,
    such that we know logically that there is at least one that is true
    [h : exists n : nat, f n = true].
    This is represented by this context:
 *)

 Module LinearSearch.

 Context (f : nat -> bool).
 Context (h : exists n : nat, f n = true).

(** Knowing there is an [n : nat] such that [f n = true], we would like to
    actually compute one.
    Intuitively, we should be able to just try them one by one starting from 0
    until we find one, and it should terminate as we know there exists one.
    However, it is not clear which classical measure or order to use to
    justify this idea. We will hence use a custom one.

    We define a relation [R : nat -> nat -> nat] such that [n] is "smaller" than
    "m" when [n = 1 + m] and that all booleans before [m] are [false],
    i.e [forall k, k <= m -> f k = false].
*)

  Definition R n m := (forall k, k <= m -> f k = false) /\ n = S m.

(** Knowing that the previous booleans have been [false] enables us to prove
    that [R] is well-founded when combined with [h].
    We omit the proof here because it is a bit long, and not very interesting
    for our purpose.
 *)

  Lemma wf_R : (exists n : nat, f n = true) -> well_founded R.
  Proof.
  Admitted.

(** Having proven it is well-founded, we declare it as an instance of the database
    [WellFounded] so that [Equations] can find it automatically when using the
    keyword [wf x R].
*)

  Instance wfR : WellFounded R := wf_R h.

(** We are not ready to define our function by well-founded recursion.

    Here, for technical reason we use the [inspect] method to remember the value of [f m].
    Here, it is not necessary to understand it for our purpose, and we refer to
    section 2.1 for more details on the method.
 *)

  Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

  Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

(** Though, we want to start a computation at 0, to define our function
    by well-founded recursion we need to start at a generic point [m : nat],
    to actually have a term to do our recursion on:
*)

  Equations? exists_nat (m : nat) (H : forall n, n < m -> f n = false) :
    {n : nat | f n = true} by wf m R :=
  exists_nat m H with inspect (f m) :={
    | true  eqn:p => (exist _ m p)
    | false eqn:p => exists_nat (S m) _
  }.
  Proof.
  - inversion H0; auto.
  - unfold R. split. 2: reflexivity.
    intros k ikm. inversion ikm. 1: assumption.
    subst. apply H. auto with arith.
  Qed.

  Theorem linear_search : {n : nat | f n = true}.
  Proof.
    unshelve eapply (exists_nat 0).
    intros n Hn0; inversion Hn0.
  Qed.

End LinearSearch.


(** ** 3. Different methods to work with well-founded recursion

    When defining a function, it can happen that we loose information
    relevant to termination when matching a value, and that we then get
    stuck trying to prove termination.

    In this section, we discuss two such example an methods to go around the issue.
    Note, the inspect method was already used in section 2.4.

    *** 3.1 The inspect method

    Working with a particular well-founded order [lt], it may happen that
    we have a choice function [f : A -> option A] that for any [(a :A)]
    returns [None] or a strictly smaller element.
    This situation is axiomatised by the following context :
*)

Module Inspect.

  Context {A : Type} {lt : A -> A -> Prop} `{WellFounded A lt}
          (f : A -> option A) (decr_f : forall n p, f n = Some p -> lt p n).

(** In this case, given an element (a : A), we may be interested in computing
    the decreasing chain starting from [a] specified by [f].
    Naively, we would like to do so as below.
    That is check if there is an element smaller than [a] by matching [f a]
    with a [with] clause, if there is one [Some p] then returns [p] added to the
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

(** Unfortunately, as we can see, by doing so we generate an unprovable
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

  Equations? f_sequence (a : A) : list A by wf a lt :=
    f_sequence a with inspect (f a) := {
      | Some p eqn: eq1 => p :: f_sequence p;
      | None eqn:_ => List.nil
      }.
  Proof.
    apply decr_f. assumption.
  Qed.

End Inspect.


(** 3.2 Improving recursion hypotheses

    In some cases,  most particularly when using a size or measure,
    it can happen that when defining a function by well-founded recursion,
    we forget that [x] is a subterm of a larger term [Y],
    and then we get stuck proving that "[size x < size Y]".
    In this case, a possible solution is to define a custom function to "carry"
    the information that [x] is a subterm of [Y], so it is available when
    trying to prove it is well-founded.

    For an example, consider RoseTrees, trees with finite subtrees represented
    by the constructor [node : list RoseTree -> RoseTree.]
    Let's also define the usual size function on it, and an equality test on lists.
*)

Section Map_in.
  Context {A : Type}.

  Inductive RoseTree : Type :=
  | leaf : A -> RoseTree
  | node : list RoseTree -> RoseTree.

  Equations sizeRT (t : RoseTree) : nat :=
  sizeRT (leaf a) := 1;
  sizeRT (node l) := 1 + list_sum (map sizeRT l).

  Equations eqList {X} (l l' : list X) (eq : X -> X -> bool) : bool :=
  eqList [] [] _ := true;
  eqList (a::l) (a'::l') eq := andb (eq a a') (eqList l l' eq);
  eqList _ _ _ := false.

(** Having define an equality test on list, we would like to define an equality
    test on RoseTree.
    For technical reasons, the straigthforward definition is not accepted by Coq
    before Coq v8.20, so we need well-founded recursion on the size of RoseTress
    to define the equality test.
    if you are using a subsequent version, assume you need it for pedagogical purposes.

    If we try to define the equality test naively as below, [Equations] generates
    the obligation [sizeRT l < 1 + list_sum (map sizeRT lt0)] corresponding to
    the case where [lt := l :: _].
    This is obviously true, but we are stuck trying to prove it as we do not
    remember that [l] in in [lt]:
*)

  Equations? eqRT (eq : A -> A -> bool) (t t': RoseTree) : bool by wf (sizeRT t) lt :=
  eqRT eq (leaf a) (leaf a') := eq a a';
  eqRT eq (node lt) (node lt') := eqList lt lt' (fun l l' => eqRT eq l l') ;
  eqRT eq _ _ := false.
  Proof.
      simp sizeRT.
      (* What to do know ? We have forgotten that x is in l,
        and hence that sizeRT l < 1 + list_sum (map sizeRT l0)  *)
  Abort.

(** To go around this kind of issues, a general method is to strengthen the
    function that goes through the structure to remember that [x] in a subterm of [Y].
    In our case, it means strengthening [eqList] so that to remember that [l] is
    a subterm of [lt0], i.e. that [l] is in [lt0].
    To do so, we ask for the input of the equality test [eq] of [eqList]
    to additionally be in in [l], i.e. [eq : forall x : X, In x l -> X -> bool].
    This way, in the case (lt0 := l :: _) we remember [In l lt0].
    Doing so, it is now possible to define [eqRT] by well-founded on the size:
*)

  Equations eqList' {X} (l l' : list X) (eq : forall x : X, In x l -> X -> bool) : bool :=
  eqList' [] [] _ := true;
  eqList' (a::l) (a'::l') eq := andb (eq a _ a') (eqList' l l' (fun x Inl y => eq x _ y));
  eqList' _ _ _ := false.

  Definition list_sum_ine (x : nat) (l : list nat) : In x l -> x < 1 + list_sum l.
  Admitted.

  Equations? eqRT (eq : A -> A -> bool) (t t': RoseTree) : bool by wf (sizeRT t) lt :=
  eqRT eq (leaf a) (leaf a') := eq a a';
  eqRT eq (node lt) (node lt') := eqList' lt lt' (fun l Inl l' => eqRT eq l l') ;
  eqRT eq _ _ := false.
  Proof.
    simp sizeRT. apply list_sum_ine. apply in_map. assumption.
  Qed.