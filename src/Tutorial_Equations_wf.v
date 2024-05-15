(* begin hide *)
Axiom to_fill : forall A, A.
Arguments to_fill {_}.
(* end hide *)

(** * Well-founded Recursion using Equations

  *** Summary

  [Equations] is a plugin for %\cite{Coq}% that offers a powerful support
  for writing functions by dependent pattern matching.
  In this tutorial, we focus on the facilities provided by Equations to
  define function using well-founded recursion and reason about them.

  In section 1, we explain the basic of defining and reasoning by
  well-founded recursion using Equations.
  - In section 1.1, we contextualise and recall the concept of
    well-founded recursion.
  - In section 1.2, we explain how to define and reason about basic
    functions defined using well-founded recursion and Equations.
  - In section 1.3, we explain how to define more complex examples using
    obligations.

  In section 2, we discuss different techniques that can be useful when
  attempting to define functions by well-founded recursion:
  - When matching on terms, it can happen that we loose information relevant
    to termination.
    In Section 2.1, we show an example of that and discuss the inspect
    method as a possible solution to this problem.
  - When defining functions by well-founded recursion, it often happens
    that we are left with easy theory specific obligations to solve,
    for instance basic arithmetic on lists.
    In section 2.2, we explain how to adapt locally the tactic trying to
    solve obligations to deal with such goals.

  *** Table of content

  - 1. Defining and reasoning using well-founded recursion
    - 1.1 Introduction to well-founded recursion
    - 1.2 Basic definitions and reasoning
    - 1.3 Well-founded recursion and Obligations
  - 2. Different methods to work with well-founded recursion
    - 2.1 The inspect method
    - 2.2 Personalising the tactic proving obligations

  *** Prerequisites

  Needed:
  - We assume known basic knowledge of Coq, of and defining functions by recursion
  - We assume basic knowledge of the plugin Equations, e.g, as presented
    in the tutorial Equations: Basics

  Not needed:
  - This tutorial discuss well-founded recursion but no prior knowledge
    about it is required, and we recall the concept at the beginning
  - Defining functions by well-founded recursion using Equations relies on
    Coq's obligation mechanism, but no previous knowledge about it is needed.
  - To simplify proofs involving arithmetics, we use the automatisation
    tactic [lia] and [auto with arith], but they can be used as black boxes

  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name coq-equations

*)

From Equations Require Import Equations.
From Coq Require Import List Arith Lia.
Import ListNotations.



(** ** 1. Defining and reasoning using well-founded recursion

    *** 1.1 Introduction to well-founded recursion

    For Coq to be consistent, all functions must be terminating.
    To ensure they are, Coq check that they verify a complex syntactic
    criterion named the guard condition.
    While powerful, this syntactic criterion is by nature limited, and it
    happens that functions can be proven terminating, using a potentially non
    trivial size argument and some mathematical reasoning, that Coq syntactic
    guard fails to see as such on its own.


    *** The syntactic guard condition is limited

    As a first example, consider the function [last] that returns the last
    element of a list if there is one and None otherwise.
    To return the last element, we must distinguish if a list has
    zero, one, or more than 2 elements leading to nested matching
    [ last (a::(a'::l)) := last (a'::l) ].
    Yet, doing so is not accepted by Coq's current syntactic guard as the
    nested matching forgets that [a'::l] is a subterm of [a::(a'::l)]
    and only recall [l] as a smaller subterm.
*)

Fail Equations last {A} (l : list A) : option A   :=
last [] := None;
last (a::nil) := Some a;
last (a::(a'::l)) := last (a'::l).

(** For an other example consider the definition of the Ackerman function.
    This function is clearly terminating using the lexicographic order:
    [(n,m) <lex (k,l) iff n < m or n = m and k < l].
    Yet, Coq syntactic guard can not see it as terminating as [n] is not
    universally quantified in this definition.
    Consequently, for checking termination, Coq is only aware of the smaller
    recursive call [ack m (S n)] and [ack (S m) n] and not of the one of
    actually used [ack m (ack (S m) n)].
*)

Fail Equations ack (m n : nat) : nat :=
ack 0 n := S n;
ack (S m) 0     := ack m 1;
ack (S m) (S n) := ack m (ack (S m) n).

(** The guard condition being purely syntactic, it turns out that by playing
    with the syntax, it is possible to get small variant of the functions
    above accepted by Coq.
    Yet, playing with syntax is not a viable option as soon as functions and
    datastructures complexify.
    We would like to be able to define this kind of definition as though.

    Moreover, there are functions that can not be accepted even by twisting
    the syntax as the recursive call are not performed on the recursive arguments.

    For instance, it can happen that the algorithm applies a function to
    one of the recursive argument preventing the syntactic guard condition
    from checking that it is still indeed smaller.
    Consider, bellow, the function [nubBy] that given an equality
    test recursively filters out the duplicates of a list.
    The recursive call is not performed on the recursive argument [l] but
    on the list [filter (fun y => negb (eq x y)) l].
    We can prove that [filter] do not increase the size of a list, and hence
    that the recursive call is indeed performed on a smaller instance, and
    that nubBy is terminating.
    But, without surprise, it can not be checked automatically using Coq's
    syntactic guard as it involves mathematical reasoning on [filter].
*)

Fail Equations nubBy {A} (eq : A -> A -> bool) (l : list A) : list A :=
nubBy eq []        => [];
nubBy eq (a :: l) => a :: nubBy eq (filter (fun b => negb (eq a b)) l).

(** Furthermore, opposite to functions like [ack] or [nubBy], some recursive
    functions are simply not naturally defined by structural recursion.
    A prime example is the Euclidean algorithm computing the gcd of
    [x] and [y] assuming that [x > y].
    It performs recursion on [x mod y] which is not a function of
    any recursively smaller arguments, as [gcd] do not match any inputs.
    It is well-founded and terminating for [lt], as we have tested
    that [y > 0] and that in this case we can prove that [x mod y < y].
    Consequently, there is no hope for a syntactic guard to accept [gcd] as
    its definition fully relies on theoretic reason to ensure termination.
*)

Fail Equations gcd (x y : nat) : nat :=
gcd x y with Nat.eq_dec y 0 => {
  | left _ => x
  | right _ => gcd y (x mod y)
}.

(** *** Well-founded recursion

    It would be limitating if all this kind of functions could not be defined.
    Fortunately, they can be using well-founded recursion.

    Given a well-founded relation [R : A -> A -> Type], defining a function
    [f] by well-founded recursion on [a : A] basically consists in defining [f] assuming that
    [f] is defined for all [a'] smaller than [a], that is such that [R a a'].
    When particularise to natural numbers and [<], this concept is sometimes
    known as "strong recursion / induction": when defining [f n] one asummes
    that [f] is defined for all smaller natural numbers [n' < n].

    There are several methods to define functions by well-founded recursion using Coq.
    They all have their pros and cons, but as a general rules defining functions
    and reasonning using well-founded recursion can be tedious.

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
    - there is are explicit proof appearing in the definition of the function,
      here through [gcd_oblig], as we must provide a proof that recusive call
      are indeed smaller.
    It can also make it harder to reason about as the recursion scheme is no
    longer trivial.
    Moreover, as we had to use curryfication in our definition, we may need
    the axiom of function extentionality to reason about [gcd_Fix].

    Consequently, Equations provide a built-in mechanism to help us
    write functions and reason by well-founded recursion.
*)


(** *** 1.2 Basic definitions and reasoning

    To define a function by well-founded recursion with Equations, one must add
    after the type of the function, the command [by wf x R] where [x] is the term
    decreasing, and [R] the well-founded relation for which [x] decreases.

    For instance, the function [last] terminates as the size of the list decrease
    in each recursive call according to the usual well-founded strict order [<]
    on [nat], which is named [lt] in Coq.
    We hence, need to write:

    [[
    Equations last {A} (l : list A) : option A by wf (length l) lt   :=
    ]]

    Equations will then automatically:
    - 1. Check for a proof that [R] is a well-founded in a type classes
         specific to [Equations] logically named [WellFounded]
    - 2. Try to prove that the recursive call are made on decreasing arguments,
         and if it can not do it on its own, it will generate a proof obligation
         i.e. intuitively a goal for the user to fill.

    This enables to separate the proofs that the recursive call are smaller
    from the definition of the function, making it easier to read while dealing
    automatically with trivial cases.

    In this section, we focus on simple examples where no obligations are
    left for the user to solve, and we refer to section 1.3 for more involved
    examples with non trivial obligations.

    Let's first consider the definition of [last] that we can define by
    well-founded recursion by adding [by wf (length l) lt].
    [Equations] will then creates one obligation per recursive call and
    try to solve them.
    In the case of [last], it creates the obligation [length (a'::l) < length (a::a'::l)]
    which as we can check can be solved automatically.
*)

Equations last {A} (l : list A) : option A by wf (length l) lt   :=
last [] := None;
last (a::nil) := Some a;
last (a::(a'::l)) := last (a'::l).

(** Defining [last] by well-founded recursion is hence effortless and the
    the definition is as legible as we would hope.

    Moreover, thanks to functional elimination through [funelim], we can reason
    about function defined by well-founded recursion without having to repeat
    the well-founded induction principle.
    For each recursive call, the tactic [funelim] will create a goal
    goal and an induction hypothesis where all the dependent terms have been
    quantified.

    For instance, let's prove that if [l <> nil], then there exists an
    [a : A] such that [last l = (Some a)].
    By functional elimination, we only need to deal with the case where
    [l := nil], [l := [a]] and [l := (a::a'::l)].
    Moreover, in the last case, we know recursively that
    [a' :: l <> [] -> {a : A & last (a' :: l) = Some a}].
    As we can see, the condition [l <> nil] as correctly been
    particularise and quantified by.
*)

Definition exists_last {A} (l : list A) (Hneq : l <> nil) :
           { a : A & last l = (Some a)}.
Proof.
  funelim (last l); simp last.
  - specialize (Hneq eq_refl) as [].
  - exists a. reflexivity.
  - apply X. discriminate.
Defined.

(** Similarly, we can prove that [last] respects [app] in a suitable way.
*)

Definition last_app {A} (l l': list A) (Hneq : l' <> nil) :
           last (l ++ l') = last l'.
Proof.
  funelim (last l); cbn; autorewrite with last.
  - reflexivity.
  - funelim (last l'); simp last.
    -- specialize (Hneq eq_refl) as [].
    -- reflexivity.
    -- reflexivity.
  - apply H. assumption.
Qed.

(** Let's now consider the Ackerman function which is decreasing according to
    the usual lexicographic order on [nat * nat], [(<,<)] which is accessible
    as both [<] are.
    You can define the lexicographic order and automatically derive a proof
    it is well-founded using the function [Equations.Prop.Subterm.lexprod].
    As we can see, with this order, once again no obligations are generated as
    Coq can prove on its own that [(m, (ack (S m) n)) <lex (S m, S n)] and
    [(S m, n) < n].
*)

Equations ack (m n : nat) : nat by wf (m, n) (Equations.Prop.Subterm.lexprod _ _ lt lt) :=
ack 0 n := S n;
ack (S m) 0     := ack m 1;
ack (S m) (S n) := ack m (ack (S m) n).


(** ISSUES : TO SLOW TO WORK
*)

Definition ack1y {n} : ack 1 n = 2 + n.
Proof.
  Succeed timeout 3 (funelim (ack 1 n)).
  induction n; simp ack; auto.
  rewrite IHn. reflexivity.
  (* Restart. *)
  (* WHY SO SLOW ??? *)
  (* funelim (ack 1 n).
  - reflexivity.
  - simp ack. rewrite H. reflexivity. *)
Qed.

(* Print ack_equation_1. *)

(* ISSUES BUGS + SLOW *)
Definition ack_incr {m n} : ack m n < ack m (n+1).
Proof.
  (* apply ack_elim.
  - intro n'; simp ack. rewrite ack_equation_1 at 1. simp ack.
  apply ack_elim; intros.
  (* ISSUES *)
  - cbn. simp ack. *)
Admitted.


(** As exercices, you can try to:
    - Prove that if [last l = None] than [l = nil]
    - Define a function [removelast] removing the last element of a list
    - Prove the two properties about it
*)

Definition last_none {A} (l : list A) (Hn : last l = None) : l = nil.
Proof.
Admitted.

Equations removelast {A} (l : list A) : list A by wf (length l) lt :=
removelast _ := to_fill.

Definition removelast_app {A} (l l': list A) (Hneq : l' <> nil) :
           removelast (l ++ l') = l ++ removelast l'.
Proof.
Admitted.

(* You may need to use assert *)
Definition removelast_last {A} (l : list A) (Hneq : l <> nil) :
          {a : A & { _ : last l = Some a & l = removelast l ++ [a]}}.
Proof.
Admitted.


(** *** 1.3 Well-founded recursion and Obligations

    For a more involved example where Coq can not prove on its own that the
    recursive call are performed on smaller arguments, let's consider the
    [nubBy] function.

    Given an equality test, [nubBy] recursively filters out the duplicates
    of a list and only keeps the first occurrence of each element.
    It is terminating as the recursive call is performed on
    [filter (fun y => negb (eq x y)) xs] which is smaller than [xs] as
    [filter] can only remove elements.
    Consequently, to define [nubBy] by well-founded recursion, we need to
    add [wf (length l) lt].

    If we try to define the function [nubBy] like that, it seems that all is
    well and that the definition is accepted.
*)

Equations nubBy {A} (eq : A -> A -> bool) (l : list A) : list A by wf (length l) lt :=
nubBy eq []        => [];
nubBy eq (a :: l) => a :: nubBy eq (filter (fun b => negb (eq a b)) l).

(** Yet, if we try to use the function [nubBy], e.g. to prove a property
    about it, we get the error message "The reference nubBy was not found
    in the current environment."
*)

Fail Lemma In_nubBy {A} (eq : A -> A -> bool) (l : list A) (a : A)
               : In a (nubBy eq l) -> In a l.

(** The reason is that Coq can not prove on its own that the recursive
    call is performed on a smaller instance.
    It is not surprising as our argument rests on the property that
    for any test [f : A -> bool], [length (filter f l) ≤ length l].
    Property that is not trivial, and that Coq can not prove on its own,
    nor look for on its own without any indications.
    Consequently, there is an obligation left to solve, and [nubBy] is not
    definied as long as we have not solve it.

    You can check if there is any obligations left to prove and display them
    using the command [Obligations].
*)

Obligations.

(** To prove the remaining obligations, you can use the command [Next Obligations].
    It will get the first obligation left to solve, and creates a corresponding
    goal to solve.

    For instance, in the case of [nubBy], it display the only obligation
    left to solve [length (filter ... l) < length (a::l)].
    You can then solve it using the usual proof mode and tactics:
*)

Next Obligation.
Proof.
  eapply Nat.le_lt_trans.
  - apply filter_length_le.
  - auto with arith.
Qed.

(** As we can see, it was indeed the only obligation as [Next Obligation] fails.
    Moreover, we can see that [nubBy] is now defined as [In_nubBy] is well-typed.
*)

Fail Next Obligation.

Lemma In_nubBy {A} (eq : A -> A -> bool) (l : list A) (a : A)
               : In a (nubBy eq l) -> In a l.
Abort.

(** Unshelving and proving the obligations one by one using [Next Obligation]
    can be tedious.
    Consequently, the package [Equations] enables to automatically unshelve
    all obligations and enter proof mode by starting the definition by
    [Equations?] rather than by [Equations].
    See for instance, [nubBy] below.
*)

Equations? nubBy' {A} (eq : A -> A -> bool) (l : list A) : list A by wf (length l) lt :=
nubBy' eq []        => [];
nubBy' eq (a :: l) => a :: nubBy' eq (filter (fun b => negb (eq a b)) l).
Proof.
  eapply Nat.le_lt_trans.
  - apply filter_length_le.
  - auto with arith.
Defined.

(** This is a powerful feature as compared to the [Fix] definition of section 1.1:
    the code is perfectly legible, in particular the body of the function and
    the proof are clearly separated.

    Though, note that [Equations?] triggers a warning when used on a definition
    that leaves no obligations unsolved.
    It is because for technical reasons, [Equations?] can not check if they
    are at least obligation left to solve before openning the proof mode.
    Hence, when there is no obligation proof mode is open for nothing, and
    as to be closed by hand using [Qed] or [Defined] as it can be seen bellow.
    As it is easy to forget, a warning is raised.
*)

Equations? foo (n : nat) : nat :=
foo _ => 0.
Qed.

(** In practice, if you wish to automatically test if obligations are
    left to solve and unshelved them if so, you can just start all your definitions
    with [Equations?] and remove the [?] if the warning is triggered.

    Reasoning on functions defined by well-founded recursion with
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


(** As exercices you can try to define the [gcd] function.
    You should need the lemma Nat.mod_upper_bound.
 *)
Equations? gcd (x y : nat) : nat by wf y lt :=
gcd x y with Nat.eq_dec y 0 => {
  | left _ => x
  | right _ => gcd y (x mod y)
}. Proof. now apply  Nat.mod_upper_bound. Qed.

(* Properties gcd ? *)

Lemma mul_gcd (k x y : nat) : x > y -> gcd (k * x) (k * y) = k * (gcd x y).
Proof.
  intro H. funelim (gcd x y); simp gcd.
  - rewrite e. rewrite Nat.mul_0_r. cbn. reflexivity.
Admitted.

(** ** 2. Different methods to work with well-founded recursion

    *** 2.1 The inspect method

    When defining a functions, it can happen that we loose information
    relevant to termination when matching a value, and that we then get
    stuck trying to prove termination.

    In this section, we discuss such an example, and explain a solution to
    this problem using the function [inspect].

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
    with a with clause, if there is one [Some p] then returns [p] added to
    chain starting [f_sequence p] here our recursive call, and otherwise
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

(** Unfortunately, as we can see, if do so it generates an unprovable
    obligation as we don't remember information about the call to [f n] being
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
    [f a = f a], one would surely get [Some p = Some p] and learn nothing ?
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


(** *** 2.2 Personalising the tactic proving obligations

    When working, it is common to be dealing with a particular class of
    functions that shares a common theory, e.g, they involves basic
    arithmetic.
    Yet, without surprise, by default the tactic trying to prove obligations is not
    aware of the particular theory at hand, and it will fail to solve
    most of the obligations generated.
    This is normal, as it would be very inefficient if Coq were trying to solve
    a goal using all lemma ever defined, or even all lemma featuring
    [+] in its definition.
    Therefore, it can be interesting to define a local custom strategy for
    solving obligations specific to our theory at hand.

    In this section, we explain how to do so to for a [gcd] function,
    and show how function elimination then enables to prove a few properties
    efficiently.

    We can define a [gcd] function that does not require the assumption that
    [x > y] as below, by first checking if [x] or [y] is [0], and otherwise
    compare [x] and [y], and recall [gcd] with [x - y] or [y - x] depending
    which is the greater.
    It is terminating as the sum [x + y] is decreasing for the usual
    well-founded order on [nat], accounted for by [wf (x + y) lt].
*)

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

(** As we can see, Coq fails to prove the obligations on its own as they
    involve basic reasoning on arithmetic, a theory that Coq is unaware of
    by default.
    This can be checked by using [Show Obligation Tactic] to print the
    tactic currently used to solve obligations and inspecting it.
*)

Show Obligation Tactic.

(** The obligations generated are not complicated to prove but tedious,
    and they can actually be solved automatically via the arithmetic
    solver [lia].
    Therefore, we would like to locally change the tactic solving the
    obligations to take into account arithmetic, and try lia.

    To do so, we use the command [ #[local] Obligation Tactic := tac ]
    to change locally the tactic solving obligation to a tactic [tac].

    In our case, we choose for [tac] to be the previously used
    tactic to which we have added a call to [lia] at the end:
*)

#[local] Obligation Tactic :=
          simpl in *;
          Tactics.program_simplify;
          CoreTactics.equations_simpl;
          try Tactics.program_solve_wf;
          try lia.

(** As we can see by running [Show Obligation Tactic] again, the tactic
    has indeed been changed.
*)

Show Obligation Tactic.

(** We can see our change was useful as [gcd] can now be defined by
    well-founded recursion without us having to solve any obligations.
*)

Equations gcd (x y : nat) : nat by wf (x + y) lt :=
gcd 0 x := x ;
gcd x 0 := x ;
gcd x y with gt_eq_gt_dec x y := {
  | inleft (left _) := gcd x (y - x) ;
  | inleft (right refl) := x ;
  | inright _ := gcd (x - y) y }.


(** For further examples of how functional elimination works on well-founded
    recursion and is useful on complex definitions, we will now show a
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