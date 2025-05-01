(** * How to write a tactic Contradiction with Ltac2

  *** Authors
  - Thomas Lamiaux

  *** Summary

  This tutorial explains how to write a contradiction tactic using Ltac2.
  In particular, it showcase how to use quoting, and match goal with
  the Constr API to check properties on terms.

  *** Table of content

  - 1.

  *** Prerequisites

  Disclaimer:

  Needed:
  - Basic knowledge of Ltac2

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

*)

From Ltac2 Require Import Ltac2 Constr Printf.

(**
According to its specification the [contradiction] can take an argument or not.
If [contradiction] does not take an argument, then [contradiction]:

1. First introduces all variables,
2. Try to prove the goal by checking the hypothesis for:
   - An hypothesis [i : I] such that [I] is an inductive type without any constructor
     like [False], i.e. such that any goal can be proven by [destruct i]
   - An hypothesis [ni : ~I] such that [I] is an inductive type with
     one constructor without hypotheses, like [True] or [0 = 0].
     In other word, such [I] is provable by [constructor 1].
   - A pair of hypotheses [p : P] and [np :~P], such that any goal can be
     proven by [exact (False_rect _ (np p))]

If [contradiction] takes an argument [t] then, the type of [t] must either be:
1. An empty like [False], in which case the goal is proven
2. Or a negation [~P], in which case:
    - There is an hypotheis [P] in the context, then the goal is proven
    - Othewise, the goal is replace by [P]
*)


(* Let us start by writing a simplified first version without checking if
the types are empty or are singleton types.
This already require matching over goals and quoting. *)

(** ** 1.  Step 1:

    *** 1.1 Matching the Goal

    To look up for a pair of hypotheses [P] and [~P], we need to match the goal.
    There are three commands to match the goal that have different behaviour in
    regarding backtracking. The first step is to understand which one we want to use.

  - [lazy_match! goal with] that picks a branch, and stick to it.
    It will not backtrack to pick another branch if this choice leads to a failure.
    For instance, here, it picks the first branch which fails, hence fail.
*)

Goal False.
  Fail lazy_match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.

(** - [match! goal with] that picks the first branch that succeeds.
      In the example, the first branch fails, it hence backtrack to its choice,
      pick the second which this time succeeds
*)

Goal False.
  match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.

(** - [multi_match! goal with] which is more complex and subtile.
      It picks the first branch that makes the whole tactic to succeed,
      and not just the [match!] like [match!] does.
      In another word, if it choose a branch that succeeds, but this leads to
      a subsequent failure when composed with another tactic [; tac],
      then it backtracks to pick the next branch that succeeds.
      This until either [tac] succeeds, or all the branches have been tried in
      which cas it fails.

      To understand this better, consider the example below.
      [multi_match!] picks the first branch that succeeds, here the second one,
      and prints "branch 2".
      This choice is combined with [fail] that leads to a failure.
      It hence backtrack and picks to the next branch, and prints "branch 3".
      This lead again to a failure, and hence backtracks.
      There is no branches left, and hence fail.
*)

Goal False.
  Fail multi_match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end;
  fail.
Abort.

(** [lazy_match!] is the easiest command to use and to understand, as there is no
    backtracking involved whatsoever. It is sufficient for all applications
    where the matching choice is deterministic.

    [match!] is useful as soon as matching the syntax is not enough,
    and we need additional tests to see if we picked the good branch.

    [multi_match!] can be interresting but it can be hard to predict and should
    only be used by people that understand what is going on.
    We have no use for it here.
*)




(**

    To match the goal, all commands use patterns of form:

      [[ [name_hyp1 : type_1, ..., name_hyp1 : type_k] |- to_prove  => ... ]]

    The name of all the variables and meta-variables must start for a small cap.

    To match for [P] and [~P], we hence use the pattern [p : ?t, np : ~(?t)].
    This provides us the ? of the hypotheses [p : ident] and [q : ident], and
    with the type [t : constr].
*)

Goal forall P, P -> ~P -> False.
  intros.
  lazy_match! goal with
  | [p : ?t, np : ~(?t) |- _ ] => printf "Matching Worked!";
                                  printf "The names of the hypotheses are %I, %I " p np
  | [ |- _ ] => fail
  end.
Abort.

(** There are two subtilities to understand here about.

    1. Matching is syntactic. This means that [P -> False] will not be matched
       by the pattern [~ P], even though [~P] is convertible to [P -> False].
*)

Goal forall P, P -> (P -> False) -> False.
  intros.
  Fail lazy_match! goal with
  | [p : ?t, np : ~(?t) |- _ ] => printf "Matching Worked!";
                                  printf "The names of the hypotheses are %I, %I " p np
  | [ |- _ ] => fail
  end.
Abort.

(** 2. However, matching for meta-variables is up to conversion.
       This can be seen by adding a trivial expension around [P]:
*)

Goal forall (P : Prop), P -> (~((fun _ => P) 0)) -> 0 = 1.
  intros.
  lazy_match! goal with
  | [ p : ?t, np : ~(?t) |- _ ] =>
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p))
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "There are no hypothesis solvable by contradiction")))
  end.
Qed.

(** *** 1.2 Quoting

    To prove the goal, we want to apply [destruct [np p]]. This is not directly
    possible as [np] and [p] are idents, they are not terms.

    Consequently, what we want is to apply the term that [np] refers to the term
    that [p] refers to.

    To get the term associated to the ident, we first use [Control.hyp : ident
    -> constr] to get a Ltac2 ??? out of an ident. We then use [$] to go back to
    a Rocq term. This provide us with the script:

  [[
    let p := Control.hyp p in let q := Control.hyp q in exact (False_rect _ ($q
    $p))
  ]]

  Putting it all together, this give us the following Ltac2 term:
*)

Goal forall (P : Prop), P -> ~P -> 0 = 1.
  intros.
  lazy_match! goal with
  | [ p : ?t, np : ~(?t) |- _ ] =>
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p))
  | [ |- _ ] => fail
  end.
Abort.

(** 1.3 Error Messages  *)

(** 1.4 Putting it all together *)

(** The two other cases proceed similarly. We use:
    - [match! goal] to find the hypothesis,
    - [Control.hyp] and [$] to use the rocq term associated to the hypotheses.

    The only key difference is that for the last two cases the syntaxtic
    match is not enough on its own to select the good hypothesis.
    Indeed, there is no reason why matching [~(t)] would imply that [t] is a
    singleton type, which can be proven by [constructor 1].
    It could very well be a function type, like [~(nat -> False)].
    Consequently, we must use [match!] rather than [lazy_match!] as
    if the wrong [~t] is picked, we want to backtrack to try the next one.
*)

Goal ~(0 = 0) -> 0 = 1.
  intros.
  match! goal with
  | [ np : ~(_) |- _] =>
        let np := Control.hyp np in
        exact (False_rect _ ($np ltac2:(constructor 1)))
  | [ |- _ ] => fail
  end.
Qed.

Goal False -> 0 = 1.
  intros.
  match! goal with
  | [ p : _ |- _] =>
        let p := Control.hyp p in
        destruct $p; fail
  | [ |- _ ] => fail
  end.
Qed.

(** To put it together, we must pick the match goal that backtracks the more.
    As we have used [lazy_match!] and [match!], we must hence pick [match!].
    This is gives us the following tactic. Let us not forget the thunk as otherwise
    the script would  be excuted immediately, which is clearly not what we want.
*)

Ltac2 contradiction_empty_v1_ : unit -> unit :=
  fun () =>
  match! goal with
  | [ p : ?t, np : ~(?t) |- _ ] =>
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p))
  | [ np : ~(_) |- _] =>
        let np := Control.hyp np in
        exact (False_rect _ ($np ltac:(constructor 1)))
  | [ p : _ |- _ ] =>
        let p := Control.hyp p in
        destruct $p; fail
  | [ |- _] => fail
  end.

(** Finally, we can define an abreviation for it to try it out *)

Ltac2 Notation contradiction_empty_v1 :=
  intros; contradiction_empty_v1_ ().

Goal (1 = 0) -> ~(1 = 0) -> 0 = 1.
  contradiction_empty_v1.
Qed.

Goal ~(0 = 0) -> 0 = 1.
  contradiction_empty_v1.
Qed.

Goal False -> 0 = 1.
  contradiction_empty_v1.
Qed.


(** ** 2. Using Constr.Unsafe to add syntactic check  *)


(*
- need for the test
- intro to unsafe
- empty
- singleton


*)


Ltac2 decompose_app (c : constr) :=
  match Unsafe.kind c with
    | Unsafe.App f cl => (f, cl)
    | _ => (c,[| |])
  end.

(* singletong types *)
Ltac2 singleton_type (t : constr) : bool :=
  let (i, _) := decompose_app t in
  match Unsafe.kind i with
  | (Unsafe.Ind x _) => Int.equal (Ind.nblocks (Ind.data x)) 1
  | _ => false
  end.

(* empty types *)
Ltac2 empty_types (t : constr) : bool :=
  let (i, _) := decompose_app t in
  match Unsafe.kind i with
  | (Unsafe.Ind x _) => Int.equal (Ind.nconstructors (Ind.data x)) 0
  | _ => false
  end.

Ltac2 contradiction_empty_v2_ : unit -> unit := fun () =>
  match! goal with
  | [ p : ?t, np : ?t -> False |- _ ] =>
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p))
  | [ np : ~(?t) |- _] =>
        if singleton_type t
        then let np := Control.hyp np in
             exact (False_rect _ ($np ltac:(constructor)))
        else fail
  | [ p : ?t |- _ ] =>
        if empty_types t
        then let p := Control.hyp p in
             destruct $p
        else fail
  | [ |- _] => let err_message := fprintf "No hypothesis is an obvious contradiction" in
               Control.zero (Tactic_failure (Some err_message))
  end.

Ltac2 Notation contradiction_empty_v2 := contradiction_empty_v2_ ().

(** 3. [contradition_arg] *)



(** 4. Combining [contradiction_empty] and [contradition_arg], and Notation  *)

(* Ltac2 my_contradiction2_ : unit -> unit := fun () =>
  (* get an hypothesis *)
  match! goal with
  | [ p : ?t1 |- _ ] =>
    let p := Control.hyp p in
    (* 1. If [~t] is an empty type *)
    if empty_types t1 then destruct $p else
    (* 2. If [~t] is the negation of a singleton type *)
    match! t1 with
    | ?t -> False =>
        if singleton_type t
        then exact (False_rect _ ($p ltac:(constructor 1)))
        else fail
    (* 3. Search for [~t] *)
    | _ =>
      match! goal with
      (* t is rebind here! *)
      | [q : ?t2 -> False |- _] =>
          if Constr.equal t1 t2 then
          printf "type q: %t" t2;
          let q := Control.hyp q in
          exact (False_rect _ ($q $p))
          else fail
      | [|- _] =>
            let err_message := fprintf "No hypothesis is an obvious contradiction" in
            Control.zero (Tactic_failure (Some err_message))
      end
    end
  end. *)

