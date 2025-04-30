(** * How to write a tactic Contracition with Ltac2

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


(** ** 1.  Step 1:

    *** 1.1 A simplified version

    Let us start by writing a simplified first version without checking if
    the types are empty or are singleton types.
    This already require matching over goals and quoting.

*)

(* Ltac2 err_contradiction : exn :=
    Tactic_failure (Some (fprintf "There are no hypothesis solvable by contradiction")). *)

(** To look up for a pair of hypotheses [P] and [~P], we match the goal using
    [lazy_match! goal with].
    The patterns are of the form [ [name_hyp1 : type, ..., name_hyp1 : type,] ]

    The name of all the variables and meta-variables must start for a small cap.
    To match for [P] and [~P], we hence use the pattern [p : ?t, np : ~(?t)].
    This provides us the ? of the hypotheses [p : ident] and [q : ident],
    and with the type [t : constr].

  [[
    lazy_match! goal with
    | [ p : ?t, q : ~(?t) |- _ ] => ???
    | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "There are no hypothesis solvable by contradiction")))
    end.
  ]]

    To prove the goal, we want to apply [destruct [np p]].
    This is not directly possible as [np] and [p] are idents, and not terms.
    Consequently, what we want is to apply the term that [np] refers to
    the the term that [p] refers to.

    To get the term associated to the ident, we first use [Control.hyp : ident -> constr]
    to get a Ltac2 ??? out of an ident. We then use [$] to go back to a Rocq term.
    This provide us with the script:

  [[
    let p := Control.hyp p in
    let q := Control.hyp q in
    exact (False_rect _ ($q $p))
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
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "There are no hypothesis solvable by contradiction")))
  end.

(** There are two subtilities to understand here about.

    1. Matching is syntactic. This means that [P -> False] will not be matched
       by the pattern [~ P], even though [~P] is convertible to [P -> False].
*)

Goal forall (P : Prop), P -> (P -> False) -> 0 = 1.
  intros.
  Fail lazy_match! goal with
  | [ p : ?t, np : ~(?t) |- _ ] =>
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p))
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "There are no hypothesis solvable by contradiction")))
  end.

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

(** The two other cases proceed similarly. We use:
    - [match! goal] to find the hypothesis,
    - [Control.hyp] and [$] to use the rocq term associated to the hypotheses.

    In the first case, we use [ltac2:(tac)] to build a term using the tactic [constructor].
    Note, that here, we really need to use [match] as in the absence of a check to ensure
    [t] can be proven by [constructor 1], it may fail.
    In which, case we want to backtrack to try the next hypothesis of the form [~t].
*)

Goal ~(0 = 0) -> 0 = 1.
  intros.
  match! goal with
  | [ np : ~(_) |- _] =>
        let np := Control.hyp np in
        exact (False_rect _ ($np ltac2:(constructor 1)))
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "There are no hypothesis solvable by contradiction")))
  end.
Qed.

(** In the second case, in the absence of a test to check if [t] is an empty type,
    [destruct $p] could succeed without solving the goal, for instance for [t := nat].
    We hence, link [destruct $p] with [fail] to ensure the goal is solved,
    as if they are any remaining goal after [destruct $p], [fail] wil [fail].
*)

Goal False -> 0 = 1.
  intros.
  match! goal with
  | [ p : _ |- _] =>
        let p := Control.hyp p in
        destruct $p; fail
  | [ |- _ ] => Control.zero (Tactic_failure (Some (fprintf "There are no hypothesis solvable by contradiction")))
  end.

(** Putting this altogether, this gives us the following tactic  *)

Ltac2 contradiction_empty_v1_ : unit -> unit :=
  fun () =>
  match! goal with
  | [ p : ?t, np : ~(?t) |- _ ] =>
        let p := Control.hyp p in
        let np := Control.hyp np in
        exact (False_rect _ ($np $p))
  | [ np : ~(_) |- _] =>
        let np := Control.hyp np in
        exact (False_rect _ ($np ltac:(constructor)))
  | [ p : _ |- _ ] =>
        let p := Control.hyp p in
        destruct $p; fail
  | [ |- _] => let err_message := fprintf "No hypothesis is an obvious contradiction" in
               Control.zero (Tactic_failure (Some err_message))
  end.

(** We can now define an abreviation for it and try it out *)

Ltac2 Notation contradiction_empty_v1 := intros; contradiction_empty_v1_ ().

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

