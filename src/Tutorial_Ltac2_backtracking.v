(** * Tutorial Ltac2 : Backtracking

  *** Summary

  Ltac2 has native support for backtracking, and powerful primitives to
  manipulate it enabling us to write powerful automatisation proof script.
  While powerful, backtracking and its primitives can be a bit unsetteling for newcommers.
  In this tutorial, we explain how backtracking works in Ltac2, and
  how to use the different primitives to manipulate bactracking by recoding
  basics tactics that were hardcoded in Ltac1.

  *** Table of content

  - 1. Manipulating Tactics with Ltac2, and Thunks
  - 2. Backtracking in Ltac2
  - 3. Manipulating Backtracking with Ltac2 primitives
    - 3.1 Using [Control.Plus] to stack possibilities
    - 3.2 Using [Control.Case] to inspect backtracking
    - 3.4 Implementing [once] with [Control.case] and [Control.zero]
          for a finer control of backtracking
    - 3.4 Backtracking and Goal focussing
    - 3.5 Reimplementing [;] using [zero],[plus] and [case]

  *** Prerequisites

  Disclamer:
    - You can go a **long way** with Ltac2 without ever needing to directly
      manipulate backtracking, outside of already backtracking tactics like
      [constructor], [once] and [match!].
      This tutorial is for advanced users of Ltac2, or for users wanting a
      deeper understanding of how backtracking works.

  Needed:
  - Already know the basics of Ltac2.
  - Having used Ltac2 before.

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

*)



(** Let us start by importing Ltac2, and write a small function for
    printing the current goals to check out what is going on.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Printf.
From Ltac2 Require Import Notations.

Ltac2 print_goals () :=
  Control.enter (fun () =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end
  ).

Ltac2 Notation "print_goals" := print_goals ().

Ltac2 only0 (startgoal : int) (endgoal : int option) (tac : unit -> 'a) : 'a :=
  let clamp i :=
    if (Int.lt i 0)
    then Int.add (Int.add i (Control.numgoals ())) 1
    else i
  in
  let endgoal := Option.default startgoal endgoal in
  Control.focus (clamp startgoal) (clamp endgoal) tac.

Ltac2 Notation "only" startgoal(tactic) endgoal(opt(seq("-", tactic))) ":" tac(thunk(tactic)) :=
  only0 startgoal endgoal tac.



(** 1. Manipulating Tactics with Ltac2, and Thunks

  Before explaining how to manipualte backtracking with Ltac2,
  let us recall how to manipulate tactics with Ltac2 functions.

  Tactics such as [assumption] or [left] modify the proof state through side effects,
  such as modifying hypotheses or resolving an existential variable.
  They do not produces Ltac2 value, like an integer [Int] of Ltac2, and are
  hence of type [unit].

  Opposite to Rocq that is call-by-name, Ltac2 is language that is call-by-value.
  This means that a Ltac2 function evaluates its arguments before evaluating the body of the function.
  Being call-by-value is important for a functional programming language like Ltac2
  to be predicatable and intuitive.

  However, this has an important side effect to manipulate tactics.
  If we pass a tactic like [fail] **as is** to a Ltac2 function, it will be evaluated first.
  As [fail] fails, the whole Ltac2 tactic will then fail, even if [fail] is not used.
  For instance, consider a function ignoring its arguments, and doing nothing.
  Applying it directly to [fail] will fail, even though it should do nothing.
*)

Ltac2 bad_ignore (bad_tac : unit) : unit := ().

Goal 0 = 0.
  Fail bad_ignore fail.
Abort.

(** Consequently, tactics must be "thunk" to be manipulated by a Ltac2 function.
    That is, rather than manipulating [tac : unit] directly, a Ltac2 function
    manipulates it is "thunk" version instead [fun () => tac : unit -> unit].
    As function are already fully-evaluated in call-by-value, "thunk" do
    not get reduced further when passed as arguments, and can hence be evaluated
    on demand by Ltac2 functions applying it to [()], [(fun () => tac) ()].

    A [good_ignore] function would hence have following type, and we can check it works:
*)

Ltac2 good_ignore (tac : unit -> unit) : unit := ().

Goal (0 = 0).
  (* succeeds doing nothing  *)
  good_ignore (fun () => fail).
Abort.

(** While this works, no one wants to write "thunk" by hand in proof scripts.
    Thanfully, there is an easy not to have to. It suffices to define
    a Ltac2 notation that directly inserts the thunks around tactics for us.
    For instance, for [good_ignore], we declare a notation with the same
    name that takes a tactic as argument that is "thunk", i.e. [tac(thunk(tactic))].
*)

Ltac2 Notation "good_ignore" tac(thunk(tactic)) := good_ignore tac.

(** It is then possible to write clean proof script as usual, while having a
    meta-programming language with a clear semantics, opposite to Ltac1.
*)

Goal 0 = 0.
  good_ignore fail.
Abort.






(** ** 2. Backtracking in Ltac2

  TO WRITE

*)







(** ** 3. Manipulating Backtracking with Ltac2 primitives

    *** 3.1 Using [Control.Plus] to stack possibilities

    To understand how [Control.plus] works, let us implement a [or] tactical
    that given two tactics [tac1 or tac2] will:

    1. Execute [tac1] until it produces a success, or run out of possibilities,
       in which case execute [tac2]
    2. [tac1 ++ tac2] can succeed but lead to a subsequent failure when composed
       with another tactic, i.e. [tac1 ++ tac2 ; ... ; tac3].
       In this case, it should backtrack to [tac1 ++ tac2] and pick the next
       success, either produces by [tac1] or if they are none left, try [tac2].

    This can be coded very simple using the [Control.plus] primitive.
    Given two tactics [tac1 tac2: unit -> unit], [tac1 ++ tac2] consists in
    using [Control.plus] to install a backtracking point around [tac1],
    runnning [tac2] in case of exhaustion and failure of [tac1].

    This does satify the specification as:
    - This will try [tac1] first, and then try [tac2] if [tac1] failed.
    - This will indeed backtrack in case of subsequent failure and try [tac2] if
      needed, as backtracking is the default behaviour of [;], and we simply
      added [tac2] to additionnaly try if [tac1] fails.

    If this feels confusing, it can be useful to see it from the perspective
    of the stream model. In this particular case, it makes the problem easy.
    Here, we want to try all the possibilities of [tac1], then all the
    possibilities of [tac2] until one succeeds or none are remaining, and it fails.
    In other words, we want to build the concatenation of the stream of [tac1]
    and of the stream of [tac2]. That is exactly what [Control.plus] does.

*)

Ltac2 or_backtrack (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  Control.plus tac1 (fun () => tac2 ()).

Ltac2 Notation tac1(thunk(self)) "++" tac2(thunk(self)) :=
  or_backtrack tac1 tac2.

(** Now that we have defined [++], let us tests it to ensure it works.
    That is important because it is easy to make mistakes when dealing with
    backtracking, for instance to forget side cases.
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
    (* If the first tactic succeed, it should be picked *)
  - (exact 2) ++ (exact 1).
    (* If the first tactic failed, the second should be picked *)
  - assumption ++ reflexivity.
    (* If none works, it should fail returning the last error message *)
  - Fail assumption ++ (exact 4).
Abort.

(** Moreover, [tac1 ++ tac2] should backtrack to pick the next success,
    possibily trying [tac2], if a choice leads to a subsequent failure.

    To check it consider the example below that require a value [n] such that [n = 2].
    The first success is [exact 1] which leads to the goal [1 = 2].
    This latter leads to a failure as [reflexivity] can not solve the goal [1 = 2].
    The proof script hence backtracks to apply [exact 2] which succeeds, then
    run the proof script again, here [reflexivity] which now succeeds as [2 = 2].
*)

Goal exists n, n = 2.
  unshelve econstructor.
  all: only 1: (exact 1) ++ (exact 2); print_goals; reflexivity.
Qed.

(** Something important to understand about backtracking is that a tactic [tac1]
    can have more than one success, as [tac1] can backtrack itself.
    That is why we talk about successes and not of the result: everything can backtrack.
    For instance, our tactic could be [(tac1 ++ tac2) ++ tac3].
    In this case, it should try all the successes of [ltac1 ++ ltac2], that is
    all the successes of [ltac1], before trying the ones of [ltac2], and the ones of [tac3].

    We can easily check that our implementation is correct and tries
    the successes in the good order by printing the goals.
 *)

Goal exists n, n = 3.
  unshelve econstructor.
  (* The goals should be [1 = 3], [2 = 3], [3 = 3] *)
  all: only 1: ((exact 1) ++ (exact 2)) ++ (exact 3); print_goals; reflexivity.
Qed.



(** *** 3.2 Using [Control.Case] to inspect backtracking

  In practice, backtracking on subsequent failure is not always wanted
  as it can make proof scripts costly, and hard to predict.

  For instance, consider a script of the form [tac1 ++ tac2; script].
  [script] will be tried for every success of [tac1 ++ tac2] until one is found
  that will make [script] succeed, or all success have been exhausted.
  Repeating [script] this way can be costly if [script] is a complex tactic.
  Moreover, [script] itself could be backtracking causing an exponantial blow up
  of combinations tried, and potential resulting goals:
*)

Goal exists (n m : nat), n = m.
  unshelve econstructor; only 2 : unshelve econstructor.
  all: only 1 : (exact 0) ++ (exact 1) ++ (exact 2);
       only 1 : (exact 10) ++ (exact 9) ++ (exact 2);
      print_goals ; reflexivity.
Qed.

(** This can easily make proof script hard to predict as a choice of success
    affect which tactics can succeed next, and hence which will be picked next.
    For instance, consider proving [nat \/ 2 = 2].
    If we choose [left], we want to choose [exact 0] next, but if we choose [right],
    we want to choose [reflexivity] next.
*)

Goal nat + (2 = 2).
  (left ++ right) ; reflexivity ++ (exact 0).
Qed.

(** Consequently, we would like a variant of the [++] tactical that
    applies the first tactics that succeeds, but will not backtrack to try
    [tac2] if it has chosen [tac1] and that lead to a subsequent failure.

    To do this, we use [Control.case] to compute [tac1] and check if it fails or not:
    - If it fails, we compute [tac2].
    - If it succeds, we return [tac1] which we have to reconstruct with
      [Control.plus] as we have destructed it with [Control.Case].
*)

Ltac2 orelse (tac1 : unit -> 'a) (tac2 : unit -> 'a) : 'a :=
  match Control.case tac1 with
  | Err _ => tac2 ()
  | Val (x,k) => Control.plus (fun () => x) k
  end.

(*
    This satifies the specification as:
    - It applies [tac1] and if it fails [tac2]
    - This does not backtrack from [tac1] to [tac2] as in case of subsequent failure
      it backtracks to [Control.plus (fun () => x) k] i.e. [tac1].

    In terms of streams, this corresponds to using the stream [tac1]
    if at has at least one success, and the stream [tac2] otheriwse.
    This case analysis naturally corresponds to [Control.Case tac1].
    However, as [Control.case] returns a [result] and not directly a stream,
    we need to use [Control.plus] to glue the result back into [tac1].
*)


(** Now that we have define [orelse], let us define an infix notation for it.
*)

Ltac2 Notation tac1(thunk(self)) "||" tac2(thunk(self)) :=
  orelse tac1 tac2.

(** We can now try the previous to tests that this still applies the first
    tactic that succeeds, but will not backtrack to [tac2] if [tac1] fails:
*)

Goal exists n, n = 2 /\ n = 3.
  unshelve econstructor; only 2 : split.
    (* If the first tactic succeed, it should be picked *)
  - (exact 2) || (exact 1).
    (* If the first tactic failed, the second should be picked *)
  - assumption || reflexivity.
    (* If none works, it should fail returning the last error message *)
  - Fail assumption || (exact 4).
Abort.

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [exact 1] and can not backtrack to try [exact 2] *)
  Fail all: only 1: (exact 1) || (exact 2); print_goals; reflexivity.

Abort.

(** Note that this does not disable the backtraking abilities of [tac1] and [tac2]:
    if [tac1] or [tac2] is picked, it can still backtrack in case of subsequent failure.
    It only prevents backtracking to try [tac2] if [tac1] was picked.

    This is because, in each branch of [Control.case], we apply [tac1] or [tac2]
    without any further modification, hence preserving their backtracking abilities.
*)

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [(exact 1) ++ (exact 2)] then [excat 1] then backtrack to [exact 2] *)
  all: only 1: ((exact 1) ++ (exact 2)) || (exact 3); print_goals; reflexivity.
Abort.



(** *** 3.3 Implementing [once] with [Control.case] and [Control.zero]
            for a finer control of backtrackin

    TODO: write it

    To control backtracking further, Ltac2 comes with a primitive [once].

    In case f

*)

Goal exists n, n = 2.
  unshelve econstructor.
  (* It picks [(exact 1) ++ (exact 2)] can not backtrack further due to [only]
     hence backtrack to try [exact 3] *)
  Fail all: only 1: (once ((exact 1) ++ (exact 2))) ++ (exact 3); print_goals; reflexivity.
Abort.

Goal (0 = 0).
  once (assumption ++ reflexivity).
Abort.

(** [once] can be coded easily with [Control.case] and [Control.zero].
    We inspect [tac] to check if it fails or produces a success.
    - If it fails, we return the empty stream.
    - If it produces a success, we return the success, discarding the rest of
      the stream to prevent any backtracking.
*)

Ltac2 my_once (tac : unit -> 'a) : 'a :=
  match Control.case tac with
  | Err e => Control.zero e
  | Val(x,_) => x
  end.

Ltac2 Notation "my_once" tac1(thunk(self)) := my_once tac1.

(** A common source of confusion using [Control.case], it to think that this
    will only try the first tactics in the stream of possibilities.
    This is not the case, as [Control.case] return the first success, that is,
    here, the first tactic to work if any.

    For instance, if we try to solve [0 = 0] with [assumption ++ reflexivity]
    the first tactic to succeed is not [assumption] but [reflexivity], which
    will hence be picked by [Control.case (assumption ++ reflexivity)]:
*)

Goal (0 = 0).
  my_once (assumption ++ reflexivity).
Abort.

(** A logical question in now what does the Ltac2 function [once_plus] do?
    It can seem weird at first to add a continuation to try in case of failure
    to use [once] and disable backtracking.
*)

Ltac2 once_plus (run : unit -> 'a) (handle : exn -> 'a) : 'a :=
  once (Control.plus run handle).

(** Well, as [Control.plus] corresponds to [++], this exactly to what was just exlained.
    This does not add potential successes to backtrack to in case of subsequent failure,
    it adds more potential successes to try if [run] produces none.

    Given an error [e], another common source of confusion is the difference
    between returning [Control.zero e] or [Control.throw e].
    [Control.throw e] raises the error [e] and interrupts the computation.
    It will not look for any other success, not trigger backtracking,
    opposite to [Control.zero].
*)

Goal 0 = 1 -> 0 = 1.
  (* When evaluated [Control.throw] raises an error and interrupts the computation *)
  Fail intros H1; (Control.throw Not_found ++ assumption).
  (* [Control.zero] fails, so it will just look for next success, here [assumption] *)
  intros H1; (Control.zero Not_found ++ assumption).
Qed.

Goal exists n, n = 2.
  unshelve econstructor.
  (* [Control.throw] will not backtrack either: it stops computation *)
  Fail all: only 1 : (exact 1) ++ (exact 2); Control.throw Not_found ++ reflexivity.
  (* Whereas [Control.zero] will fail, trigerring braktracking as usual *)
  all: only 1 : (exact 1) ++ (exact 2); Control.zero Not_found ++ reflexivity.
Qed.

(** To implement [once], it is hence crucial to use [Control.zero] rather than [Control.throw].
    Otherwise, in the example below [once reflexivity] would fail without backtracking,
    which clearly not wanted as [once tac] is supposed to prevent backtracking
    of a [tac], not backtracking of all the previous tactics.
*)

Goal exists n, n = 2.
  unshelve econstructor.
  all: only 1 : (exact 1) ++ (exact 2); once reflexivity.
Qed.


(** *** 3.4 Backtracking and Goal Focusing

  In all previous sections, we have used our tactics with exactly one goal focused.
  What happens if more than one goal is focused ? Does [tac1 ++ tac2]:
  1. must choose [tac1] or [tac2], and apply it to all the goals
  2. it can apply [tac1] or [tac2] independently for each goal

  With the current implementation it must choose [tac1] or [tac2] and apply it everywhere.
  For instance, the following example fails, even though it clearly works if
  the tactic was evaluated independently for every goal.
*)

Goal (0 = 0 \/ 0 = 1) /\ (1 = 0 \/ 1 = 1).
  split.
  Fail all: left ++ right; print_goals; reflexivity.
Abort.

(** The reasons is that it tries to figure one computation path that will succed
    for all the goals.
    In particular, a failure in one goal will trigger backtracking to the first
    goal and try the next success of the tactic for this goal and all the goals,
    this until it has found a success that work in for goals, or exhaust all possibilities.

    This can be seen by trying to prove [(0 = 0 \/ 1 = 1) /\ (1 = 0 \/ 1 = 1)].
    Both [0 = 0] and [1 = 1] are provable, but if we pick [left] to solve the
    first goal, and hence the second goal, we get stuck with [1 = 0] which is not
    provable. It should hence backtrack to pick [right].
*)

Goal (0 = 0 \/ 0 = 0) /\ (1 = 0 \/ 1 = 1).
  split. all: left ++ right; print_goals; reflexivity.
Qed.

(** If you want to apply a tactic independently to every goal, it must be wrapped in
    [Control.enter : (unit -> unit) -> unit], it now works as expected.
 *)

Ltac2 or_backtrack_indep (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  Control.enter (fun () => Control.plus tac1 (fun () => tac2 ())).

Ltac2 Notation tac1(thunk(self)) "++i" tac2(thunk(self)) :=
  or_backtrack_indep tac1 tac2.

Goal (0 = 0 \/ 0 = 1) /\ (1 = 0 \/ 1 = 1).
  split. all: left ++i right; print_goals; reflexivity.
Abort.




(** *** 3.5 Reimplementing [;] using [zero],[plus] and [case]

    As it turns out, [zero], [plus] [case] are so powerful that when combined
    with recursion they enable us to reimplement the [;] operator.

   Specifically [tac1 ; tac2] should execute [tac1]:
   1. If [tac1] fails it should fail
   2. Oherwise it should execute [tac2], and in case of failure backtracks to [tac1]

  This naturally leads to use [Control.Case] to inspect if [tac1] fails or not.
  - If it fails, we return [Control.zero], rather than [Control.throw], in order
    to fail without breaking previous backtracking points.
  - If [tac1] succeds and return a value [x] and an handler [h],
    we want to execute [tac2] and if it fails backtrack to execute [h ; tac2]
    This corresponds to the [Control.plus] primitive, with recursively calling [concat].

    Note, that here, we do not care about [x] as it has already been evaluated,
    and its side effect, so the tactic already be executed.
*)

Ltac2 rec concat (tac1 : unit -> unit) (tac2 : unit -> unit) : unit :=
  match Control.case tac1 with
  | Err e => Control.zero e
  | Val ( _ , f ) =>
      Control.plus tac2 (fun e' =>
      concat (fun () => f e') (fun () => tac2 ()))
  end.

Ltac2 Notation tac1(thunk(self)) "##" tac2(thunk(self)) :=
  concat tac1 tac2.

(** Let us now check that it work *)

Goal 0 = 0 \/ 1 = 2.
  (* [##] fails if [tac1] fails *)
  Fail (fail ## reflexivity).
  (* it does chain tactics *)
  left ## reflexivity.
Abort.


Goal 0 = 1 \/ 0 = 0.
  (* [##] does backtrack *)
  constructor ## reflexivity.
Abort.