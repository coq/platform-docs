(** * Tutorial Ltac2 : Matching Terms and Goals

  *** Authors
  - Thomas Lamiaux

  *** Summary

  Ltac2 has native support to match the structure of terms, and of the goal
  making it easy to build decision procedure or solvers.
  There are three primtives to match terms or goals [lazy_match!], [match!],
  and [multi_match!], which only differ by their backtracking abilities.
  Consequently, we first explain the syntax using [lazy_match!], then
  discuss the backtracking differences in a second part.
  In a third part, we discuss non-linear matching which can be subtle.

  *** Table of content

  - 1. Matching Terms and Goals
    - 1.1 Matching Terms
    - 1.2 Matching Goals
  - 2. [lazy_match!], [match!], [multi_match!] and Backtracking
    - 2.1 [lazy_match!]
    - 2.2 [match!]
    - 2.3 [multi_match!]
  - 3. Non-Linear Matching

  *** Prerequisites

  Disclaimer:

  Needed:
  - Basic knowledge of Ltac2

  Installation:
  - Ltac2 and its core-library are available by default with Rocq

*)

(** Let us firs import Ltac2, and write a small function printing the goal under focus
*)
From Ltac2 Require Import Ltac2 Printf.

Ltac2 print_goals0 () :=
  Control.enter (fun () =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end
  ).

Ltac2 Notation print_goals := print_goals0 ().

(** 1. Matching Terms, and Goals *)

(** 1.1 Matching terms *)

(** 1.2 Matching Goals *)









(* 2. [lazy_match!], [match!], [multi_match!] and Backtracking *)

(** 2.1 [lazy_match!]

    [lazy_match!] is the easiest command to understand and to use.
    [lazy_match!] picks a branch, and sticks to it to even if the code excuted
    after picking this branch (the body of the branch) leads to a failure.
    It will not backtrack to pick another branch if a choice leads to a failure.

    For instance, in the example below, it picks the first branch as everything
    match [ |- _]. It prints "branch 1", then fails. As no backtracking is
    allowed, it stick to this choice and fails.
*)

Goal False.
  Fail lazy_match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.

(** [lazy_match!] should be considered as the default, as it is easy to understand
    (no backtracking) which prevents unexpected behaviour, and yet sufficient
    for all applications where matching the syntax is a sufficient to decide what to do.

    A common application of [lazy_match!] is to use to match the shape of the
    goal or the shape of a term or type, in order to decide to do [X] or [Y].

    A basic example, is to write a tactic [split_and] that introduces the
    variable with [intros ?] if the goal is of the form [A -> B],
    split the goal with [split] if it is a product [A /\ B], and recursively
    simplify the new goals.
    In both case, the syntax check is sufficient to decide what to do as
    if its of the required form, then the branch will succeed.
    One should hence use [lazy_match!], which gives the following simple function:
*)

Ltac2 rec split_and () :=
  lazy_match! goal with
  | [ |- _ -> _ ] => intros ?; split_and ()
  | [ |- _ /\ _ ] => split > [split_and () | split_and ()]
  | [ |- _ ] => ()
  end.

Goal (True /\ ((False /\ True) /\ False)) /\ True.
  split_and ().
Abort.

Goal forall (n : nat), (forall m, m = n) /\ (False \/ False) /\ True.
  split_and ().
Abort.

Goal True \/ False.
  Fail (progress (split_and ())).
Abort.


(** 2.2 [match!]

      [match! goal with] picks the first branch that succeeds.
      If it picks a branch, and evaluation of its body fails, then it backtracks
      and choose the next branch where the pattern matches the hypotheses and goal,
      potentially the same one if all the hypotheses have not been exhausted yet.

      In the example below the first branch is picked and fails, it hence
      backtracks to its choice.
      There is only one possibility for the pattern [ |- _] as it matches any goal.
      As it has already been tried, it hence switch to the second pattern which is [ |- _].
      This branch now succeeds, hence the whole [match!] hence succeeds.
*)

Goal False.
  match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end.
Abort.


(** match!] is useful as soon as matching the syntax is not enough, and we
    need additional tests to see if we have picked the good branch or not.
    Indeed, if such a test fail raising an exception (or we make it so), then
    [match!] will backtrack, and look for the next branch matching the pattern.

    A common application of [match!] is to match the goal for hypotheses,
    that we then need to do extra-check one to decide what to do or ensure
    we have picked the good.
    If we have not, failing or triggering failure, then enables to backtrack and
    to try the next possible hypotheses.

    A basic example is to recode a simple [eassumption] tactic, that tries
    to solve the goal with [exact P] for all hypotheses [P].
    If we match the goal with the pattern [p : _ |- _] to get a [P], it is most
    likley the first hypothesis [P] picked will not solve the goal, and hence
    that [exact P] will fail.
    In this case, we want to backtrack to try the next hypothesis [P].

    It is only if [exact P] succeeds that we know we have picked the good branch.
    Consequently, we want to use [match!] and not [lazy_match!].
*)

Ltac2 my_eassumption () :=
  match! goal with
  | [p : _ |- _] =>
      printf "Try %I" p;
      let p := Control.hyp p in exact $p
  | [ |- _] => Control.zero (Tactic_failure (Some (fprintf "No such assumption")))
  end.

Goal forall P Q, P -> Q -> P.
  intros P Q p q. my_eassumption ().
Qed.

Goal forall P Q, P -> P -> Q.
  intros P Q p1 p2. Fail my_eassumption ().
Abort.


(** 2.3 [multi_match!]

      [multimtch! goal with] is more complex and subtle. It basically behaves
      like [match!] except that it will further backtrack if the choice of a
      branch leads to a subsequent failure when linked with another tactic.

      For instance, in the example below we link the [match!] with [fail],
      to make the composition fail.
      In the [match!] case, it will try the first branch, then the second that
      succeeds, then try [fail], and hence fail.
      It will hence print [branch 1] and [branch 2], then fail.
*)

Goal False.
  Fail match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end; fail.
Abort.

(** In contrast, when the composition fails [multi_match!] will further bracktrack
    to its choice of branch, in this case the second one, and try the next matching branch.
    The idea is that picking a different branch could have led to the subsequent
    tactic to succeed, as it can happen when using [constructor].
    Here, as [fail] always fails, it will still failed but we can see it did
    backtrack and tried the third branch as it will print [branch 3].
*)

Goal False.
  Fail multi_match! goal with
  | [ |- _ ] => printf "branch 1"; fail
  | [ |- _ ] => printf "branch 2"
  | [ |- _ ] => printf "branch 3"
  end; fail.
Abort.

(** [multi_match!] is meant to write tactics performing a choice, and that
    we want to link with other tactics, like the [constructor] tactic
    that we can then link with [reflexivity] or [assumption] to solve the goal.

    A basic example is to code a tactic that recursive pick [left] or [right]
    if the goal is for the form [A \/ B], which is similar to [repeat constructor].
    The choice [left] or [right] are both correct as soon as the goal is of the
    form [A \/ B]. We can only know if we have picked the good one, once chained
    with another tactic that tries to solve the goal.
    We hence need to use [multi_match!] as if we have picked the wrong side
    to prove, we want to backtrack to pick the otherwiside.

    This leads to the following small script, improved with printing to check
    the backtracking structure:

*)

Ltac2 rec left_or_right () :=
  multi_match! goal with
  | [ |- _ \/ _ ] => print_goals; printf "use left"; left; left_or_right ()
  | [ |- _ \/ _ ] => print_goals; printf "use right"; right; left_or_right ()
  | [ |- ?t ] => printf "the final goal is %t" t ; printf "-------"
  end.

Goal False \/ (False \/ True) \/ 0 = 1.
  left_or_right (); exact I.
Abort.

Goal False \/ (False \/ False) \/ (0 = 1 -> 0 = 1).
  left_or_right (); intros X; exact X.
Abort.


(** [multi_match!] is **not meant** to be used by default.
    Yes, it is the more powerful match primitive in terms of backtracking, but it
    can can be hard to understand, predict and debug, in particular for newcomers.
    Moreover, it can be expensive as it can perform an exponential number of
    backtracking attempts when linked with another tactic that can backtrack.
    It should hence only be used when needed.
*)



(** 3. Non-Linear Matching

    A pattern is non-linear when a variable [?t] appears more than one time.
    In this case, the natural question is how are this variables match.
    On the non-linear case, variable are matched up to conversions when they
    appear in different clause, and up to syntax when it appears in the same clause.

    To understand this better, let us look at an example.
    We could write a version of [eassumption] by checking for the pattern [_ : ?t |- ?t].
    In this case, as [?t] appears in different clauses -- the hypotheses and
    then conclusion -- it will matched up to conversion.
    We can check it works by supposing [0 + 1 = 0] and trying to prove [1 = 0],
    as [0 + 1] is equal to [1] up to conversion but not syntactically.
*)

Goal 0 + 1 = 0 -> 1 = 0.
  intros.
  lazy_match! goal with
  | [ _ : ?t |- ?t] => printf "succeeded: %t" t
  | [ |- _ ] => fail
  end.

(** However, if a variable appears several times in a same clause, then it is
    checked syntactically.
    For instance, in [ |- ?t = ?t], [?t] is checked syntactically as the it
    appears twice in the goal which forms one clause.
    We can check checking this by trying to match [0 + 1 = 1] which fails.
*)

Goal 1 + 1 = 2.
  Fail lazy_match! goal with
  | [ |- ?t = ?t] => printf "equality is %t" t
  | [ |- _ ] => fail
  end.
Abort.

(** A subtlety to understand is that only the hole associated to a variable will
    be checked up to conversion, other symbols are matched syntactically as usual.
    For instance, if we check for [?t, ~(?t)], the symbol [~] will matched,
    if one if found then inside the clause ~(X) that it will be checked
    up to conversion with [?t].

    Consequently, if we have [P], it will fail to match for [P -> False] as
    [~] is matched syntactically, but [P -> False] is the unfolding of [~P].
*)

Goal forall P, P -> (P -> False) -> False.
  intros.
  Fail match! goal with
  | [_ : ?t, _ : ~(?t) |- _ ] => printf "succeed: %t" t
  | [ |- _ ] => fail
  end.
Abort.

(** However, matching for [~((fun _ => P) 0)] will work as [~] will be matched,
    then [(fun _ => P)0] matched with [P] up to conversion which works.
*)

Goal forall P, P -> ~((fun _ => P) 0) -> False.
  intros.
  match! goal with
  | [_ : ?t, _ : ~(?t) |- _ ] => printf "succeed: %t" t
  | [ |- _ ] => fail
  end.
Abort.

(** It often happens that non-linear matching is not precise enough for our
    purpose, either because we would like to match both term in one clause
    up to conversion, or because we would like to use a different notation of
    equality of non-linear occurencess like syntactic equality, equality up to
    some reduction, or even up to unification.

    In this case, the best approach is to use different variables for each
    occurences we want to check, then call the equality we wish.
    For instance, to match for [P] and [~P] up to unification, we would:
    match for a pair of variables [t1], [t2] then call a unification function
    to check if one of the hypotheses is indeed a negation of the other.
*)

Goal forall P, P -> (P -> False) -> False.
  intros.
  match! goal with
  | [ _ : ?t1, _ : ?t2 |- _] =>
      Unification.unify_with_full_ts t2 '($t1 -> False);
      printf "success"
  | [ |- _ ] => fail
  end.

(** The advantage of this method is that it provides the user with a fine grained
    control to the user when and how reduction and equality tests are performed.
*)