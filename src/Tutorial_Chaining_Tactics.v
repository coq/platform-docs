(** * Tutorial: Chaining Tactics

*** Main contributors

   - Thomas Lamiaux

    *** Summary

    In this tutorial, we explain how to chain tactics together to write more
    concise code.

    *** Table of content

        - 1. Chaining Tactics Linearly
          - 1.1 ???
          - 1.2 ???
          - 1.3 Chaining is actually backtracking
        - 2. ???
          - ???
          - ???

    *** Prerequisites

    Needed:
    - No Prerequisites

    Not Needed:
    - TO FILL

    Installation:
  - Available by default with coq

*)




(** ** 1. Chaining Tactics Linearly

    *** 1.1 ??? *)

  (* INTRO TEXT *)

  Section Chaining.
  Context (A B C D E F : Type).

  Set Printing Parentheses.

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left. left. constructor.
      -- assumption.
      -- assumption.
    - left. right. constructor.
      -- assumption.
      -- assumption.
    - right. constructor.
      -- assumption.
      -- assumption.
  Qed.

(** TODO TEST: LOGICAL STEP  *)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; left. constructor.
      -- assumption.
      -- assumption.
    - left; right. constructor.
      -- assumption.
      -- assumption.
    - right. constructor.
      -- assumption.
      -- assumption.
  Qed.


(** Further, chaining tactics is particularly practical to flatten code: when a
    tactic create different subgoals, for which we want to apply the same
    reasonning for each of them.

    Typically, in the example above, in all the cases created by [constructor],
    we want to apply [assumption] to conclude the proof.
    We can hence simply write [constructor; assumption], greatly simplifying
    the proof while reflecting better the logical structure.
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; left. constructor; assumption.
    - left; right. constructor; assumption.
    - right. constructor; assumption.
  Qed.

(** *** 1.2 ???

    Chaining tactics with [tac1 ; tac2] applies the tatic [tac2] to all the subgoals created by [tac1].
    Yet, it is not always subtile enoguh as different subgoals can require different
    kind of reasonning.

    For instance, consider the example below where we need to apply diffenre tactic
    for each subgoals, namely applying [fAC] in one case and [fBD] in the other case:
*)
    Goal (A -> C) -> (B -> D) -> A * B -> C * D.
      intros fAC fBD p. destruct p as [a b].
      constructor.
      - apply fAC. assumption.
      - apply fBD. assumption.
    Qed.

(** Yet, we would still like to be able to chain tactics together to factorise
    code and make it clear.
    To do so, it is possible to combine the [;] notation
    with the notation [ [tac1 | ... | tacn] ] with one tactic per subgoal.
    The tactic [ tac; [tac1 | ... | tacn] ] will then apply [taci] to the
    i-th subgoal created by [tac].
*)

  Goal (A -> C) -> (B -> D) -> A * B -> C * D.
    intros fAC fBD p. destruct p as [a b].
    constructor; [apply fAC | apply fBD].
    - assumption.
    - assumption.
  Qed.

(** It is particularly practical when the subgoals created require
    a slitglty different logical step, before resuming the same proof script.
    In which case, we can use goal salection to do the differantied resonning
    before resuming regular chaining.

    For instance, in the proof above, in both case, we conclude the proof
    with [assumption] after applying [fAC] or [fBC].
    We can hence, further chain [ [apply fAC | apply fBD] ] to provide a
    significantly shorten proofs:
*)

  Goal (A -> C) -> (B -> D) -> A * B  -> C * D.
    intros fAC fBD p. destruct p as [a b].
    constructor; [apply fAC | apply fBD] ; assumption.
  Qed.

(** The construction [tac ; [tac1 | ... | tacn] requires a tactic per subgoal.
    Yet, in some cases, before continuing the common proof, an action is needed
    for only one subgoal.

    For instance, consider a ternary version of the example above.
    Using [constructor] creates a subgoal where we need to use [constructor]
    again, before continuing the same usual proof.
    We hence, would like to apply [constructor] once more, but only on the first branch.
*)

    Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
      intros fAD fBE fCF p. destruct p as [[a b] c].
      constructor.
      - constructor.
        -- apply fAD; assumption.
        -- apply fBE; assumption.
      - apply fCF; assumption.
    Qed.

(** This is possible by using the [idtac s] tactic that does noting but printing [s],
    or simply by leaving the expected tactic spot emppty.

    This enables to flatten, the structure of the proof, yielding a much more
    natural proof structure:
*)

    Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
      intros fAD fBE fCF p. destruct p as [[a b] c].
      constructor; [constructor| idtac "hello world"].
      - apply fAD; assumption.
      - apply fBE; assumption.
      - apply fCF; assumption.
    Qed.

    Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
      intros fAD fBE fCF p. destruct p as [[a b] c].
      constructor; [constructor|].
      - apply fAD; assumption.
      - apply fBE; assumption.
      - apply fCF; assumption.
    Qed.

(** If wished, it is then possible to further factorise the structure by
    chaining the [apply] and [assumption] as before.
*)
    Goal (A -> D) -> (B -> E) -> (C -> F) -> A * B * C -> D * E * F.
      intros fAD fBE fCF p. destruct p as [[a b] c].
      constructor; [constructor |]; [apply fAD | apply fBE | apply fCF]; assumption.
    Qed.

(** However, as you can it does not necessarily make the proof clearer.
    As a general rule chaining tactics should not be used for more than a
    a logical step, or a otherwise tedious but straigthfoward task.

    This construction is also particularly practical to get rid of trivial subgoals
    that are generated by a tactic.
    For instance, consider, the proof where a trivial subgoal is generated by [constructor]:
*)

    Goal (B -> D) -> (C -> D ) -> A * (B + C) -> A * D.
      intros fBD fCD p. destruct p as [a x].
      constructor.
      - assumption.
      - destruct x; [apply fBD | apply fCD] ; assumption.
    Qed.

(** Chaining with [ ; [assumption |] ] enables to get rid of the trivial goal,
    and make the proof flatter and nicer:
*)

    Goal (B -> D) -> (C -> D ) -> A * (B + C) -> A * D.
      intros fBD fCD p. destruct p as [a x].
      constructor; [assumption |].
      destruct x; [apply fBD | apply fCD] ; assumption.
    Qed.

(** Note that you can also apply a tactic to specific subgoals using the
    notation [only m-n,..., p-q: tac], where [n] and [m] refers to the range
    of subgoals on which you want to apply the tactic [tac].
    As a shortcut, it is also possible to just write [only m: tac] to only apply
    [tac] to the m-th subgoal:
*)
    Goal (B -> D) -> (C -> D ) -> A * (B + C) -> A * D.
      intros fBD fCD p. destruct p as [a x].
      constructor; only 1: assumption.
      destruct x; [apply fBD | apply fCD] ; assumption.
    Qed.

(** It often happens that we have several goals, for which we want to apply
    the same tactic, or do nothing.
    Consequently, to provide a bit more flexibility, it is possible to
    use the [..] notation to iterate a tactic on different subgoals.

    Assume the following context, applying [foo] to prove [forall a : A, D]
    creates
*)
  Section DotDotNotation.
    Context (foo : (A -> D) -> (B -> D) -> (C -> D) -> A + B + C -> D).
    Context (fA : A -> D).
    Context (fB : B -> D).
    Context (fC : C -> D).

    Goal forall (a : A), D.
      intros a. apply foo.
      - assumption.
      - assumption.
      - assumption.
      - left; left. assumption.
    Qed.

    Goal forall (a : A), D.
      intros a. apply foo; [.. | left; left].
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    Qed.

(** It can then futher be factorised by chaining it with [assumption] *)

    Goal forall (a : A), D.
      intros a. apply foo; [.. | left; left]; assumption.
    Qed.

(** It is possible to use this notation at any point to iterate a tactic until the next ones.
    For instance, we could also have used it to iterate [assumption].
*)

    Goal forall (a : A), D.
      intros a . apply foo; [ assumption .. | ].
      left; left. assumption.
    Qed.

(** Note, that it can be used at any point, as shown below:  *)

    Goal forall (a : A), D.
      intros a . apply foo; [ .. | assumption | ].
    Abort.

    Goal forall (a : A), D.
      intros a . apply foo; [ assumption | idtac "will be printed twice" .. | ].
    Abort.

  End DotDotNotation.


(** *** 1.3 Chaining is actually backtracking

    A substiltiy with chaining of tactics is that [;] does not only chain tactics
    together, applying them once after the other, but also does batracking.

    TODO TEXT: EXPLANATIONS
    If one of the tactic chained support backtracking, then the while

    This is noticeably the

    Consider, the following proof where we have to choose between proving the
    left side [A * B] or the right side [A * C] depending on what we know:
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; left. constructor; assumption.
    - left; right. constructor; assumption.
    - right. constructor; assumption.
  Qed.

(** TODOT TEST: Some text about left and right *)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    - left; constructor; constructor; assumption.
    - left; constructor; constructor; assumption.
    - right. constructor; assumption.
  Qed.

(** We can then further simplify the proof by factorising the [left] and [right],
    using [only 1-2:] for the extra [constructor], provinding us with one
    common proof script for all the cases:
*)

  Goal A * (B + C + D) -> A * B + A * C + A * D.
    intros x. destruct x as [a x]. destruct x as [[b | c] | d].
    all: constructor; only 1-2: constructor; constructor; assumption.
  Qed.

(** Using the backtracking ability of [;] is a simple method that can allow
    writing simple but very powerful script, as backtracking enables to deal
    with different possible choices that would be tedious to automatize otherwise.
*)


(* ** 2. Combining Tactics *)


End Chaining.