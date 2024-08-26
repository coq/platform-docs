(** * Tutorial about Rcoq (Coq) tactics

  *** Summary
  In this tutorial, we briefly introduce some main Rocq (Coq) tactics,
  that are shipped with the standard distribution of Rocq.
  Both vanilla tactics and SSReflect tactics are dealt with.
  One can work either with vanilla tactics or with SSReflect tactics,
  and short examples are provided for both sets of tactics.
  One can do most reasoning steps with the introduced tactics.
  The main take-away is to understand intuitively what is the effect of each tactic on the proof state,
  so that one has an overview of possible logical reasoning steps when in the proof mode.
  Small insecable steps are emphasised.
  The code examples in this page can serve as memo-snippets 
  to remember how to achieve some main basic logical steps within proofs in Rocq.
  
  [SSReflect] tactics are shipped with the standard Rocq distribution.
  They are made available after loading the SSReflect plugin.

  *** Table of content

  - 1. Introduction
  - 2. Main tactics
  - 3. Some more tactics
  - 4. Exercices

  *** Prerequisites
  - We assume basic knowledge of Rocq

*)

(** ** 1. Introduction

  One typically uses Rocq tactics in one of the two following ways: one exclusively uses vanilla tactics,
  or else one uses SSReflect tactics with some vanilla tactics.
  This tutorial covers some main tactics. Many tactics are twins (a vanilla one and a SSReflect one)
  that behaves similarly.
  When dealing with an SSReflect tactic, the two following aspects are not covered int his tutorial: 
  Small Scale Reflection methodology and Mathematical Components Library.
  There are some benefits to using the SSReflect set of tactics. For instance,
  they are equipped with a rewrite pattern language, 
  and fewer tactics are necessary to kill trivial goals
  (even without using this methodology or the Mathematical Components Library).
  
  Isolated basic reasoning steps are illustrated with examples. 
  The objective is to be aware of some main valid reasoning steps that are available.

  In the section 3. More tactics, 
  one will find tactics that can technically be got around with previous tactics from section 2.

  Let us start by showing how to load SSReflect tactics.
*)

(**
  To work with SSReflect tactics, one typically runs the following commands
  as is done in the following module:
*)

Module LoadSSReflect.

From Coq Require Import ssreflect.

(* One may also need to uncomment the following two lines. *)
(* From Coq Require Import ssreflect ssrfun ssrbool. *)
(* Import ssreflect.SsrSyntax. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

End LoadSSReflect.

(** ** 2. Main tactics
  Overall, there are two main tactics, [rewrite] and [apply]/[apply:].
  The syntax for the [rewrite] tactic is the same for SSReflect and vanilla Rocq.
  The colon punctuation mark at the end of the SSReflect tactic [apply:] 
  distinguishes it from the vanilla Rocq tactic [apply].
  After loading SSReflect, the default behaviour of [rewrite] is changed.
*)

(** *** Moving things

  (a completely unrelated link, just a song in a movie:
  https://www.youtube.com/watch?v=m1543Y2Em_k&pp=ygU6QnVybmluZyBMaWdodHMgLSBKb2UgU3RydW1tZXIgaW4gSSBIaXJlZCBhIENvbnRyYWN0IEtpbGxlcg%3D%3D )

  We start by showing how to move things between the current goal and the context.
  SSReflect has a simplier syntax to move things.
  With SSReflect, with [move=>] (which can sometimes be shortened to just [=>] when combined with other tactics) 
  one can move the first assumption of the goal to the local context.
  In the opposite direction,
  with [move:], one can move something from the local or global context to the first assumption
  (also called top assumption or just "top").
  Some basic steps with the [move] tactic
  (the proof script shown below does not meet coding conventions):

*)

Module MoveWithSSReflect.

From Coq Require Import ssreflect.

(* For other uses of SSReflect, one may also need to uncomment the following two lines. *)
(* From Coq Require Import ssreflect ssrfun ssrbool. *)
(* Import ssreflect.SsrSyntax. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal forall (P Q : Prop), P -> Q -> P.
Proof.
move=> P.
move=> Q.
move=> HP.
move=> HQ.
Fail move: P. (* As expected, the command "move: P" should fail here. *)
move: HQ. (* please note that HP is removed from the local context *)
move: HP.
move: Q.
move: P. (* one can keep P in the local context with: move: (P). *)
move: or_comm. (* moving something from the global context *)
Abort.

(* Several moves can be combined into one, as follows. *)

Goal forall (P Q : Prop), P -> Q -> P.
Proof.
move=> P Q HP HQ.
move: or_comm P Q HP HQ. 
Abort.

End MoveWithSSReflect.

(* With vanilla Rocq, one can move the top assumption to the local context with [intros]. *)
(* To move something from the context, one has to consider whether it comes from the local or the global context. *)
(* One can move something from the local context to top with [revert]. *)
(* One can move something from the global context to top with [generalize]. *)

Goal forall (P Q : Prop), P -> Q -> P.
Proof.
intros P.
intros Q.
intros HP.
intros HQ.
revert HQ.
revert HP.
(* Here, the command revert P would succeed and generalise over P. *)
revert Q.
revert P.
generalize or_comm. (* moving something from the global context *)
                    (* alternatively: specialize or_comm. *)
(* assert ( H_or_comm := or_comm). *)
Abort.

(* It can be simplified to: *)

Goal forall (P Q : Prop), P -> Q -> P.
Proof.
intros P Q HP HQ.
revert P Q HP HQ.
generalize or_comm.
Abort.

(**
  One goes from a goal of the form [P] to [T -> P] where [T] is a result from the global context.
  If one looks at the goal only, it seems that it has been weakened.
  However, it is indeed a generalisation and here follows an explanation why.

  One should look at the whole information that consists of both the context and the goal.
  Initially, there is a goal [P] with some term [pr : T] in the global context.
  The goal is generalised over [pr] and one gets the new goal [forall ( _ : T), P]
  also written as [T -> P]. Instead of completing the goal with the specific proof [pr]
  one aims at proving a universal quantification over that proof.
  One should thus prefer to use the tactic [generalize] over [specialize].

*)

(** *** Destructing

  The syntax for destructing is [[]].
  Destructing can let one access values of a record, do a case analysis on an inductive type, 
  split a disjunction into subgoals. 
  If new goals are introduced just after destructing, they are separated with the pipe symbols [|]
  within the brackets.
  As a result, the number of pipe symbols is the number of subgoals minus one.
  It is possible to use destructing within subgoals, subsubgoals and so on, 
  as is done with [[[HQ | [HR | HS]]]].
  With SSReflect, the [move] tactic can be used in combination with destructing.

*)

Module SSRReflectDestructing.

From Coq Require Import ssreflect.
(* It is better to place all import commands at the beginning of the file,
   contrary to what is done here. 
   Yeah, do what I say, not as I do xD *)

Section S.
Variables (T : Type) (P : T -> Prop) (y z : T).

Goal (exists u : T, P u) -> y = z.
Proof.
move=> [x].
Abort.

Goal (exists u : T, P u) -> y = z.
Proof.
move=> [x Px].
Abort.

Record Pair : Set := mkPair
 { n : nat
 ; b : bool}.

Definition incr_pair (x : Pair) := mkPair (S (n x)) (negb (b x)).

Lemma PairP (x : Pair) : incr_pair (incr_pair x) = mkPair (S (S (n x))) (b x).
Proof.
move: x.
move=> [n b]. 
by rewrite /incr_pair Bool.negb_involutive.
Qed.

Goal forall (Q R : Prop), Q \/ R -> R \/ Q.
Proof.
move=> Q R. 
move=> [HQ | HR].
- right.
  exact: HQ.  
- left.
  exact: HR.
Qed.

Goal forall (Q R S : Prop), Q \/ R \/ S -> S \/ R \/ Q.
Proof.
move=> Q R S. 
move=> [HQ | HRS].
- admit. (* a proof is given in the next Goal *)
- move: HRS => [HR | HS].
  + admit.
  +
Abort.

(** 
  The previous introductions can be shortened, as follows:
*)

Goal forall (Q R S : Prop), Q \/ R \/ S -> S \/ R \/ Q.
Proof.
move=> Q R S. 
move=> [HQ | [HR | HS]].
- by right; right.
- by right; left. 
- by left.
Qed.

End S.
End SSRReflectDestructing.

Module Destructing.

Section S.
Variables (T : Type) (P : T -> Prop) (y z : T).

Goal (exists u : T, P u) -> y = z.
Proof.
intros [x Px].
Abort.

Record Pair : Set := mkPair
 { n : nat
 ; b : bool}.

Definition incr_pair (x : Pair) := mkPair (S (n x)) (negb (b x)).

Lemma PairP (x : Pair) : incr_pair (incr_pair x) = mkPair (S (S (n x))) (b x).
Proof.
case x.
intros n b.
unfold incr_pair.
simpl.
now rewrite Bool.negb_involutive.
Qed.

Goal forall (Q R : Prop), Q \/ R -> R \/ Q.
Proof.
intros Q R.
intros [HQ | HR].
- now right.
- now left.
Qed.

Goal forall (Q R S : Prop), Q \/ R \/ S -> S \/ R \/ Q.
Proof.
intros Q R S. 
intros [HQ | HRS].
- admit.
- revert HRS. 
  intros [HR | HS].
  + admit.
  +
Abort.

(** 
  The previous script can be shortened into:
*)

Goal forall (Q R S : Prop), Q \/ R \/ S -> S \/ R \/ Q.
Proof.
intros Q R S. 
intros [HQ | [HR | HS]].
- now right; right.
- now right; left. 
- now left.
Qed.

End S.
End Destructing.


(** *** Simplifying

  At any stage within a proof script, one can try to simplify the goal.
  The simplification does not fail, even if no simplification could be done.
  The syntax for simplification is [rewrite /=] with the SSReflect tactic and [simpl] with vanilla Rocq
  (with similar but slighlty different behaviours).
  The SSReflect simplification tactic is a special case for the [rewrite] tactic.

  It is possible to use patterns to guide the SSReflect tactic 
  to simplify only some specific parts of the goal.
  See the section 'Rewriting pattern' for the use of patterns.
  We will see that it is possible to combine SSReflect moving with simplification attempt.
    
*)

(**

  At any proof step, one can start with ask to try to kill the current goal 
  which should be trivial for Rocq.
  The SSReflect tactic [by []] tries to kill the goal - which is expected to be trivial for Rocq - otherwise it fails.
  This SSReflect tactic can cover cases that require a few tactics with vanilla Rocq, 
  such as [reflexivity], [assumption] and [now trivial].

  One can require a proof line to succeed in killing the current goal.
  With vanilla Rocq, this is achieved by beginning the line with [now]
  ([now trivial] is preferred over just [trivial], because the latter can silently fail).

*)

Module Simplification.

Definition foo (b : bool) := match b with
| true => false
| false => true
end.

Goal foo true = false.
Proof.
simpl.
reflexivity.
Qed.

End Simplification.

Module SSRSimplification.

From Coq Require Import ssreflect.

Definition foo (b : bool) := match b with
| true => false
| false => true
end.

Goal foo true = false.
Proof.
rewrite /=.
by [].
Qed.

End SSRSimplification.

Module SSRNonTrivialCase.

From Coq Require Import ssreflect.

Goal 2 * 3 = 3 + 3.
Proof.
by [].
Qed.

End SSRNonTrivialCase.

Module NonTrivialCase.

Goal 2 * 3 = 3 + 3.
Proof.
now simpl.
Qed.

End NonTrivialCase.

(** *** Rewriting 

  Rewriting is performed with the [rewrite] tactic.
  The vanilla Rocq version of [rewrite] is loaded by default.
  After having loaded SSReflect, the behaviour of [rewrite] is the one from SSReflect.
  Some use cases are presented below.

*)

(** **** Rewriting with equalities

  The [rewrite] tactic let one rewrite the goal with a given equality from the context.
  Let's look at the following example.

*)

Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof.
intros T a b c H. (* it is possible to combine several [intros] into a single one *)
rewrite H.
now trivial.
Qed.

(** 
  In this proof, the last two steps can be combined into a single one with: [now rewrite H]. 
  One can also rewrite from right to left instead.
*)

Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof.
intros T a b c H. (* it is possible to combine several move into one *)
rewrite <-H. (* rewrites with the equality H from right to left *)
now trivial.
Qed.

(**
  A shorter version of the proof script:
*)
Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof. now intros T a b c H; rewrite H. Qed.

(**

  A similar script with the SSReflect [rewrite] tactic can be:

*)

Module SSRRewrite.

From Coq Require Import ssreflect.

Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof.
move=> T a b c H. (* it is possible to combine several [intros] into a single one *)
rewrite H.
by [].
Qed.

(** 
  In this proof, the last two steps can be combined into a single one with: [by rewrite H]. 
  One can also rewrite from right to left instead.
*)

Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof.
move=> T a b c H. (* it is possible to combine several move into one *)
rewrite -H. (* rewrites with the equality H from right to left *)
by [].
Qed.

(**
  A shorter version of the code:
*)
Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof. by move=> T a b c H; rewrite H. Qed.

End SSRRewrite.

(** *** Unfolding a definition.

  Unfolding a definition is done with [rewrite /the_definition_to_be_unfolded] with SSReflect
  and [unfold] with vanilla Rocq.

*)

Definition secret : nat := 42.

Goal secret = 41 + 1.
Proof.
unfold secret.
fold secret. (* folding back *)
now trivial.
Qed.

Module SSRUnfolding.

From Coq Require Import ssreflect.

Definition secret : nat := 42.

Goal secret = 41 + 1.
Proof.
rewrite /secret.
rewrite -/secret. (* folding back *)
by [].
Qed.

End SSRUnfolding.

(** *** The [apply] tactic 

The [apply] tactic tries to match the conclusion (and eventually some premisses) 
of the lemma being applied with the goal. It lets one do backward reasoning.
The syntax with SSReflect is [apply:] and
one can require that it should kill the goal with [exact:].
Let's look at some examples.

*)

Goal forall (A B : Prop) (HA : A) (H : A-> B), B.
Proof.
intros A B HA H.
apply H.
assumption.
Qed.

Goal forall (A B C : Prop) (HA : A) (H : A -> B -> C), B -> C.
Proof.
intros A B C HA H.
apply H. (* the premise B has been included *)
assumption.
Qed.

Module SSReflectApply.

From Coq Require Import ssreflect.

Goal forall (A B : Prop) (HA : A) (H : A-> B), B.
Proof.
move=> A B HA H.
apply: H. (* or better: exact: H *)
by [].
Qed.

Goal forall (A B C : Prop) (HA : A) (H : A -> B -> C), B -> C.
Proof.
move=> A B C HA H.
apply: H. (* the premise B has been included *)
by [].
Qed.

End SSReflectApply.

(** *** Generalisation 
The SSReflect syntax for generalising is the same as for moving things to top. *)


Module SSRGeneralisation.

Require Import Nat.
From Coq Require Import ssreflect.

Goal (4 + 1) ^ 2 = 4 ^ 2 + 4 * 2 + 1 .
Proof.
move: 4. (* generalises over the term 4 *)
move=> n.
Abort.

Goal 1 + 1 = 1 * 1.
Proof.
move: 1 => n. (* generalises over all occurrences of 1 *)
Abort.

Goal 1 + 1 = 1 * 1.
Proof.
move: {2}1 => n. (* generalises over the second occurrence of 1 *)
Abort.

Goal 1 + 1 = 1 * 1.
Proof.
move: {2 4}1 => x. (* generalises over the second and the forth occurrence of 1 *)
Abort.

Goal forall (T : Type) (l : list T) (C : Prop), C.
Proof.
move=> T l C.
move: (eq_refl (length l)). (* this illustrates moving something from the global context to top *)
move: {2}(length l) => n. (* generalises over the second occurrence only *)
Abort.

End SSRGeneralisation.

Module Generalisation.

Require Import Nat.

Goal (4 + 1) ^ 2 = 4 ^ 2 + 4 * 2 + 1 .
Proof.
generalize 4. (* generalises over the term 4 *)
intros n. 
Abort.

Goal 1 + 1 = 1 * 1.
Proof.
generalize 1. (* generalises over all occurrences of 1 *)
intros n. 
Abort.

Goal 1 + 1 = 1 * 1.
Proof.
generalize 1 at 2. (* generalises over the second occurrence of 1 *)
intros n.
Abort.

Goal 1 + 1 = 1 * 1.
Proof.
generalize 1 at 2 4. (* generalises over the second and the forth occurrence of 1 *)
intros n. 
Abort.

Goal forall (T : Type) (l : list T) (C : Prop), C.
Proof.
intros T l C.
generalize (eq_refl (length l)). (* this illustrates moving something from the global context to top *)
generalize (length l) at 2. (* generalises over the second occurrence only *)
intros n.
Abort.

End Generalisation.

(** *** Inductive reasoning

  Inductive reasoning is initiated with the [induction] tactic in vanilla Rocq 
  and the [elim:] tactic with SSReflect.
  
*)

Module Induction.

Require Import Lists.List.

Variable (T : Type).

Goal forall (l m : list T), length (l ++ m) = length l + length m.
Proof.
intros l.
induction l.
- intros m.
  now simpl.
- intros m.
  rewrite <-app_comm_cons.
  simpl.
  now rewrite IHl.
Qed.

End Induction.

Module SSRInduction.

From Coq Require Import ssreflect.

Section S.
Variable (T : Type).

Goal forall (l m : list T), length (l ++ m) = length l + length m.
Proof.
move=> l.
elim: l => //= a l IH m.
by rewrite IH.
Qed.

End S.
End SSRInduction.

Module OtherInduction.

Require Import Lists.List.

Section S.
Variable (T : Type).

Goal forall (l m : list T), length (l ++ m) = length l + length m.
Proof.
intros l m.
revert m.
induction l using rev_ind. (* induction is done with the inductive principle last_ind *)
- now intros m'.
- intros m'.
  rewrite IHl; simpl.
  rewrite <-app_assoc.
  rewrite IHl; simpl.
  rewrite <-PeanoNat.Nat.add_assoc.
  now rewrite <-PeanoNat.Nat.add_1_l.
Qed.

End S.
End OtherInduction.

Module SSROtherInduction.

Require Import Lists.List.
From Coq Require Import ssreflect.

(* The result [rev_ind] is an alternative induction principle *)
(* that can be applied at the elimination step in the previous example. *)
(* Instead of using the default induction principle, *)
(* the syntax [elim/rev_ind:] combines elimination with view application. *)
(* Starting again from the same goal and applying the [rev_ind] view: *)

Section S.
Variable (T : Type).

Goal forall (l m : list T), length (l ++ m) = length l + length m.
Proof.
move=> l m.
move: m.
elim/rev_ind: l. (* elimination is done with the inductive principle last_ind *)
- by move=> m'.
- move=> m' a IH l'.
  rewrite IH /=.
  rewrite <-app_assoc.
  rewrite IH.
  rewrite /=.
  rewrite -PeanoNat.Nat.add_assoc.
  by rewrite PeanoNat.Nat.add_1_l.
Qed.

End S.
End SSROtherInduction.

(** *** Congruence

  When an equality is required between two applications of the same function, 
  it suffices to prove that the corresponding arguments of both applications are equal.
  With vanilla Rocq, this is achieved with the [congruence] tactic.
  With SSReflect, this is achieved with the [congr] tactic.

  For instance, in the following examples it is required to prove [op w x = op y z].
  This goal has the form of an equality with the same function applied in each member.
  The first arguments are [w] on the left and [y] on the right.
  The second arguments are [x] on the left and [z] on the right.
  It is sufficient to prove that [w = y] and [x = z].

*)

Module SSRCongruence.

From Coq Require Import ssreflect.

Section S.
Variables (T : Type) (op : T -> T -> T) (w x y z : T).

Goal w = y -> x = z -> op w x = op y z. 
Proof.
move=> eq_wy eq_xz.
congr op.
- exact: eq_wy.
- exact: eq_xz.
Qed.

End S.
End SSRCongruence.

Module Congruence.

Section S.
Variables (T : Type) (op : T -> T -> T) (w x y z : T).

Goal w = y -> x = z -> op w x = op y z. 
Proof.
intros eq_wy eq_xz.
congruence.
Qed.

End S.
End Congruence.

(**
  In the example above, it is also possible to use the [rewrite] tactic 
  and get around the use of congruence.
*)

(**
  If an assumption is used to rewrite just after being introduced and then no more used,
  it is possible to use the [->] syntax:
*)

Module MoveAndRewrite.

From Coq Require Import ssreflect.

Section S.
Variables (T : Type) (op : T -> T -> T) (w x y z : T).

Goal w = y -> x = z -> op w x = op y z. 
Proof.
move => ->.
move => ->.
by [].
Qed.

Goal w = y -> x = z -> op w x = op y z. 
Proof. by move => -> ->. Qed. (* the shortest rewrite script for this proof *)

Goal w = y -> x = z -> op w x = op y z. 
Proof. 
move->. 
by move ->. 
Qed.

End S.
End MoveAndRewrite.


(** *** Forward reasoning
  
  To do forward reasoning.
  one can use either the SSReflect tactic, [have:], or the vanilla Rocq tactic [assert].

  From the point of view of proof engineering with Rocq, 
  one generally prefers to work on the goal over working on the local context.
  This proof style is used in the Mathematical Components Library and is orthogonal to using SSReflect tactics.
  One benefit of this style is to get failure earlier when the script gets broken, 
  and thus it is easier to locate the proof steps that need to be fixed. Instead of working on the local context 
  (for instance by using [rewrite in] on an hypothesis in the local context)
  it is preferable to work on it while it is still in the goal and before it is introduced to the local context.
  This way, one avoids relying on the names of the introduced assumptions.
  It may also be possible to factor some treatments and remove some subgoals right away,
  which let one keep fewer subgoals (and thus sometimes avoid relying on the order of introduction of subgoals).
  Pushing something to top might be changed without creating an error immediately,
  leading to more difficulties when maintaining the script.
  This difficulty can be more apparent when one needs to fix a proof script 
  to reuse old code or code written by others
  (and even more if one is just a user of the code and needs to fix a proof script).

  Still, one may want to use forward reasoning occasionally.

*)

Goal forall (n : nat), n * n = 0 -> n + 1 = 1.
Proof.
intros n Hn.
assert (n = 0).
- apply PeanoNat.Nat.eq_square_0.
  assumption.
- rewrite H. 
  trivial.
Qed.

Module ForwardReasoningWithSSReflect.

From Coq Require Import ssreflect.

Goal forall (n : nat), n * n = 0 -> n + 1 = 1.
Proof.
move=> n Hn.
have: n = 0.
- by apply/PeanoNat.Nat.eq_square_0. (* this is a view application *)
- by move ->.
Qed.

(* It can be written more shortly: *)

Goal forall (n : nat), n * n = 0 -> n + 1 = 1.
Proof.
move=> n /PeanoNat.Nat.eq_square_0 Hn. (* move + view application *)
by have: n = 0 => // ->.
Qed.

(* In this example, it is better to avoid forward reasoning. *)

Goal forall (n : nat), n * n = 0 -> n + 1 = 1.
Proof. by move=> n /PeanoNat.Nat.eq_square_0 ->. Qed.

End ForwardReasoningWithSSReflect.

(** 
  The [have:] tactic can be combined with destructing [[]] and with rewriting [->].
  Below are some examples:
*)

Module MoreForwardReasoning.
(* From Coq Require Import ssreflect. *)

Section S.

Require Import List.

Variable (T : Type).
Hypothesis eq_dec : forall x y : T, {x = y} + {x <> y}.

Lemma nodupIn (a : T) (l : list T) : 
  In a l -> nodup eq_dec (a :: l) = nodup eq_dec l.
Proof.
intros In_al.
simpl.
now case (in_dec eq_dec a l); intros H; trivial.
Qed.

Goal forall (x y : T) (l : list T), 
  List.nodup eq_dec (x::(y::l)) = if (eq_dec x y) 
                                  then List.nodup eq_dec (x::l) 
                                  else List.nodup eq_dec (x::(y::l)).
Proof.
intros x y l.
generalize (eq_dec x y).
intros [eq_xy|neq_xy].
- rewrite eq_xy.
  clear eq_xy.
  rewrite nodupIn; last exact (in_eq y l).
   reflexivity.  
- reflexivity.
Qed.

End S.
End MoreForwardReasoning.

Module MoreSSRForwardReasoning.
From Coq Require Import ssreflect.

Section S.

Require Import List.

Variable (T : Type).
Hypothesis eq_dec : forall x y : T, {x = y} + {x <> y}.

Lemma nodupIn (a : T) (l : list T) : 
  In a l -> nodup eq_dec (a :: l) = nodup eq_dec l.
Proof.
move=> In_al /=.
by case: (in_dec eq_dec a l). 
Qed.

Goal forall (x y : T) (l : list T), 
  List.nodup eq_dec (x::(y::l)) = (if (eq_dec x y) 
                                  then List.nodup eq_dec (x::l) 
                                  else List.nodup eq_dec (x::(y::l)))%GEN_IF.
Proof.
move=> x y l.
have [->|neq_xy] := eq_dec x y.
- rewrite nodupIn; first exact: (in_eq y l).
  by case: (eq_dec y y).
- by case: (eq_dec x y).
Qed.

End S.
End MoreSSRForwardReasoning.


(** *** Changing view
   
  View change - also called view application - is performed on the top assumption with the SSReflect tactic [move/]
  or on the conclusion with the tactic [apply/].
  It replaces it with a "different view".
  The conclusion can be replaced with a stronger conclusion
  and the top assumption can be replaced with a weaker asumption (when it is not the conclusion).

  One specific case of view application results are reflection results (which use the [reflect] keyword).
  A reflection establishes the equivalence between a proposition and a boolean
  (the truth of the proposition is thus decidable).
  In this context, a boolean can always be coerced to a proposition 
  and this is done with the coercion [is_true] on the Mathematical Components Library.
  By exploiting a reflection result, a proposition can be replaced with an equivalent boolean 
  and conversely a boolean can be replaced with an equivalent proposition.
  This is part of the Small Scale Reflection methodology.
 
  Please note that one can use view application without necessarily using reflection.

  Let's look at some examples.

*)

Module ChangingView.

From Coq Require Import ssreflect.

Section S.
Variables (A B C D E : Prop).
Hypothesis (H : B -> C).

Goal B -> D -> E.
Proof.
move/H. (* weakens B to C *)
Abort.

Goal A -> C.
Proof.
move=> HA.
apply/H. (* strenghten C to B *)
move: HA.
Abort.

Hypothesis (H2 : D -> (B -> C)).

Goal A -> B -> C.
Proof.
move=> A' /=.
apply/H2.
Abort.

(*
  These examples also work with equivalence instead of implication.
*)

Hypothesis (H3 : B <-> C).

Goal B -> D -> E.
Proof.
move/H3. (* weakens B to C *)
Abort.

Goal A -> C.
Proof.
move=> HA.
apply/H3. (* strenghten C to B *)
move: HA.
Abort.

(* 
  Some examples of view changing are now shown with boolean reflection.

*)

From mathcomp Require Import ssrbool ssrnat.

Check minn_idPr.

Variables (m n : nat) (P : Prop).

Goal minn m n = n -> P.
Proof.
move/minn_idPr.
Abort.

(*
  One can combine changing view with moving things:
*)

Goal minn m n = n -> P.
Proof.
move/minn_idPr=> H'.
Abort.

(*
  Some other examples:
*)

Goal n <= m-> P.
Proof.
move/minn_idPr.
Abort.

Goal P -> minn m n = n.
Proof.
move=> H'.
apply/minn_idPr.
Abort.

Goal P -> n <= m.
Proof.
move=> H'.
apply/minn_idPr.
Abort.

End S.
End ChangingView.

Module ChangingViewVanillaCoq.

Variables (P Q R : Prop).
Hypothesis (H : P <-> Q).

Goal P.
Proof.
apply H.
(* apply <- H. *)
Abort.

Goal Q.
Proof.
apply H.
(* apply -> H. *)
Abort.

End ChangingViewVanillaCoq.


(** Rewriting pattern. *)

(** 
  SSReflect offers rewrite patterns to guide Rocq to select specific matches for a rewrite.
  By default (when no pattern is specified) the first match is selected, which is not necessarly the desired effect.
  Please not that match and occurence differs.
  A pattern has several matches - eventually none - and each match has one or multiple occurrences.
  Let's look at some examples. 
*)

Module SSReflectRewritePatterns.

From Coq Require Import ssreflect.

Section S.

Variable (T : Type).
Variables (add mul : T -> T -> T).

Local Notation "x + y" := (add x y).
Local Notation "x * y" := (mul x y).

Variable (c : T).
Hypothesis H : forall (x : T), x = c.

Variables (a b : T).

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [LHS]H. (* rewrites the left-hand side of the equality *)
Abort.

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [RHS]H. (* rewrites the right-hand side of the equality *)
Abort.

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [a+b]H. (* rewrites the all occurrences of a+b with H *)
Abort.

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [a+b in LHS]H. (* rewrites the all occurrences of a+b in the left-hand side *)
Abort.

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite {2}[a + b]H. (* rewrites the second occurrence of a+b with H *)
Abort.

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [a + b + _]H. (* rewrites occurences of the first match of a + b + _ *)
Abort.

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [X in X + b]H. (* the pattern X + b is matched against a + b then a is rewritten in occurences of a + b *)
Abort.

(* 
  The following examples shows that we can explicit a pattern 
  to the point that exactly one [b] is rewritten, 
  the one in the middle in the term [a + b + b]. 
*)

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [X in (_ + _)* _ + (_ + X + _)* _ * _]H.
Abort.

End S.

End SSReflectRewritePatterns.

Module SomeMoreSSReflectPatterns.

From Coq Require Import ssreflect.
From mathcomp Require Import ssrbool ssrnat order.

Local Open Scope nat_scope.
Local Open Scope order_scope.

Variables (a b c : nat).

Hypothesis H : forall x, x = c.

Goal (a + b) * a + (a + b + a) * b <= (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [leLHS]H.
Abort.

Goal (a + b) * a + (a + b + a) * b < (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [ltRHS]H.
Abort.

End SomeMoreSSReflectPatterns.

(** ** 3. More tactics
*)

(** *** Case analysis

  Case analysis is performed with [case] with vanilla Rocq
  and with [case:] with SSReflect.
  The colon punctuation mark at the end of [case:] distinguishes both tactics.

*)

Module CaseAnalysis.
Section S.

Variables (a b : nat). 

Definition f n := match n with
  | 0 => a
  | S n => b + n
end.

Require Import Nat.
Goal forall (n : nat), f n <= max a (b + n).
Proof.
intros n.
case n.
(* the goal is splitted into two goals *)
- simpl.
  rewrite PeanoNat.Nat.add_0_r.
  exact (PeanoNat.Nat.le_max_l a b).
- intros m.
  simpl.
  apply (PeanoNat.Nat.le_trans _ _ _ (ssreflect.iffLR (PeanoNat.Nat.add_le_mono_l _ _ _) (PeanoNat.Nat.le_succ_diag_r _))).
  exact (PeanoNat.Nat.le_max_r a (b + S m)).
Qed.

End S.
End CaseAnalysis.

Module SSReflectCase.

From Coq Require Import ssreflect.

Section S.

Variables (a b : nat). 

Definition f n := match n with
  | 0 => a
  | S n => b + n
end.

Require Import Nat.
Goal forall (n : nat), f n <= max a (b + n).
Proof.
move=> n.
case: n.
(* the goal is splitted into two goals *)
- rewrite /=.
  rewrite PeanoNat.Nat.add_0_r.
  exact: (PeanoNat.Nat.le_max_l a b).
- move=> m.
  rewrite /=.
  apply: (PeanoNat.Nat.le_trans _ _ _ (ssreflect.iffLR (PeanoNat.Nat.add_le_mono_l _ _ _) (PeanoNat.Nat.le_succ_diag_r _))).
  exact: (PeanoNat.Nat.le_max_r a (b + S m)).
Qed.

(* The previous script can be simplified as follows: *)

Require Import Nat.
Goal forall (n : nat), f n <= max a (b + n).
Proof.
move=> /= [|n].
- rewrite PeanoNat.Nat.add_0_r. 
  exact: (PeanoNat.Nat.le_max_l a b).
- apply: (PeanoNat.Nat.le_trans _ _ _ (ssreflect.iffLR (PeanoNat.Nat.add_le_mono_l _ _ _) (PeanoNat.Nat.le_succ_diag_r _))). 
  exact: (PeanoNat.Nat.le_max_r a (b + S n)).
Qed.

End S.


(** 
  It is possible to combine moving ([move =>]) 
  with simplification [/=] and with removing trivial goals [//].
  In the following script, after the case analysis, the first goal is trivial and removed by [//].
  Thus, only one goal remains and [n] can be introduced without using the pipe symbol.
*)

End SSReflectCase.

(** *** Specialising 

  One can always weaken the top assumption by specialising it. 
  With vanilla Rocq, this can be achieved with the [specialize] tactic.
  With SSReflect, it can be achieved as a special case of view application, with the syntax [/(_ value)].
  In the following example, the assumption [forall y, P y] is specialised with [x],
  which results in the asumption [P x]. 

*)

Module Specialise.

Section S.
Variables (T : Type) (P : T -> Prop) (Q : Prop) (a : T).
Hypothesis H : P a -> Q.

Goal (forall (x : T), P x) -> Q.
Proof.
intros H'.
specialize (H' a).
apply H.
assumption.
Qed.

End S.
End Specialise.


Module SSReflectspecialise.

From Coq Require Import ssreflect.

Section S.
Variables (T : Type) (P : T -> Prop) (Q : Prop) (a : T).
Hypothesis H : P a -> Q.

Goal (forall (x : T), P x) -> Q.
Proof.
move/(_ a).
exact: H.
Qed.

End S.
End SSReflectspecialise.

(** *** Discarding top

  Discarding the top assumption can be achieved by introducing it with [_] instead of a proper name.
  With SSReflect, this writes [move=> _] and with vanilla Rocq this writes [intros _].
  as in the following example.

*)
Goal forall (P Q : Prop), P -> Q -> P.
Proof.
intros P Q HP _.
exact HP.
Qed.

Module SSReflectDiscard.

From Coq Require Import ssreflect.

Goal forall (P Q : Prop), P -> Q -> P.
Proof.
move=> P Q HP _.
exact: HP.
Qed.

End SSReflectDiscard.

(**
  One can also discard something from the local context.
  It may be interesting to do so to keep a smaller local context 
  and to emphasise that it is not used anymore in the proof.
  With SSReflect, this is achieved with the syntax [move=> {something}].
  With vanilla Rocq, one can do it with the [clear] tactic.
  Here is an example:
*)

Module SSReflectDiscardFromLocalContext.

From Coq Require Import ssreflect.
From mathcomp Require Import ssrbool eqtype ssralg ssrnum.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Variable (R : fieldType).
Variable (x : R).

Goal x != 0 -> (x ^+ 2) / x = x.
Proof.
move=> x_neq_0.
rewrite -mulrA.
rewrite mulfV.
- move=> {x_neq_0}. (* we can discard x_neq_0 here *)
  by rewrite mulr1.
- exact: x_neq_0.
Qed.

End SSReflectDiscardFromLocalContext.

Module DiscardFromLocalContext.

Variables (P Q R : Prop).

Goal P -> (P -> Q) -> (Q -> R) -> R.
Proof.
intros HP HPQ HQR.
apply HQR.
clear HQR.
apply HPQ.
clear HPQ.
exact HP.
Qed.

End DiscardFromLocalContext.

(** ** 4. Exercices
  with SSReflect.
*)

From Coq Require Import ssreflect.

(** *** Exercice 1
  For this exercice, you may want to use the vanilla tactic [split].
*)

Goal forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
move=> P Q [HP HQ].
split.
- exact: HQ.
- exact: HP.
Qed.

(** *** Exercice 2
*)

Goal forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
move=> P Q [HP | HQ].
- right.
  exact: HP.
- left.
  exact: HQ.
Qed.

(** *** Exercice 3
*)

Module Exercice3.

From mathcomp Require Import ssrbool ssrnat div.

Local Open Scope nat_scope.

Lemma div2nSn (n : nat) : 2 %| n * n.+1.
Proof. by rewrite dvdn2 oddM /= andbN. Qed.

End Exercice3.
