(** * Tutorial about SSReflect tactics

  *** Summary
  In this tutorial, we introduce the main [SSReflect] tactics
  with which one can do most reasoning steps.
  After mastering this rather small set of tactics,
  one should be able to write large parts of proof scripts and many complete proof scripts
  from the proof scripts one is already able to write with vanilla Coq.
  The main take-away is to understand intuitively what is the effect of each tactic on the proof state,
  so that one have an overview of possible logical reasoning steps when in the proof mode
  (within the kewwords [Proof] and [Qed]).
  Small insecable steps are emphasised, however the examples can seem artificial
  and the shown scripts do not necessarly meet coding conventions.
  The code examples in this page serve only as memo-snippets 
  to remember how to achieve the main basic logical steps inside proof.
  
  [SSReflect] tactics are shipped with the standard Coq distribution.
  The default proof mode is “Classic” and comes with the Ltac​﻿ tactic language. 
  SSReflect tactics are made available after loading the SSReflect plugin.

  *** Table of content

  - 1. Introduction
  - 2. SSReflect tactics
  - 3. More SSReflect tactics
  - 4. Exercices

  *** Prerequisites
  - We assume known basic knowledge of Coq

  Installation: the SSReflect set of tactics is shipped with the Coq distribution.
*)



(** ** 1. Introduction

  SSR means Small Scale Reflection,
  which is a methodology that can been used in computer-assisted formalisation with Coq.
  This methodology goes beyond just using SSRfeflect tactics and is not covered in this tutorial.
  There is a benefit to using this set of tactics
  since one can achieve most proof steps with a relatively small set of tactics
  (even without using this methodology or the Mathematical Components Library).

  Let us start by importing SSReflect.
*)

From Coq Require Import ssreflect.

(* One may also need to uncomment the following two lines. *)
(* From Coq Require Import ssreflect ssrfun ssrbool. *)
(* Import ssreflect.SsrSyntax. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *** Some terminology

  During an interactive session with Coq, one should see three panels:
  _ the source code, a .v file
  _ the goal panel, which displays proof states (focused goals and local context of the current goal)
  _ the answer panel.
  

*)

(** ** 2. SSReflect tactics
  The two main tactics are [rewrite] and [apply:]. 
  There are already a [rewrite] and [apply] tactics in vanilla Coq (before loading SSReflect).
  The colon punctuation mark at the end of [apply:] distinguishes it 
  from the [apply] tactic from vanilla Coq.
  After loading SSReflect, the default behaviour of [rewrite] is changed. 
  Both [rewrite] tactics are similar but they behave differently and have syntactic differences.
*)

(** *** Moving things

(a completely unrelated link, just a song in a movie:
https://www.youtube.com/watch?v=m1543Y2Em_k&pp=ygU6QnVybmluZyBMaWdodHMgLSBKb2UgU3RydW1tZXIgaW4gSSBIaXJlZCBhIENvbnRyYWN0IEtpbGxlcg%3D%3D )

We start by showing how to [move] things between the current goal and the context.
With [move=>] one can move the first assumption of the goal to the local context.
With [move:] one can move something from the local or global context to the first assumption
(also called "top").
You are invited to execute the following example step-by-step 
while looking at the goal panel.
Please not that the code showed below does not meet coding conventions.

*)

Goal forall (P Q : Prop), P -> Q.
Proof.
move=> P.
move=> Q.
move=> p.
Fail move: P. (* The command "move: P" should fail. *)
move: p.
move: Q.
move: P.
move: or_comm. (* moving something from the global context *)
Abort.

(** *** Destructing

  The [move] tactic can be used in combination with destructing, whose syntax is [[]].
  Destructing can let one access values of a record, do a case analysis on an inductive type, 
  split a disjunction into subgoals. 
  If new goals are introduced just after destructing, they are separated by the pipe symbols [|]
  within the brackets.
  As a result, the number of pipe symbols is the number of subgoals minus one.
  It is possible to use destructing within subgoals, subsubgoals and so on, 
  as in done with [[move=> [HQ | [HR | HS]]]].

*)

Module Destructing.

From mathcomp Require Import ssrbool ssrnat.
(* Tt is better to place all import commands at the beginning of the file,
   contrary to what is done here. 
   Yeah, do what I say, not as I do xD *)

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

Lemma PairP (x : Pair) : n x <= n x + (b x).
Proof.
move: x.
move=> [n b].
rewrite /=.
(* proof to be finished *)
Abort.

Goal forall (Q R S : Prop), Q \/ R -> S.
Proof.
move=> Q R S. 
move=> [HQ | HR].
- admit.
-
Abort.

Goal forall (Q R S U : Prop), Q \/ R \/ S -> U.
Proof.
move=> Q R S U. 
move=> [HQ | HRS].
- admit.
- move: HRS => [HR | HS].
  + admit.
  +
Abort.

(** 
  The previous script can be shortened into:
*)

Goal forall (Q R S U : Prop), Q \/ R \/ S -> U.
Proof.
move=> Q R S U. 
move=> [HQ | [HR | HS]].
- admit.
- admit. 
-
Abort.


End Destructing.

(** *** Simplifying

  At any stage within a proof attempt, one may want to try to simplify the goal
  with the tactic [rewrite /=],
  which is a special case for the [rewrite] tactic.
  The tactic [rewrite /=] does not fail, even if no simplification could be done.

  It is possible that simplifying does actually something but leads to a less readable term.
  In this case, you would rather step back in order to keep the goal (and local context) readable.
  It is also possible that it simplifies too much, 
  because simplification applies undesirably at several parts of the goal.
  In this case, you may consider using patterns to guide the tactic 
  to simplify only some specific parts of the goal.
  See *** for the use of patterns.
  We will see that it is possible to combine moving with simplification attempt.
    
*)

Definition foo (b : bool) := match b with
| true => false
| false => true
end.

Goal foo true = false.
Proof.
rewrite /=.
by [].
Qed.

(**

  The tactic [by []] tries to kill the goal, otherwise it fails.

*)

(** *** Rewriting 

  Rewriting is performed with the [rewrite] tactic.
  Some use cases are presented below.

*)

(** **** Rewriting with equalities

One of the use cases of the [rewrite] tactic is to rewrite the goal with a given an equality from the context.
Let's look at the following example.

*)

Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof.
move=> T a b c H. (* it is possible to combine several [move] into one *)
rewrite H. (* rewrites with the equality H from left to right *)
by [].
Qed.

(**
  It is convenient to reason with the Coq builtin equality [=].
*)

(** 
  In this proof, the last two steps can be combined into a single one: [by rewrite H]. 
  If you want, you can try to rewrite from right to left instead.
*)

Goal forall (T : Type) (a b c : T) (H : a = b), a = c -> b = c.
Proof.
move=> T a b c H. (* it is possible to combine several move into one *)
rewrite -H. (* rewrites with the equality H from right to left *)
by [].
Qed.


(** One can combine [rewrite] and partial application.
    Let's look at the following example.
*)

Module AnotherRewrite.

(* it is better to import HB in order to display more nicely some messages *)
(* however it seems it is not available in jsCoq at the moment *)
(* From HB Require Import structures. *) 
From mathcomp Require Import ssrbool ssralg ssrnum.

(* Import GRing.Theory Num.Theory. *)
Local Open Scope ring_scope.

Variable (R : numDomainType).

Lemma add_leq_right (z x y : R) : (x <= y) = (x + z <= y + z).
Proof.
(* we are going to use this admitted lemma *)
(* proving this lemma can be left as an exercice once you are emore familiar with SSReflect tactics *)
(* and have started exploring the Mathematical Components Library. *)
Admitted.

(** In the lemma [add_leq_right], please note that the argument [z] is in the first position.
*)

Goal forall (x : R), x <= x.
Proof.
move=> x.
Fail rewrite add_leq_right. (* Coq cannot guess what x is *)
Check (add_leq_right x).
rewrite (add_leq_right x). (* uses the partial application of add_leq_right to x *)
Abort.

End AnotherRewrite.

(** *** Unfolding a definition.

  Unfolding a definition is done with [rewrite /the_definition_to_be_unfolded].

*)

Definition secret : nat := 42.

Goal secret = 41 + 1.
Proof.
rewrite /secret.
rewrite -/secret. (* folding back*)
by [].
Qed.

(** *** The [apply:] tactic 

The [apply:] tactic tries to match the conclusion (and eventually some premisses) of the lemma 
with the goal.
It lets one do backward reasoning.
Let's look at some examples.

*)

Goal forall (A B : Prop) (H : A-> B), B.
Proof.
move=> A B H.
apply: H.
Abort.

Goal forall (A B C : Prop) (H : A -> B -> C), B -> C.
Proof.
move=> A B C H.
apply: H. (* the premise B has been included *)
Abort.

(** *** Generalisation

It is usually a valid logical step to strengthen the goal.
This is the case in the logic of Coq. 
In other words, if one can prove more, then one can prove less.
Generalisation is a way to strengthen a statement by introducing one universal quantification.
Generalisation can be an essential step to prepare inductive reasoning, in order to get strong enough
inductive hypotheses (but not too strong, otherwise one gets stuck with unprovable base cases in the inductive reasoning).

*)

Module Generalisation.

From mathcomp Require Import ssrbool ssralg ssrnum.
Local Open Scope ring_scope.

Variable (R : numDomainType).

Goal (4 + 1) ^+ 2 = 4 ^+ 2 + 4 *+ 2 + 1 :> R.
Proof.
move: 4. (* generalises over the term 4 *)
Abort.

Goal 1 + 1 = 1 * 1 :> R.
Proof.
move: 1. (* generalises over all occurrences of 1 *)
Abort.

Goal 1 + 1 = 1 * 1 :> R.
Proof.
move: {2}1. (* generalises the second occurrence of 1 *)
move=> x. 
Abort.

Goal 1 + 1 = 1 * 1 :> R.
Proof.
move: {2 4}1. (* generalises the second and the forth occurrence of 1 *)
move=> x. 
Abort.

Check list.

Goal forall (T : Type) (l : list T) (C : Prop), C.
Proof.
move=> T l C.
(* imagine that we would like to make induction on the lentgh of l - which is a natural number-
not on the list l itself. *)
move: (eq_refl (length l)). (* this illustrates moving something from the global context to top *)
move: {2}(length l). (* generalises over the second occurrence only *)
move=> n.
Abort.

End Generalisation.


(** *** Induction reasoning

  Let's say there is a value [v] of type [T] and there is an induction principle for the type [T].
  Induction reasoning on [v] consists in starting an induction reasoning exploiting this principle.
  Case analysis can be seen as a special case of induction reasoning, 
  driven by the constructors
  and where the induction hypotheses are not used.

  For a given inductive type, there may be several induction principles.
  For instance, there are two induction principles for sequences in Mathematical Component Library.
  Picking the induction principle impacts the proof effort.
  

  Induction principles' names often contain the substring
  "elim" in the Standard Library ("elim" which stands for "elimination") or
  "ind" in the Mathematical Components Library.

  In the following examples, sequences from the Mathematical Components Library are used 
  instead of lists from the standard library. *)

Module Range.

From mathcomp Require Import ssrnat seq.

Fixpoint range (a : nat) (n : nat) := match n with
| 0 => [::]
| m.+1 => a::(range (a.+1) m)
end.

(* The following code is considered bad practise. *)
(* It is presented this way to ease playing it step-by-step *)
(* and identifying basic reasoning steps. *)
Goal forall (a : nat) (n : nat), size (range a n) = n.
Proof.
move=> a n.
move: a.
elim: n. (* starts induction on n *)
- (* base case *)
  move=> n.
  rewrite /=.
  by [].
- (* inductive step *)
  move=> n.
  move=> IH.
  move=> b.
  rewrite /=.
  rewrite IH.
  by [].
Qed.
(* Les preuves n'ont pas d'odeur. *)


(* The previous script can be shortened to: *)

Lemma size_range (a : nat) (n : nat) : size (range a n) = n.
Proof.
move: a; elim: n => // n IHn b /=.
by rewrite IHn.
Qed.

(* The syntax [//] after [=>] in a [move] means: please rmove trivial goal. *)
(* In this example, Coq is able to kill the base case as a trivial goal. *)
(* As a result, only one goal remain after [//] and no pipe symbol is required. *)
(* Simplification and removing trivial goals can be combined with the syntax [//=]. *)

End Range.

Module InductionSequence.

From mathcomp Require Import ssrnat seq.

Variables (l m : seq nat).

Goal size (l++m) = size l + size m.
Proof.
move: m.
elim: l=> // a l IH m /=.
by rewrite IH.
Qed.

Check last_ind.

(* The result [last_ind] is an alternative induction principle *)
(* that can be applied at the elimination step in the previous example. *)
(* Instead of using constructors *)
(* The syntax [elim/last_ind:] combines elimination with view application. *)
(* Starting from the same goal and applying the [last_ind] view: *)

Goal size (l++m) = size l + size m.
Proof.
move: m.
elim/last_ind: l. (* elimination is done with the inductive principle last_ind *)
- by move=> m.
- move=> m a IH l.
  rewrite size_rcons.
  rewrite cat_rcons.  
  rewrite IH.
  rewrite /=.
  by rewrite addnS.
Qed.


End InductionSequence.


(** *** Congruence

  When it is required to prove an equality between two applications of the same function, 
  it suffices to prove that the corresponding arguments of both applications are equal.
  For instance, in the following examples it is required to prove [op w x = op y z].
  This goal has the form of an equality with the same function applied in each member.
  The first arguments are [w] on the left and [y] on the right.
  The second arguments are [x] on the left and [z] on the right.
  It is sufficient to prove that [w = y] and [x = z].

*)

Section Congruence.

Variables (T : Type) (op : T -> T -> T) (w x y z : T).

Goal w = y -> x = z -> op w x = op y z. 
Proof.
move=> eq_wy eq_xz.
congr op.
- exact: eq_wy.
- exact: eq_xz.
Qed.

End Congruence.

(** *** Forward reasoning
  
  From the point of view of proof engineering with Coq, 
  one generally prefers to work on the goal over working on the local context.
  This proof style is used in the Mathematical Components Library and is orthogonal to SSReflect tactics.
  One benefit of this style is to get failure earlier when the script gets broken, 
  and thus it is easier to fix it. Instead of working on the local context 
  (for instance by using [rewrite in] on an hypothesis in the local context)
  it is preferable to work on it while it is still in the goal and before it is introduced to the local context.
  This way, one avoids relying on the names of the introduced assumptions.
  Pushing something to top might be changed without creating an error immediately,
  leading to more difficulties to maintain the script.
  This difficulty can be more apparent when reusing old code or code written by others.

  Still, one may want to use forward reasoning occasionally.
  The main SSReflect forward reasoning tactic is [have:].

*)

Goal False.
Proof.
have : 0 = 0.
- by [].
- move=> H.
Abort.

Goal False.
Proof.
have H : 0 = 0. (* syntax to give a name to the introduced intermediate result *)
- by [].
- 
Abort.

(** *** Changing view
  
  Changing view is performed on the first assumption with the tactic [move/]
  or on the conclusion with the tactic [apply/].
  It replaces it with a "different view".
  The first asumption can be replaced by a weaker asumption 
  and the conclusion can be replaced by a stronger conclusion.

  With reflection results (with the [reflect] keyword) a proposition 
  can be replaced with an equivalent boolean and a boolean 
  can be replaced with an equivalent proposition.
  This is part of the Small Scale Reflection methodology.

  Let's look at some examples.

*)

Module ChangingView.

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

(*
  These examples also work with equivalence instead of implication.
*)

Hypothesis (H' : B <-> C).

Goal B -> D -> E.
Proof.
move/H'. (* weakens B to C *)
Abort.

Goal A -> C.
Proof.
move=> HA.
apply/H'. (* strenghten C to B *)
move: HA.
Abort.

End ChangingView.

(* 
  We now show some examples of view changing with boolean reflection.

*)

Module BooleanReflection.
From mathcomp Require Import ssrbool ssrnat.

Check minn_idPr.

Variables (m n : nat) (P : Prop).

Goal minn m n = n -> P.
Proof.
move/minn_idPr.
Abort.

Goal n <= m-> P.
Proof.
move/minn_idPr.
Abort.

Goal P -> minn m n = n.
Proof.
move=> H.
apply/minn_idPr.
Abort.

Goal P -> n <= m.
Proof.
move=> H.
apply/minn_idPr.
Abort.

End BooleanReflection.

(*
  One can combine changing view with moving things.
*)

(** Rewriting pattern. *)

(** 
  SSReflect offers rewrite patterns to guide Coq to select specific matches for a rewrite.
  Otherwise the first match is selected, which is not necessarly the desired effect.
  Please not that the match and the occurence are two different things.
  A pattern has several matches - eventually none - and each match has one or multiple occurrences.
  Let's look at examples. 
*)

Module RewritePatterns.

From mathcomp Require Import ssrbool ssralg ssrnum.

(* Import GRing.Theory Num.Theory. *)
Local Open Scope ring_scope.

Variables (R : ringType) (a b c : R).
Hypothesis H : forall (x : R), x = c.

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

(* The following examples shows that we can explicit a pattern 
to the point that exactly one b is rewritten, 
the one in the middle in the term a + b + b *)

Goal (a + b) * a + (a + b + a) * b = (b + b) * a + (a + b + b) * a * b.
Proof.
rewrite [X in (_ + _)* _ + (_ + X + _)* _ * _]H.
Abort.

End RewritePatterns.

Module SomeMorePatterns.

(* From HB Require Import structures. *)
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

End SomeMorePatterns.

(** ** 3. More SSReflect tactics
*)

(** *** Case analysis

  Let's say there is a value [v] of type [T] where [T] is an inductive type
  (an inductive type has a finite number of constructors).
  Case analysis on [v] consists in examining how [v] is constructed, 
  which leads to one subgoal for each constructor.

*)

Goal forall (n : nat), n + n = n.
Proof.
move=> n.
case: n.
(* the goals is splitted into two goals *)
- rewrite /=. 
  by [].
- move=> n.
  (* we get stuck here, because we are trying to prove something false *)  
Abort.

(** The previous script can be written more shortly as follows 
*)

Goal forall (n : nat), n + n = n.
Proof.
move=> n.
case: n=> [|n]. (* the pipe symbol '|' separates each subgoal *)
(* the goals is splitted into two goals *)
- by []. 
- (* we get stuck here, because we are trying to prove something false *)  
Abort.

(** It is possible to combine moving (with [move =>]) 
    with simplification [/=] and removing trivial goals [//].
    In the following script, after the case analysis, the first goal is trivial and removed by [//].
    Thus, only one goal is remaining and [n] can be introduced without using the pipe symbol.
*)

Goal forall (n : nat), n + n = n.
Proof.
move=> n.
case: n=> // n. 
(* we get stuck here, because we are trying to prove something false *)  
Abort.

(** *** Specialising 

  Conversely to strengthening the goal, one can always weaken assumptions.
  In other words, if one can do with less then one can do with more.
  One way to weaken an assumption is by specialising it.
  In the following example, the assumption [forall y, P y] is specialised to [x],
  which results in the asumption [P x].

*)

Goal forall (T G : Type) (P : T -> Prop) (x : T), (forall y, P y) -> G.
Proof.
move=> T G P x.
move/(_ x).
Abort.

(*
  The same could have been achieved with partial application.
*)

Goal forall (T G : Type) (P : T -> Prop) (x : T), (forall y, P y) -> G.
Proof.
move=> T G P x H.
move: (H x).
Abort.

(** *** Setting a new definition (vanilla Coq)

We remind here the [pose] tactic (that does not come from SSReflect)
which let one add a local definition to the current context.
It can be useful to see more clearly the goal and the local context.

*)

Goal 1 + 2 = (1 + 2) + (1 + 2).
Proof.
pose a := 1 + 2.
rewrite -/a. (* can see more clearly now *)
Abort.

(** ** 4. Exercices
*)

(** *** Exercice 1
  For this exercice, you may want to use the Coq tactic [split] 
  to break a cunjunction-goal into two goals.
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

(** ** Where to go from here
 
  One may try to port one proof script from vanilla Coq to SSReflect and see the difference.
  In addition to using SSReflect tactics, 
  one may start reusing some results from the Mathematical Components Library. 

  Finally, one may get inspiration from the Mathematical Component Library for their own formalisation.
  This includes Small Scale Reflection methodology and SSReflect coding conventions. 
  Some ingredients are boolean reflection, decidable structures 
  and hierarchy of structures (with Hierarchy Builder).

*)
