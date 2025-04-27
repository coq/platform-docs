(** * Tutorial: Hierarchy Builder
  *** Main contributors

    - Quentin Vermande

  *** Summary

  In this tutorial, we discuss Hierarchy Builder, a plugin providing high-level
  commands to declare a hierarchy of structures (or interfaces).

  *** Table of contents

      - 1. Mixins and structures
      - 2. Instances
      - 3. Factories and builders
      - 4. Options, parameters, visibility of instances
      - 5. Non-forgetful inheritance

  *** Prerequisites

    Needed:
    - TODO

    Not Needed:
    - TODO

    Installation:
    - See the [official installation instructions](https://github.com/math-comp/hierarchy-builder?tab=readme-ov-file#installation--availability)

*)

From HB Require Import structures.
From Coq Require Import PeanoNat.

(** ** 1. Mixins and structures

  By structure, we mean an object (which we call structure) equipped with some
  data (usually operations) and properties. The basic building bloc of a
  structure is the mixin, which is a record that regroups an "interesting" part
  of the content of a structure. We declare a record as a mixin by prefixing the
  definition of the record with the [HB.mixin] command.
*)

HB.mixin Record hasOp (T : Type) := {op : T -> T -> T}.

(** To get information about anything HB knows about, we can use the [HB.about]
  command.
 *)

HB.about hasOp.

(** This tells us that [hasOp] is a factory (more on that later) which contains
  one field named [op], which has no dependency and which can be used to
  obtain an [hasOp] mixin (obviously).
*)

(** Now that we have a mixin, let us build a structure out of it. We describe a
  structure using a sigma type by giving a name to the subject and then all the
  mixins it is equipped with. We use the [{X of mixin_1 X & ... & mixin_k X}]
  notation and prefix the definition with the [HB.structure] command.
*)

HB.structure Definition Magma := {T of hasOp T & hasOp T}.

(** We see that HB declares a lot of things. The ones we are interested in
  are [type] and [sort]. But let us first see what [HB.about] has to say.
*)

HB.about Magma.

(** [HB.about] claims that [Magma.type] is a structure. This means that
  [Magma.type] is a type whose inhabitants are the instances of the [Magma]
  structure. We also learn that any [Magma.type] has an [op] operation, that
  there is a [Magma] factory (those again) and that the inheritance graph is
  empty (as far as [Magma] is concerned).
*)

(** Now, let us be curious and look at what [type] is. *)

Print Magma.type.

(** We see that [type] is a record with fields [sort] and [class]. [sort] is
  the subject of the structure and [class] hides all the mixins we used to
  define the structure. For instance, when we will declare an instance
  of [Magma] for [nat], say [N : Magma.type], then [Magma.sort N] will be [nat].
*)

(** Now, what about that [op] operation? *)

About op.

(** Given [s : Magma.type], [op] is indeed an operation on the underlying
  [Magma.sort s] type.
*)

(** The point of mixins is that they can be reused in several structures. In
  this sense, a structure can be thought of as a set of mixins on a common
  subject. Let us define a structure of semigroup. A semigroup is a type with
  an associative operation. We already have a mixin for the operation, let us
  add a mixin for the associativity property. We will need for the underlying
  set to already be equipped with a [hasOp] mixin, but the subject has to be
  the same as the one of the [hasOp] mixin, so we declare the dependencies with
  the syntax [Record newMixin X of mixin_1 X & ... & mixin_k X := ...].
*)

HB.mixin Record isAssoc T of hasOp T := {
  opA : forall x y z : T, op x (op y z) = op (op x y) z
}.

HB.about isAssoc.

(** The only noticeable difference with [HB.about hasOp] is that now, HB teels
  us about the dependency between [hasOp] and [isAssoc].
*)

HB.structure Definition Semigroup := {T of hasOp T & isAssoc T}.

HB.about Semigroup.

(** Now, the inheritance graph is not empty, since [Semigroup] inherits from
  [Magma], meaning that any semigroup is a magma. This materializes as a
  coercion from [Semigroup.type] to [Magma.type]. Besides, [HB.about] only shows
  [opA], as the operation [op] is already in the [Magma] structure.
*)

Check fun (T : Semigroup.type) => T : Magma.type.

(** ** 2. Instances *)

(** Let us now build actual magmas. The important thing to know here is that
  when Coq/Rocq will try to elaborate a magma out of any given type, it will
  only look at the "head" of the subject, which we call its key. For instance,
  if the subject is [nat], then the key is [nat]. If the subject is
  [prod nat bool], then the key is [prod]. This means that we should not declare
  two instances of the same structure on the same key. For instance, we should
  not declare an instance of [Magma] on [prod nat nat] and on [prod bool bool].
  Now, in order to know what to do to declare an instance on a given key, we can
  use the [HB.howto] command.
*)

HB.howto nat Magma.type.

(** This command tells us that we should use the hasOp mixin and invites us to
  look at the output of [HB.about hasOp.Build]. *)

HB.about hasOp.Build.

(** This tells us that [hasOp.Build] is a constructor with no requirement which
  builds the [hasOp] mixin. It also shows that the constructor has two
  arguments, namely the subject and the operation. Now, to get our instance of
  [Magma.type] on [nat], we define an instance of [hasOp] using its constructor
  and prefix this definition with the [HB.instance] command.
*)

HB.instance Definition _ := hasOp.Build nat Nat.add.

(** We usually do not give a name to the term we just built for two reasons.
  First, it is a mixin, not the structure, and second, the structure can be
  recovered as follows.
*)

Check nat : Magma.type.

(** This also means that when we want to use a lemma about magmas on [nat], we
  can give the subject [nat] and Coq/Rocq will automatically replace it with
  the corresponding instance. For example, we can write
*)

Check eq_refl : op 1 1 = 2.

(** and Coq/Rocq automatically applied the operation from the instance of magma
  on [nat] that we just declared to [1] and [1].
*)

(** But wait, what if we also wanted to have the instance where the operation
  is the multiplication? Since we can only have one instance of magma on the
  key [nat], we need to change the key. The solution is to use an alias of
  [nat], that is to say a definition that unfolds to [nat].
*)

Definition nat_mul := nat.
HB.instance Definition _ := hasOp.Build nat_mul Nat.mul.
Check eq_refl : @op nat_mul 1 1 = 1.

(** Now, what about semigroups? *)

HB.howto nat Semigroup.type.

(** In order to build a semigroup, we need to instantiate the [hasOp] and
  [isAssoc] mixins. Since we already have an instance for [hasOp], let us do the
  other one.
*)

HB.about isAssoc.Build.
HB.instance Definition _ := isAssoc.Build nat Nat.add_assoc.

Goal forall n, 1 + (1 + n) = 2 + n.
Proof.
intro n.
rewrite (@opA nat).
reflexivity.
Qed.

(** ** 3. Factories and builders *)

(** There may be several ways to describe the same structure. For example, when
  dealing with orders, giving either of the large operator and the strict
  operator are enough to describe the order. We pick one of those
  representations as the canonical one, which drives the definition of mixins
  and we declare the others as factories. A factory is, just like mixins, a
  record containing operations and properties about a given subject. In this
  sense, a mixin is a factory. Let us see a very silly example. *)

HB.factory Record isSemigroup T := {
  op : T -> T -> T;
  opA : forall x y z, op x (op y z) = op (op x y) z
}.

HB.about isSemigroup.

(** As of now, the [isSemigroup] factory is not interesting since we can not do
  anything with it. We need to tell Coq/Rocq how to transform an instance of
  [isSemigroup] into instances of [hasOp] and [isAssoc]. We do this using what
  we call builders. We start a section of code declaring builders using the
  [HB.builders] command. It expects a context containing a subject and the
  factory we start from.
*)

HB.builders Context T of isSemigroup T.

(** We can now build any object and prove any lemmas that we may need. For us
  now, there is nothing to do so we immediately declare the instances.
*)

HB.instance Definition _ := hasOp.Build T op.
HB.instance Definition _ := isAssoc.Build T opA.

(** We close the section using the [HB.end] command.
*)
HB.end.

HB.about isSemigroup.

(** Now, HB registered that [isSemigroup] can be used to build both [hasOp] and
  [isAssoc].
*)

HB.howto nat Semigroup.type.

(** Indeed, we now have 2 options to build an instance of semigroup. We can
  either instantiate the [hasOp] and [isAssoc] mixins separately, or we can
  instantiate the [isSemigroup] factory.
*)

Definition nat_add := nat.
HB.instance Definition _ := isSemigroup.Build nat_add Nat.add Nat.add_assoc.

(** Factories can also be used to specify structures. In the definition of a
  structure, factories stand for all the mixins they can build. Let us see that
  in action with commutative semigroups.
*)

HB.mixin Record isComm T of hasOp T := {
  opC : forall x y : T, op x y = op y x
}.

HB.structure Definition ComSemigroup := {T of isSemigroup T & isComm T}.

(** Remember that [HB.about Magma] said that [Magma] is a factory. With a bit
  of generalization, this means we can also write
  HB.structure Definition ComSemigroup' := {T of Semigroup T & isComm T}.
  Right now, this command would fail because HB does not accept several
  structures with the same mixins.
*)

(** 4. Options, scope *)

(** HB lets us customize a few things. First, we can give a short name for a
  structure with the [short] attribute.
*)

HB.mixin Record hasPoint T := {pt : T}.
#[short(type="ptType")]
HB.structure Definition Pointed := {T of hasPoint T}.

(** We can ask for HB to use primitive records with the [primitive] attribute.
  This is only visible when the structure has parameters, let us try with magma
  morphisms. This will be the occasion to see what happens when we have 
  parameters.
*)

HB.mixin Record isMagmaMorphism (T U : Magma.type) (f : T -> U) := {
  op_morph : forall x y, f (op x y) = op (f x) (f y)
}.

#[primitive]
HB.structure Definition MagmaMorphism (T U : Magma.type) :=
  {f of isMagmaMorphism T U f}.

Set Printing Coercions.
Check fun (T : Magma.type) (f : MagmaMorphism.type T T) =>
  MagmaMorphism.sort T T f.
Unset Printing Coercions.

(** Now, let us talk about the visibility of instances. An instance is visible
  only when it is declared in the current module.
*)

Definition idfun (T : Type) (x : T) := x.
Lemma idfun_op_morph (T : Magma.type) (x y : T) :
  idfun T (op x y) = op (idfun T x) (idfun T y).
Proof. reflexivity. Qed.

Module A.
HB.instance Definition _ (T : Magma.type) :=
  isMagmaMorphism.Build T T (idfun T) (idfun_op_morph T).
End A.

(** The instance of magma morphism on [idfun] is hidden in module [A], so
  Coq/Rocq will not use it.
*)

Fail Check idfun nat : MagmaMorphism.type nat nat.

(** When we import [A], its content becomes visible to the current scope.
*)

Import A.
Check idfun nat : MagmaMorphism.type nat nat.

(** It is common to declare instances inside modules but want for them to be
  seen outside of it. There is the [export] attribute that marks an instance as
  needing to be exported. Then, the [HB.reexport] commands redefines these
  tagged instances at the point where it is called.
*)

Definition idfun' (T : Type) (x : T) := x.
Module B.
Definition hidden := 0.
#[export]
HB.instance Definition _ (T : Magma.type) :=
  isMagmaMorphism.Build T T (idfun' T) (idfun_op_morph T).
Module Exports. HB.reexport. End Exports.
End B.
Import B.Exports.

Check idfun' nat : MagmaMorphism.type nat nat. (* The instance has been imported. *)
Fail Check hidden. (* [hidden] has not been imported. *)
Check B.hidden.

(** 5. Non-forgetful inheritance *)

(** Non-forgetful inheritance is a common issue we encounter when building
  hierarchies of structures. This issue arises when there are several
  incompatible ways to build a structure on the same subject, usually using
  coercions from the inheritance graph. Coq/Rocq takes one of them, but the user
  may implicitly expecting another. These causes errors that are hard to debug
  because they involve things that do not appear on screen.
*)

HB.mixin Record hasSq T := {
  sq : T -> T;
}.
HB.structure Definition Sq := {T of hasSq T}.

Definition option_op {T : Magma.type} (o1 o2 : option T) : option T :=
  match o1, o2 with
  | Some n, Some m => Some (op n m)
  | _, _ => None
  end.
HB.instance Definition _ (T : Magma.type) := hasOp.Build (option T) option_op.

Definition option_square {T : Sq.type} (o : option T) : option T :=
  match o with
  | Some n => Some (sq n)
  | None => None
  end.
HB.instance Definition _ (T : Sq.type) := hasSq.Build (option T) option_square.

HB.instance Definition _ (T : Magma.type) := hasSq.Build T (fun x => op x x).

Lemma problem (W : Magma.type) (w : option W) : sq w = op w w.
Proof.
Fail reflexivity.

(** The issue here is that the structure of [Sq] used in [sq w] is the one for
  the [option] key, not the one on the [Magma.sort] key, so [sq w] is actually
  [option_square w], not [op w w].
*)

destruct w; reflexivity.
Qed.

(** In this case, both instances are extensionally the same so we can still
  conclude, but the could very well have not been.
*)

(** The standard solution to this is to make one structure depend on the other.
*)

HB.mixin Record hasSq' T of hasOp T := {
  sq' : T -> T;
  sq'_op : forall x, sq' x = op x x
}.
