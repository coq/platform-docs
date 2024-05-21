(** * Require, Import and Export tutorial

    *** Summary

    This tutorial is about how to get the most out of library files, that is
    Coq files containing definitions, lemmas, notations, etc and simple modules.
    These topics are often skipped from lectures or courses about Coq
    because they are mostly technical and somewhat boring. However, any Coq
    user needs to learn (usually the hard way) this content before writing their
    own libraries.

    In Coq, library files are modules, and modules provide, among other things,
    namespace facilities as well as some form of locality. Understanding what to
    expect when one [Import]s or [Export]s modules is important, even when not
    relying on modules and module types.

    *** Table of content

    - 1. Library files
    - 2. Simple modules
    - 3. Name clashes and disambiguation
    - 4. Other content types in Modules
    - 5. Selective import
    - 6. Locality attributes

    *** Prerequisites

    Needed:
    - The user should already have some basic Coq experience: writing
      definitions, lemmas, proofs...
    - Some parts deal with more advanced Coq content (user-defined tactics,
      notations, coercions...); having some basic knowledge about it is better
      to appreciate what Coq can offer, but is not really needed.

    Installation:
    This tutorial should work for Coq V8.17 or later.
*)

(** ** 1. Library files *)

(** Coq's basic compilation unit is the _library file_. Each compiled file can
    be [Require]d in order to make its logical and computational content
    available in the current file.

    If not stated otherwise (with the [-no-init] command-line flag), Coq's
    initial state is populated by a dozen library files called the [Prelude].

    We can see these files with the [Print Libraries] command: *)
Print Libraries.

(** As we can see, these files share a common logical prefix made of:
    - [Coq]: the library prefix used by the standard library
    - [Init]: the directory where these library files are located

    Let's require another small library file. *)
From Coq.Bool Require Bool.

(** The last command told [Coq] to load all logical and computational content
    in the file [Bool.vo] contained in the directory [Bool] of the root
    directory of Coq's standard library.

    Let us mention other possibilities, we could have written:
    [From Coq Require Bool.Bool.]
    or, since there is no confusion (there is only one file named [Bool.vo] in
    Coq's standard library):
    [From Coq Require Bool.]

    We can also drop the [From] part and [Require Coq.Bool.Bool].
*)

(** Now let's see how our list of libraries has evolved: *)
Print Libraries.

(** As we can see, we have not one but two more library files.
    The [Coq.Classes.DecidableClass] is itself required in [Coq.Bool.Bool].

    Now there are two very important message here:
    1. When we [Require] a file, we [Require] transitively any file it has
       [Require]d (and any file [Require]d in the [Require]d files, and so on).
    2. There is **no way** to "unrequire" anything. Once a file has been
       required, its content will remain in the global environment of the user
       for ever, possibly polluting [Search] output.

    As a consequence, one should be very careful of what one [Require]s. *)

(** Now that we have required [Coq.Bool.Bool], we have many more lemmas about
    boolean operations. *)
Search andb true.

(** Some of them are _qualified_ with the [Bool.] prefix, these come from
    [Coq.Bool.Bool]. Others have short names, these come from one of the
    [Coq.Init] files.

    Using the [About] command gives us their locations. *)
About andb_prop.

(** Now let's take a look at [Bool.andb_true_l] *)
About Bool.andb_true_l.

(** We see that it expands to [Coq.Bool.Bool.andb_true_l]. This is the internal
    name Coq uses to distinguish it from any other constant.
    We call it an _absolutely qualified identifier_ or _fully qualified
    identifier_.

    This is a technical but important notion, so we should take some time to
    describe this identifer. There are several parts separated by dots.
    - The first part is Coq: it is the _logical name_ of the library. Other
      mechanisms (for instance a [_CoqProject] file, or [-R] and [-Q] options
      for [coqc], location which are known by [coqc], such as
      the output of [coqc -where], ...) associate a logical name to a physical
      directory containing the library files.
    - The second and third part correspond to the path of the file (relative to
      the root of the library) containing the identifier in the given library,
      in our case, on a Unix family system, it corresponds to [Bool/Bool.vo].

    Now, at this point, there really is only one [Bool] library file containing
    an constant named [andb_true_l], so Coq accepts (and prints) as
    unambiguously _partially qualified_ the identifier [Bool.andb_true_l].

    Another unambiguous partially qualified identifier for the same constant is
    [Bool.Bool.andb_true_l].

    All these identifiers refer to the same constant: *)
About Coq.Bool.Bool.andb_true_l.
About Bool.Bool.andb_true_l.
About Bool.andb_true_l.

(** Now, would the unqualified [andb_true_l] be ambiguous? *)
Search "andb_true_l".

(** The answer is no. However, Coq does not accept it as an identifier: *)
Fail Check andb_true_l.

(** The [Locate] command shows all constants associated to an unqualified
    identifier and how to refer to it in the shortest way possible. *)
Locate andb_true_l.

(** If we want to use such a _short name_, we need to [Import] the [Bool]
    module (yes, we said module here and not library file, more about this
    later). *)
Import Bool.
Check andb_true_l.

(** We have used the unambiguous [Bool] name for the [Import] command, but we
    could as well have written [Import Coq.Bool.Bool] or [Import Coq.Bool]
    for the same reasons as before.

    Most users prefer short names to fully qualified names so, in practice, one
    usually [Require]s and [Import]s a file at the same time.
    This is done with the syntax: [From Coq.Bool Require Import Bool] or any
    of the other possibilities described above when we [Require]d the [Bool]
    library file. *)

(** ** 2. Simple modules *)

(** We will use modules here mostly because they will help us understand how
    to get what we want from library files (and reject, if possible, what we
    don't want). *)

(** For now let us consider a very simple module: *)
Module Foo.
  Definition foo := 42.
  Lemma bar : 21 * 2 = foo.
  Proof. reflexivity. Qed.
  Lemma baz : 21 + 21 = foo.
  Proof. reflexivity. Qed.
End Foo.

(** Such a module, written down explicitly with [End module_name] at the end
    is called an _interactive module_.
    Our module [Foo] has 1 definition and 2 lemmas. It's printed out in the
    following way: *)
Print Module Foo.

(** Notice that, surprisingly, the too lemmas are printed as [Parameter]s, but
    they really are actual lemmas.

    We can access the content of the module with the dot syntax. *)
Print Foo.foo.
Check Foo.bar.
Check Foo.baz.

(** [Foo.bar] and [Foo.baz] are not [Parameters] or [Axioms]: *)
Print Assumptions Foo.bar.
Print Assumptions Foo.baz.

(** But we cannot yet access them with short names: *)
Fail Check bar.
Locate bar.

(** The content of the module [Foo] can be used just like any other definitions
    and lemmas *)
Lemma forty : Foo.foo - 2 = 40.
Proof.
  unfold Foo.foo.
  fold Foo.foo.
  rewrite <-Foo.bar.
  reflexivity.
Qed.

(** This dot syntax is reminiscent of what we used for library files, and it is
    no accident. In fact,

    __library files are modules.__

    This is the most important fact to take home from this tutorial, and the
    main reason to study a part of Coq's module system.

    We can even print the content of library files, viewed as modules: *)
Print Module Coq.Bool.Bool.

(** [Import] is actually a module command, so we can: *)
Import Foo.

(** Now that [Foo] is [Import]ed, we can access its content with short names: *)
Check bar.

(** To sum up without subtlety what we have learned so far:
    - We _[Require] library files_ to load their content.
    - We _[Import] modules_ to use short names for their content (among other
      things we will see shortly)
    - _Library files are modules._ *)

(** ** 3. Name clashes and disambiguation *)

(** When we [Import]ed our [Foo] module before, there was no possible name
    clash since no constant in our context were named [foo], [bar] or [baz].

    In real life Coq, however, global contexts can be huge and there will
    be name clashes.

    So, what happens if we define and import the following module? *)
Module OtherFoo.
  Definition foo := true.
End OtherFoo.

Import OtherFoo.
(** First, Coq emits no error or warning, so this is a legit operation.
    What is [foo] now? *)
Print foo.
About foo.

(** Our [OtherFoo.foo] identifier has actually [shadowed] [Foo.foo].

    To identify it, we now need to use a more qualified name. *)
Print Foo.foo.
About Foo.foo.

(** The [Locate] command shows the _stack_ of identifiers whose unqualified name
    is the given argument: *)
Locate foo.

(** On top of it (first) is our [OtherFoo.foo] constant, it is available by its
    short name. Next is [Foo.foo] and Coq gives us the shortest partially
    qualified name to refer to it.

    What happens if we now [Import Foo] again? *)
Import Foo.
Print foo.
About foo.
Locate foo.

(** We have changed again to which constant refers the short name [foo]!
    Our [Foo.foo] constant is on top of the stack of [foo] constants.
    This changing short name resolution may look innocuous but it has a very
    nasty consequence:

    _The order of the [Import] commands matters, changing it can break things._
*)

(** Notice that one can always use more qualified names, so that the resulting
    code is independent of the [Import] orders: *)
Print Foo.foo.
Print OtherFoo.foo.

(** Now, for a real life example, let us consider the library files
    [Coq.Arith.PeanoNat] and [Coq.ZArith.BinInt] which contain the bulk
    of Coq's standard library content for, respectively Peano natural numbers
    and (binary) integers. *)

From Coq Require Import Arith.PeanoNat ZArith.BinInt.

(** Most of the results and operations are actually contained in the
    interactive modules [PeanoNat.Nat] and [BinInt.Z]: *)
Check Nat.add_0_r.
Check Z.add_0_r.

(** Notice that the name [add_0_r] is used both for natural numbers and for
    integers, which seems right.
    
    At this point, [add_0_r] does not refer to anything. *)
Fail Check add_0_r.
Locate add_0_r.

(** We may choose to [Import Nat] if, for instance, our current development
    deals more with natural numbers than integers. *)
Import Nat.
Check add_0_r.
About add_0_r.

(** We could even [Import] both modules, but then beware that the order is
    important. *)
Import Z.
Check add_0_r.
About add_0_r.

(** Another common choice is to [Import] neither of them and use the [Nat.] and
    [Z.] prefixes as namespaces. This is a bit more verbose, but it is also
    easier to read. *)

(** What happens if module names themselves clash?
    We actually are already in that case: *)
About Nat.
About Coq.Init.Nat.

(** We have one module named [Nat] in [PeanoNat] and another one in the [Init]
    prelude. The [Coq.Init.Nat] module was shadowed when we [Import]ed
    the module [Coq.Arith.PeanoNat].

    As we have just seen, it suffices to qualify more the module which is
    shadowed.

    To conclude this part, let us sum up what Coq allows and disallows regarding
    identifiers:
    - it is possible to have two files with the same name as long as they are
      in different directories;
    - it is possible to have two (non-file) modules with the same name as long
      as they are in different modules (which can be library files);
    - it is possible to have two constants with the same name as long as they
      are in different modules (including library files) *)

(** ** 4. Other content types in Modules *)

(** Our module [Foo] contained only definitions and lemmas.
    In practice there are many more content types in a module:
    - parameters and axioms
    - tactics
    - notations, abbreviations, [Ltac] notations and [Ltac2] notations
    - hints
    - coercions
    - canonical structures

    It is not an issue if some (or all) these categories are obscure to you.
    We are only interested in what persists outside the module and in which
    case. We will only experiment with some of these categories.
*)

Module Bar.
  Parameter (secret : nat).
  Axiom secret_is_42 : secret = 42.
  Ltac find_secret := rewrite secret_is_42.
  Tactic Notation "fs" := find_secret.
  Infix "+p" := Nat.add (only parsing, at level 30, right associativity) : nat_scope.
  Lemma secret_42 : secret = 42.
  Proof. find_secret. reflexivity. Qed.
  Lemma baz : 21 +p 21 = secret.
  Proof. fs. reflexivity. Qed.
End Bar.

(** We have not imported [Bar] yet. What do we have? *)
About Bar.secret.
About Bar.secret_is_42.
Print Assumptions Bar.secret_is_42.
About Bar.secret_42.
Print Assumptions Bar.secret_42.
About Bar.baz.
Print Assumptions Bar.baz.

(** We see that parameters and axioms are available, and axioms are treated as
    such after the end of the module.

    What about the other content? *)
Fail Check (21 +p 21).
Lemma forty_two : Bar.secret = 42.
Proof.
  Fail fs.
  Fail Bar.fs.
  Bar.find_secret.
  reflexivity.
Qed.

(** As we can see, only the _tactic_ `find_secret` was available.
    Now let's [Import Bar]: *)
Import Bar.
Check (21 +p 21).
Lemma forty_two' : secret = 42.
Proof.
  fs.
  reflexivity.
Qed.

(** To sum things up:
    - parameters, definitions, lemmas, axioms, etc and tactics contained in a
      module are available even if we do not [Import] a module, with a
      qualified name;
    - notations, [Ltac] notations, [Ltac2] notations need the module to be
      imported to be available;
    - the same holds for coercions, hints, abbreviations and canonical
      structures (we omit the experiments for brevity). *)

(** ** 5. Selective import *)

(** Now is a good time to present a recent (8.17) addition: selective import of
    modules. Recall that importing a module has basically two effects:
    - make the short names of constants (lemmas, definitions, ...) and tactics
      available
    - enable the other content: notations, tactic notations, hints, coercions
      and canonical

    Selective import lets us precisely choose what we want to import. *)

Module Baz.
  Definition b := 42.
  Definition almost_b := 41.
  Definition almost_almost_b := 40.
  Notation "x !!" := (x * 42) (at level 2) : nat_scope.
  Coercion to_nat := fun (x : Z) => 42.
End Baz.

(** Let us import our notations first: *)
Import (notations) Baz.
Compute 10 !!.

(** Everything else has not been imported. *)
Fail Check pi.
Fail Check almost_pi.
Fail Compute (0%Z + 3).

(** Let us now import our coercions: *)
Import (coercions) Baz.
Compute (0%Z + 3).

(** Our notation is still there: *)
Compute 1 !!.

(** In fact, it is important to understand that there is no way to "un-import"
    anything in the same module. Once a module feature has been activated, it
    remains so until the end of the current section or module (or file), the
    only exception being shadowed short names. *)

(** We can also select which constants are available by their short names: *)
Import Baz(almost_b, almost_almost_b).
Check almost_b.
Check almost_almost_b.
Fail Check b.

(** We call the [coercions] and [notations] seen before _import categories_.
    The other import categories correspond to what we mentioned before, namely:
    [hints], [canonicals], [ltac.notations] and [ltac2.notations].

    It is possible to select more than one import category with: *)
Import (hints, canonicals) Baz.

(** Now there is also a way to tell Coq: Import everything except these
    categories. We just need to prepend them with a minus sign: *)

Module OtherBaz.
  Definition other_b := 42.
  Definition almost_other_b := 41.
  Definition almost_almost_other_b := 40.
  Notation "x ??" := (x * 42) (at level 2) : nat_scope.
  Coercion to_nat := fun (x : bool) => 42.
End OtherBaz.

Import -(coercions) OtherBaz.
Check almost_other_b.
Compute 10 ??.
Fail Check (true + 3).

(** Notice that, when we import everything except some categories, it is not
    possible, at the time of writing, to choose which identifiers are imported
    to be available as short names: they all are. *)

(** To end this section, we turn to abbreviations and inductive types. *)

Module Unary.
  Inductive UnaryPos := one | successor (n : UnaryPos).
  Inductive UnaryZ := zero | plus (n : UnaryPos) | minus (n : UnaryPos).
  Notation succ := successor.
End Unary.

(** We have not imported anything yet.
    Our inductive types and their constructors are available with their
    qualified names: *)
Check Unary.UnaryPos.
Check Unary.one.
Check Unary.UnaryZ.
Check Unary.minus.

(** Si are our automatically generated induction principles (ending with
    [_sind], [_ind], [_rec] or [_rect]): *)
Check Unary.UnaryPos_rec.
Check Unary.UnaryZ_ind.

(** Our [succ] abbreviation is also available: *)
Check Unary.succ.

(** We can selectively [Import] all these constants and abbreviations.

    For an inductive type and its constructors, it suffices to give the type
    in the constants parenthesized list to be able to use its short name *)
Import Unary(UnaryPos).
Print UnaryPos.

(** However, its constructors and induction principles are not imported: *)
Check one. (* still shadowed by Z.one *)
Fail Check UnaryPos_rec.

(** It is possible to [Import] them manually: *)
Import Unary(one, UnaryPos_rec).
Check one.
Check UnaryPos_rec.

(** But there is a shortcut: using [UnaryPos(..)] imports at once the type, as
    well as its constructors and induction principles: *)
Import Unary(UnaryPos(..)).
Check successor.
Check UnaryPos_ind.

(** The following command enables all short names associated to the inductive
    type [UnaryZ]: *)
Import Unary(UnaryZ(..)).
Check UnaryZ.
Check plus.
Check UnaryZ_ind.

(** The [succ] abbreviation itself can also be selected: *)
Import Unary(succ).
Check succ.

(** Exporting a module *)

(** Contrarily to [Require]d library files, module imports are not transitive.
    Consider the following nested module: *)
Module A.
  Definition this_is_a := 0.
  Module B.
    Definition this_is_b := 42.
  End B.
  Fail Check this_is_b.
  Import B.
  Check this_is_b.
End A.

(** This situation may seem contrived, but imagine rather a library file, say
    A.v which [Require]s and [Imports] another library file, say B.v.
    At this point, we are in a situation similar to being in yet another file
    C.v which has [Require]d the file A.v (but not yet [Import]ed it). *)

(** We can access the content of [A] with qualified names. *)
Print A.this_is_a.
Print Module A.B.
Fail Print Module B.
Print A.B.this_is_b.
Fail Check A.this_is_b.
Fail Check this_is_b.

(** If we [Import A], we get short names for its content. *)
Import A.
Print this_is_a.
Print Module B.

(** But, even though [B] is [Import]ed in [A], we cannot use a short name
    for [this_is_b]: *)
Fail Print this_is_b.
Print B.this_is_b.

(** This behaviour is actually very sane. Some programmers may have [Import]ed
    modules in library files for convenience, this should not affect every
    users of their library.

    Still, there is a way (and sometimes good reason) to mark some inner modules
    for importation whenever the current module is [Import]ed: we use the
    [Export] command: *)
Module A'.
  Definition this_is_a' := 0.
  Module B'.
    Definition this_is_b' := 42.
  End B'.
  Fail Check this_is_b'.
  Export B'.
  Check this_is_b'.
End A'.

Fail Check this_is_b'.
Import A'.
Check this_is_b'.

(** As this gives less control to the final user, [Export]ing modules should not
    be done lightly.

    A common usage is to write a library split in small library files and a
    summary file [Export]ing all of them, so that requiring and importing it
    makes all the library content available at once.

    Another use case is when [Import]ing a module (say about real numbers)
    would only really make sense when another one (say about integers) is also
    imported. *)

(** ** 6. Locality attributes *)

(** If you're not yet bored to death, let's end this tutorial with a last tool
    to give control over what should remain local (if not hidden) and what
    should be exposed in a module (which can be a library file).

    Locality attributes change the visibility of content outside a section or
    a module. We're only interested in modules in this tutorial.

    Contrarily to selective import, which gives some amount of control on
    what is [Import]ed to the user of a module, locality attributes lets the
    writer of a module control what should be imported or not.

    There are 3 locality attributes, one of which should never be used:
    [#[local]], [#[export]] and the evil [[#global]]: *)

(** We experiment with our useless module [Baz]: *)

Module YetAnotherBaz.
  #[local] Definition yet_another_b := 42.
  Definition almost_yet_another_b := 41.
  #[local] Definition almost_almost_yet_another_b := 40.
  #[local] Notation "x %%" := (x * 42) (at level 2) : nat_scope.
  #[local] Coercion to_nat := fun (x : Prop) => 42.
  Compute 3 %%.
  Compute (True + 2).
End YetAnotherBaz.

Import YetAnotherBaz.
Fail Check yet_another_b.
Check YetAnotherBaz.yet_another_b.
Check almost_yet_another_b.
Fail Compute (True + 2).
(** The notation "x %%" is also unavailable, but we cannot show it without
    stopping compilation, as it is not even parsed.
    You can try it by uncommenting: *)
(** Compute 3 %%. *)

(** As we see, using the [#[local]] attribute prevents to import some content
    of a module, which means, for constants, to make them only available with
    qualified names and for other categories (hints, coercions, etc), to
    disable them outside the module.

    This should be used without restraint on anything which should not be part
    of the user's interface, e.g. convenience ad-hoc tactics or unstable
    implementation details. *)

(** The [#[export]] attribute has less uses within modules.
    Its only use is to allow some settings to be available when a module is
    imported. *)

Module SetNotExported.
  Set Printing Parentheses.
  Check (3 + 2 + 5).
End SetNotExported.

Import SetNotExported.
(** The option "Printing Parentheses" is not set outside the module. *)
Check (3 + 2 + 5).

Module SetExported.
  #[export] Set Printing Parentheses.
  Check (3 + 2 + 5).
End SetExported.

Check (3 + 2 + 5).
Import SetExported.
Check (3 + 2 + 5).

(** Now, for the [#[global]] evil setting. *)

(** Let us restore the state of the [Printing Parentheses] option: *)
Unset Printing Parentheses.
Check (3 + 2 + 5).

Module SetGlobalExported.
  #[global] Set Printing Parentheses.
  Check (3 + 2 + 5).
End SetGlobalExported.

Check (3 + 2 + 5).
(** We didn't even imported the module, and the setting is already there!
    As the reference manual says:
    We strongly discourage using the global locality attribute because the
    transitive nature of file loading gives the user little control. *)
