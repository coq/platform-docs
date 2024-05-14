(** * Search tutorial for Coq
    
    *** Summary

	This tutorial is about the powerful [Search] vernacular command in Coq.
	The [Search] command prints names and types of constants in the local or
	global context satisfying a number of criteria.
    
    *** Table of content
	
	- 1. Searching for lemmas
	  - 1.1 Basic [Search] by name and type
	  - 1.2 Searching using metavariables
	  - 1.3 Filtering on hypotheses (parameters) or conclusions (return type)
        - 2. Advanced [Search] options
	  - 2.1 Disambiguating strings in [Search] queries
	  - 2.2 Filtering results by logical kind and disjunctions of criteria
	  - 2.3 Searching inside or outside a specific module

    *** Prerequisites

    Needed:
    - For the first part, it suffices to have some basic experience of Coq: the
      user should know intuitively what is a Coq function and a Coq lemma or
      theorem. Scope notations are mentioned briefly but this should not be too
      much of an issue.
    - For the 2.3 part, some basic experience of Coq modules should be enough.

    Installation:
    This [Search] tutorial should work for Coq V8.14 or later.
*)

(** In this tutorial, we are going to search for lemmas, mostly about natural
    numbers.

    We already have all lemmas and definitions from the prelude ([Coq.Init]),
    and we require the library file [Coq.Arith.PeanoNat] which adds hundreds
    of new constants.
*)

From Coq Require Import PeanoNat.

(** ** 1. Searching for lemmas *)

(** *** 1.1 Basic [Search] by name and type *)

(** In its most basic form, one searches for lemmas or definitions containing
   - a given constant, eg [Nat.add], or [nat]
   - a given string to be part of the identifier
   - a given notation
*)

(** Search all lemmas or operations where the type [nat] occurs: *)
Search nat.

(** Search all lemmas or operations where [Nat.add] occurs: *)
Search Nat.add.

(** Search all lemmas or operations whose name contains "add": *)
Search "add".

(** Search all lemmas or operations where, in the current scope, (_ * _) appears: *)
Search (_ * _).

(** Notice the wildcards [_] around the operator. We call [(_ * _)] a [Search]
    pattern. We will see soon how to write more sophisticated such patterns.
    Similarly, we can search about a unary prefix operator, such as [~]
    (the negation), with: *)
Search (~ _).

(** As an alternative, we can also use a string (more on this later) to search
    for lemmas about multiplication: *)
Search "*".

(** Now our previous searches were too vague to be very useful. One usually
    combines search items in order to be more precise. *)

(** Search all lemmas where the type [nat] and the operators (_ * _) and
   (_ + _) occur. *)
Search nat (_ + _) (_ * _). (* still too much *)

(** Since our current scope is [nat], the first search item is useless.
    We can ask for distributivity lemmas, these contain the string "distr" in
    their names. *)
Search (_ + _) (_ * _) "distr".

(** *** 1.2 Searching using metavariables *)

(** We have cheated a little bit. It often happens that we have no idea how
    a lemma is named. However, we know what distributivity (say, on the left)
    is. We can use a more precise pattern instead of (_ * _). *)
Search (_ * (_ + _) = _). (* nailed it *)

(** What about the commutativity of [Nat.add]? *)
Search (_ + _ = _ + _).

(** The list is somewhat manageable (and, by sheer luck, [Nat.add_comm] appears
    first), but we can be much more precise with meta-variables. *)
Search (?a + ?b = ?b + ?a).

(** We can even search for all commutativity lemmas: *)
Search (?op ?a ?b = ?op ?b ?a).

(** If we want to exclude the [bool] commutativity lemmas, we can, as before
    add the restriction that we want [nat] to be involved: *)
Search nat (?op ?a ?b = ?op ?b ?a).

(** Another possibility is to exclude any results mentioning [bool]: *)
Search (?op ?a ?b = ?op ?b ?a) -bool.

(** We can also opt to remove only results with "orb" it its name: *)
Search (?op ?a ?b = ?op ?b ?a) -"orb".

(** Or results where the (_ || _) operator appears (notice the scope key, since
    [bool_scope] is not currently opened): *)
Search (?op ?a ?b = ?op ?b ?a) -(_ || _)%bool.

(** ** Filtering on hypotheses (parameters) or conclusions (return type) *)

(** It often happens that we [Search] in the middle of a proof for a lemma we
    suspect will apply to the current goal. In that case, we can use
    the [concl:] specifier to restrict the [Search] output to results where
    a pattern (or notation) appears in the conclusion (a.k.a. return type). *)
Search concl:(_ + _ <= _).
Search concl:"||".

(** Of course, the [hyp:] specifier also exists to [Search] for a pattern or
    notation occurring in one of the hypotheses (a.k.a. parameters): *)
Search hyp:(_ + _ <= _).

(** We can be even more precise and specify that our pattern (or notation)
    should appear at the head of the conclusion (or an hypothesis), that is,
    the whole term should match our pattern, instead of a subterm.

    As an example, let us [Search] for lemmas about conjunctions and
    disjunctions.
    We want lemmas whose conclusion is a conjunction.
    We exclude [nat] in order to get only purely logical properties. *)
Search (_ \/ _) concl:(_ /\ _) -nat.

(** Notice that, in [Decidable.not_iff] and [bool_choice], the conclusion
    contains a conjunction but is not a conjunction. We can exclude them
    with the [headconcl] specifier: *)
Search (_ \/ _) headconcl:(_ /\ _) -nat.

(** The equivalence [Decidable.not_or_iff] has also disappeared, because
    it is actually treated as a lemma having a single conclusion of the form
    [(_ <-> _)], hence not of the form [(_ /\ _)]. *)

(** We can list all lemmas about addition with an equivalence as a conclusion: *)
Search "+" headconcl:"<->".

(** and all lemmas having an equivalence as a hypothesis. *)
Search headhyp:"<->".

(** Finally the [head] keyword is just a shorthand for [headconcl] or [headhyp]: *)
Search head:"<->".

(** ** 2. Advanced [Search] options *)

(** *** 2.1 Disambiguating strings in Search queries *)

(** We have seen two different usages of strings in search queries, namely,
    searching for constants whose name contains the string, such as: *)
Search "comm".

(** or, search for constants whose type contain a notation, such as: *)
Search "||".
Search "+".

(** So, what really happens here?
    First, Coq makes a different between identifier (name) characters and
    other characters.
    The characters '|' and '+' cannot be used in constant names, so Coq guesses
    it should interpret "||" and "+" as notations to appear in the types, not as
    substrings of names.

    What happens when a notation uses only identifier characters?
    This is the case for the [mod] operator: *)
About "mod".

(** Searching for "mod" lists constants whose identifiers contain "mod", as
    is indicated in the [divmod] operation here: *)
Search "mod".

(** To [Search] for constants where the notation [mod] appears in the type, we
    have two solutions: either we enclose the string with single quotes: *)
Search "'mod'".

(** or we give an explicit scope key (hence it must be a notation): *)
Search "mod"%nat.

(** Of course, we can still use a pattern instead of a string: *)
Search (_ mod _).

(** *** 2.2 Filtering results by logical kind and disjunctions of criteria. *)

(** We can also [Search] for a constant defined with a specific keyword.
    For instance, the following lists all [Lemma]s whose names contain "add"
    and types contain [0]: *)
Search "add" 0 is:Lemma.

(** Same for constants defined with the [Theorem] keyword: *)
Search "add" 0 is:Theorem.

(** Now, if we want both [Lemma]s and [Theorem]s we can use the general
    "or" construct in [Search] queries: *)
Search "add" 0 [is:Theorem | is:Lemma].

(** The following lists lemmas and theorems about [Nat.add] or [Nat.mul]
    containing the strings "comm" or "assoc": *)
Search [Nat.add | Nat.mul] ["comm" | "assoc"] [is:Lemma | is:Theorem].

(** The interested reader can refer to
    [the reference manual](https://coq.inria.fr/doc/V8.19.0/refman/proof-engine/vernacular-commands.html?highlight=search#search-by-keyword)
    for the list of all logical kinds which can appear after [is:]. *)

(** *** 2.3 Searching inside or outside a specific module *)

(** Finally it is possible to further restrict the [Search] results inside or
    outside a specific [Module] (see the [module tutorial](TODO.todo) for
    more information about modules. *)

Search concl:"+" concl:"*" headconcl:(_ < _) inside Nat.

(** The [in] keyword is a shorthand for [inside]: *)
Search concl:"+" concl:"*" headconcl:(_ < _) in Nat.

(** The [outside] keyword on the contrary excludes results from a specific
    [Module]. *)

Search "+" outside Nat.

(** Now, these last [Search]es exhibit a subtlety related to the [Module]
    System. Actually, there are two modules named [Nat] in our environment. *)

(** The first to appear is the last to be [Require]d. In our case, its full
    name is [Coq.Arith.PeanoNat.Nat]: *)
About Nat.
Print Module Nat.

(** But this [Nat] module shadows the [Nat] module which already exists in
    [Init] (actually, as a side note, the [Coq.Init.Nat] module is [Include]d
    in [Coq.Arith.PeanoNat.Nat], but this is not relevant in this tutorial). *)

(** If one wants to [Search] for all lemmas in the [Nat] module taken from
    [Init], it suffices to qualify it more to disambiguate it: *)
Search _ in Init.Nat.

(** We can even shadow [PeanoNat.Nat] module in this file: *)
Module Nat.
  Lemma foo : 21 + 21 = 42. Proof. reflexivity. Qed.
End Nat.

Search _ in Nat.
Search "f" "o" in PeanoNat.Nat.

(** The take-home message here is that modules are often used to provide
    namespace facilities, so when using [inside] and [outside], one should
    often qualify them more. *)
