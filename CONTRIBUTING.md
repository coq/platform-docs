
# Contribution Guidelines

## General Contribution guidelines

### Format
For the moment we only support files written in [coqdoc's syntax](https://coq.inria.fr/doc/V8.19.0/refman/using/tools/coqdoc.html?highlight=coqdoc).
It is not hard to learn but a bit limited.
We plan to be compatible with a more standard and polyvalent format in the futur.

### Template to start your file
To contribute, please start your file with the following [template](https://github.com/Zimmi48/platform-docs/blob/main/template.md).
It requires to fill very basic information:
  - a title
  - a summary of the tutorial and its content
  - a table of content
  - a list of prerequisites (needed / not needed / installation)

  The list of prerequisites includes what is necessary, but also what is
  not needed and brief installation instructions.
  Understanding what is not needed to know to a complete a tutorial is as
  important as knowing what is.
  For instance, the tutorial about Equations and well-founded recursion
  recall what is well-founded.

  The installation instructions are meant to be pretty short.
  They are basically about telling the user if the feature discussed is by
  default in Coq, its in the platform, and the name of the opam package.
  For instance, the installation instruction for the Equations package are:
  ```
  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name `coq-equations`
  ```



## Writing Tutorials
Tutorials are meant to introduce and explain the different aspects of a functionality, pedagogically, step by step with (simplified) examples.
The goal is to provide user with a action-oriented documentation that user can use to learn about a feature they don't know,
and a (non-exhaustive and opinionated) material that they can come back to when they are stuck trying to use a feature.
As examples, we have been working on new tutorials for the package Equations. 
The first is one is complete and can be checked out [here](https://github.com/Zimmi48/platform-docs/pull/1).

### Horizontality

Tutorials do not necessarily need to be long, nor should aim to present
all the aspects of a feature in one unique tutorial.
Moreover, they do not have the purpose to be exhaustive like a reference
manual, and do not have to discuss every single aspects of a feature.

On the contrary, the various independent aspects of a feature should be split into several tutorials.
As a general rule, a tutorial is becoming out too long or complicated to navigate, 
or if its structure is branching out, you may want to consider splitting it out.
Moreover, tutorials can also be split in order to provide a more gradual introduction to a complicated feature.

Doing so enables users to only have to read the basics to be able to start working, 
and leaves them the possibility to learn new aspects modularly, according to their needs.
It also makes the documentation easier to maintain and to navigate, and makes it easier add new tutorials.

When possible tutorials should try to be as self contained as possible, 
and should not hesitate to recall quickly a concept rather than referring to another tutorial.
Doing so only takes a bit more time when writing a tutorial but saves a lot of times to a lot of users 
that will not have to chase information in different other tutorials, tutorials which could in turn refer to other tutorials.
It also ease maintaining as one does not need to worry about potential modifications to other tutorials.

### Adding Exercices
As tutorials are meant for studying, do not hesitate to add few exercices for the users to try, e.g. functions or properties to prove or finish.
In general, we recommand to provide at least definitions prefilled with typing informations like:

```
Fixpoint map {A B} (f : A -> B) (l : list A) : list B := to_fill.

Lemma map_app {A B} (f : A -> B) (l l' : list A) : map f (l ++ l') = map f l + map f l'.
Proof. Admitted.
```

To do so, you can add the following code at the beginning of the tutorial.
It creates an axiom `to_fill` and hides it so that it is does not appear in the body of the tutorial.
```
(* begin hide *)
Axiom to_fill : forall A, A.
Arguments to_fill {_}.
(* end hide *)
```

You can also provides tests for the users to be able to check if its definition works.
You can do so by asking them to prove basic properties like `map_app` above, or by checking computation, for instance, via the following syntax
```
(* You can uncomment the following tests to try your functions *)
(* Succeed Example testing : map (Nat.add 1) (1::2::3::4::[]) = (2::3::4::5:[]) := eq_refl. *)
```

> [!CAUTION]
> Being able to complete the exercices should not be necessary to be able
> to complete and understand the rest of the tutorial.

