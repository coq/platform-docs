
# Contribution Guidelines

## How to contribute to the documentation

There is a lot of work to be done before having a comprehensive documentation for Coq and its Platform, and we welcome contributions.

There are different possible ways to contribute depending on your time and technical skills:

- As user, do not hesitate to gives us feedback on the project on the dedicated [Zulip stream](https://coq.zulipchat.com/#narrow/stream/437203-Platform-docs)
- There is need for regular reviewers to test tutorials, both general ones and expert ones
- There is a lot of tutorials and how-tos to write, both about Coq and plugins in its Platform
- There is technical work to be done on the (interactive) web interface side

## Building the documentation

We generate interactive documents using jsCoq from the `.v` files in the `src` directory.
To build and test the documentation locally, you need to have npm and the Coq Platform installed.
Then run:

```bash
cd src
make node_modules
make
make serve
```

The last step will start a local server that you can access at `http://localhost:8080`.

To extend the list of packages that are available in jsCoq, you should add them both in `src/package.json` and in `src/jscoq-agent.js`.

## Writing Tutorials and How-tos
If you have an idea for a tutorial or how-to, you can create a discussion on the dedicated [Zulip stream](https://coq.zulipchat.com/#narrow/stream/437203-Platform-docs)
to get feedback on your idea, through the writing and to reach others that may be interested.
If there is a stream dedicated to the topic or package that you are covering in your tutorial, you can also create a discussion there.
For instance, if you are working on tutorials for the package
Equation, you can create a discussion in the associated stream.

Once you have a plan and some content, you can create a draft pull request to make your code accessible
and get feedback on it while you (and others) progress on it.

> [!WARNING]
> Before starting to work on a tutorial or a how-to and invest time into it, check if it is not already existing,
> or if someone hasn't already started working on it, either by creating a discussion on the [Zulip stream](https://coq.zulipchat.com/#narrow/stream/437203-Platform-docs) or a draft pull request about it.

> [!WARNING]
> Lots of stuff have already be written about Coq, it can make sense to reuse some of the content.
> If you wish to do so, be careful that you are indeed allowed by the copyright owners or the content licenses.


## General Guidelines

### Format
For the moment we only support files written in [coqdoc's syntax](https://coq.inria.fr/doc/V8.19.0/refman/using/tools/coqdoc.html?highlight=coqdoc).
It is not hard to learn but a bit limited.
We plan to be compatible with a more standard and polyvalent format in the future.

For writing sections, please use the following conventions:
```
* Title
** Section
*** Subsection
**** SubSubsection
```

### Template to start your file
To contribute, please start your file with the following [template](template.md).
It requires to fill very basic information:
  - a title
  - a summary of the tutorial and its content
  - a table of content
  - a list of prerequisites (needed / not needed / installation)

  The list of prerequisites includes what is necessary, but also what is
  not needed and brief installation instructions.
  Understanding what is not needed to know to follow a tutorial is as
  important as knowing what is.
  For instance, the tutorial about Equations and well-founded recursion
  recalls what is well-founded to the reader, so knowing about this is not a
  requirement to follow the tutorial.

  The installation instructions are meant to be pretty short.
  They are basically about telling the user if the feature discussed is by
  default in Coq, in the Coq platform, and the name of the opam package
  (for users that may want to use opam directly rather than through the Coq Platform).
  For instance, the installation instruction for the Equations package are:
  ```
  Installation:
  - Equations is available by default in the Coq Platform
  - Otherwise, it is available via opam under the name `coq-equations`
  ```

## Writing Tutorials
Tutorials are meant to introduce and explain the different aspects of a functionality, pedagogically, step by step with (simplified) examples.
The goal is to provide user with an action-oriented documentation that user can use to learn about a feature they don't know,
and a (non-exhaustive and opinionated) material that they can come back to when they are stuck trying to use a feature.
As examples, we have been working on new tutorials for the package Equations.
The first one is complete and can be checked out [here](src/Tutorial_Equations_basics.v).


### Horizontality

Tutorials do not necessarily need to be long, nor should aim to present
all the aspects of a feature in one unique tutorial.
Moreover, they do not have the purpose to be exhaustive like a reference
manual, and do not have to discuss every single aspects of a feature.

On the contrary, the various independent aspects of a feature should be split into several tutorials.
As a general rule, if a tutorial is becoming too long or complicated to navigate,
or if its structure is branching out, you may want to consider splitting it out.
Moreover, tutorials can also be split in order to provide a more gradual introduction to a complicated feature.

Doing so enables users to only have to read the basics to be able to start working,
and leaves them the possibility to learn new aspects modularly, according to their needs.
It also makes the documentation easier to maintain and to navigate, and makes it easier to add new tutorials.

When possible tutorials should try to be as self contained as possible,
and should not hesitate to recall quickly a concept rather than referring to another tutorial.
Doing so only takes a bit more time when writing a tutorial but saves a lot of times to a lot of users
that will not have to chase information in different other tutorials, tutorials which could in turn refer to other tutorials.
It also eases maintenance as one does not need to worry about potential modifications to other tutorials.

### Adding Exercises
As tutorials are meant for studying, do not hesitate to add some exercises for the users to try, e.g. functions or properties to prove or finish.
In general, we recommend to provide at least definitions prefilled with typing information like:

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

You can also provides tests for the users to be able to check if their definition works.
You can do so by asking them to prove basic properties like `map_app` above, or by checking computation, for instance, via the following syntax
```
(* You can uncomment the following tests to try your functions *)
(* Succeed Example testing : map (Nat.add 1) (1::2::3::4::[]) = (2::3::4::5:[]) := eq_refl. *)
```

> [!CAUTION]
> Being able to complete the exercises should not be necessary to be able
> to complete and understand the rest of the tutorial.

