# platform-docs

This project aims to create online compilation of short and interactive tutorials and how-to guides for Coq and the Coq Platform.

Each core functionality and plugin of Coq and the Coq Platform should have (short) pedagogical tutorials and/or how-to guides demonstrating how to use the functionality, with practical examples.
They should further be available online through an interactive interface, most likely using JSCoq.

Tutorials and how-to guides serve different purposes and are complementary.
Tutorials guide a user during learning in discovering specific aspects of a feature like "Notations in Coq", by going through (simple) predetermined examples, and introducing notions gradually.
In contrast, how-to guides are use-case-oriented and guides users through real life problems and their inherent complexity, like "How to define functions by well-founded recursion and reason about them".

> [!TIP]
> To gain useful insights about what documentation should be, we recommand
> checking out the website [diataxis](https://diataxis.fr/) that discusses the
> different kind of documentations.
> In particular the [difference between tutorials and how-to](https://diataxis.fr/tutorials-how-to/)
> which are often mistaken.

Such of a documentation is complementary to others kind of documentation like the reference manual, and has several advantages:

- Tutorials should enable users to learn and discover specific features on their own, modularly, and according to their needs
- How-to should provide users practical answers to practical problems that they can refer to when working
- By nature, the documentation should be mostly horizontal, which should:
  - make it easy to navigate and to find specific information
  - prevent users from having to read a bunch documentation to be able to read a specific tutorial
  - make it possible to build gradually, making new tutorials and how-to available as we progress
  - allow differentiated learning: depending on your background or objective you can navigate the documentation differently, potentially reading different tutorials.
- It will enable us to showcase all that is possible in Coq's ecosystem
- It should be easy to maintain as once fully written a tutorials or how-to should have any reason to change, except if the associated feature changes

This project will necessarily have to be a collaborative undertaking considering the richness and diversity of our ecosystem.
There is a lot of work to be done, and we welcome contributions from the different communities.
As a base for work, we have established an [informal list](https://github.com/Zimmi48/platform-docs/blob/main/draft_structure_doc.md) of tutorials and how-to it could be interesting to have.
This list is not fixed and will necessarily evolve through discussions with the community and experience, but it should already give an idea of the potential of this project.




# How to contribute to the documentation

There is a lot of work to be done before having a comprehensive documentation for Coq and its Platform, and we welcome contributions.

There are different possible way to contribute depending on your time and technical skills:
- As users do not hesitate to gives us feedbacks on the project on the <span style="color:red"><u>zulip chan</u></span>
- There is need for regular reviewers to test tutorials, both general ones and expert ones
- There is a lot of tutorials and how-to to write, both about Coq and plugins in its platform
- There is technical work to be done on the (interactive) web interface's side

If you have an idea for a tutorial or how-to, you can create a discussion on the dedicated <span style="color:red"><u>zulip chan</u></span> to
get feedbacks through the writing and to reach other interested people.
You can also create a discussions on more specific zulip chan, like on the one dedicated to the package Equations if you are working on a tutorial for Equations.
Once you have a plan and some content, you can create a draft pull request to make your code accessible and get feedback on it while you (and others) progress on it.

In the sections below, we give some tips on what a good tutorial and how-to should be.

For the moment we only support files written in [coqdoc's syntax](https://coq.inria.fr/doc/V8.19.0/refman/using/tools/coqdoc.html?highlight=coqdoc).
It is not hard to learn  bit limited, and we plan to develop


> [!WARNING]
> Before starting to work on a tutorial or a how-to and invest time into it, check if someone hasn't already starter working on it and created a draft pull request about it.

> [!WARNING]
> A lot of stuffs have already be written about Coq, it can make sense to reuse some of the content. If you wish to do so, be careful that you are indeed allowed by the copyrights.

#### Template to start your file
Start your file with the following [template](https://github.com/Zimmi48/platform-docs/blob/main/template.md).
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
  > Installation:
  > - Equations is available by default in the Coq Platform
  > - Otherwise, it is available via opam under the name `coq-equations`


### Writing Tutorials

Tutorials are meant to introduce and explain the different aspects of a functionality step by step with examples.
The goal is to provide user with a action-oriented documentation that user can use to learn about a feature they don't know, and a (non-exhaustive and opinionated) material that they can come back to when they are stuck trying to use a feature.

We give some elements to write a good tutorial
You can write a tutorial by

#### Horizontality

Tutorials do not necessarily need to be long, nor should aim to present
all the aspects of a feature in one unique tutorial.
Moreover, they do not have the purpose to be exhaustive like a reference
manual, and do not have to discuss every single aspects of a feature.

On the contrary, the various independent aspects of a feature should be split into several tutorials.
As a general rule, a tutorial is becoming out too long or complicated to navigate, or if its structure is branching out, you may want to consider splitting it out.
Moreover, tutorials can also be split in order to provide a more gradual introduction to a complicated feature.

Doing so enables users to only have to read the basics to be able to start working, and leaves them the possibility to learn new aspects modularly, according to their needs.
It also makes the documentation easier to maintain and to navigate, and makes it easier add new tutorials.

When possible tutorials should try to be as self contained as possible, and should not hesitate to recall quickly a concept rather than referring to another tutorial.
Doing so only takes a bit more time when writing a tutorial but saves a lot of times to a lot of users that will not have to chase information in different other tutorials, tutorials which could in turn refer to other tutorials.
It also ease maintaining as one does not need to worry about potential modifications to other tutorials.

#### Adding Exercices
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

### Writing how-to

