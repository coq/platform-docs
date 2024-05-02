# platform-docs
A project of short tutorials and how-to guides for Coq features and Coq Platform packages.

# How to contribute

If you wish to contribute that is great. There is a lot of work to be done
before having a comprehensive documentation for Coq and its Platform.

#### What to work on
There are different ways to contribute to the project, you can:
- Test new tutorials currently in PR
- Write a tutorial
- Write a How-to
- Improve an existing tutorial or how-to

There is not a fixed list of tutorials or "how-to" to write.
For a general idea, you can check out this
<font color="red"><ins>informal list</ins></font>

> [!TIP]
> To gain useful insights on what documentation should be, we recommand
> checking out the website [diataxis](https://diataxis.fr/) that discusses the
> different kind of documentations.
> In particular the [difference between tutorials and how-to](https://diataxis.fr/tutorials-how-to/)
> which are often mistaken.

### Tutorials

todo

### How-to

###

## Writing guidelines

### Formatting
- For the moment we only support coqdoc's syntax a custom documentation
  syntax for Coq.
  You can find information about it [here](https://coq.inria.fr/doc/V8.19.0/refman/using/tools/coqdoc.html?highlight=coqdoc)
- The numbers of characters per line must be between 80 to 100
- No trailing white spaces are allowed

### Template to start your file
Start your file with the following [<font color="red"><ins>template</ins></font>](todo), that requires to fill basic information:
  - a title
  - a summary of the tutorial and its content
  - a table of content
  - a list of prerequisites (needed / not needed / installation)

  The list of prerequisites includes what is necessary, but also what is not needed and instructions installation.

  Understanding what is not needed to know to a complete a tutorial is as important as knowing what is. For instance, the tutorial about Equations and well-founded recursion recall what is well-founded .

  The installation instructions are meant to be pretty short. They are basically about telling the user if the feature discussed is by default in Coq, its in the platform, and the name of the opam package.
  For instance, the installation instruction for the Equations package are

  > Installation:
  > - Equations is available by default in the Coq Platform
  > - Otherwise, it is available via opam under the name `coq-equations`
