# platform-docs

## A Compilation of Short Interactive Tutorials and How-To Guides for Coq
This project aims to create an online compilation of short and interactive tutorials and how-to guides for Coq and the Coq Platform.

Each core functionality and plugin of Coq and the Coq Platform should have (short) pedagogical tutorials and/or 
how-to guides demonstrating how to use the functionality, with practical examples.
They should further be available online through an interactive interface, most likely using JSCoq.

Tutorials and how-to guides serve different purposes and are complementary.
Tutorials guide a user during learning in discovering specific aspects of a feature like "Notations in Coq",
by going through (simple) predetermined examples, and introducing notions gradually.
In contrast, how-to guides are use-case-oriented and guides users through real life problems and their inherent complexity,
like "How to define functions by well-founded recursion and reason about them".

> [!TIP]
> To gain useful insights about what documentation should be, we recommand
> checking out the website [diataxis](https://diataxis.fr/) that discusses the
> different kind of documentations.
> In particular the [difference between tutorials and how-to](https://diataxis.fr/tutorials-how-to/)
> which are often mistaken.

### Why it is important
- Having an easy to access documentation, accessible through a nice centralized
  online interface is of utmost importance to engage new users, and keep current
  users. 
  We can not expect users to have to dig on their own through the reference
  manual, books, or github repositories to learn how to use a particular feature
  that appeals to them.
  Most particularly as these sources may not contain the basic answers they are
  looking for due to their nature. 
- Not having such a documentation prevents people from actually discovering and
  learning by themselves new amazing features, as well as the richness of our
  ecosystem.
  Many amazing features are still currently under-documented, and the existing
  documentation is often scattered out. 
  A symptom of that is the trouble that students are currently facing to find
  answers or discover new functionalities by themselves.
- Writing documentation forces us to do stuff right, and consequently to 
  understand better features, and their basic applications.
  We hope that by writing the documentation, we will clarify the use of many
  features, and potentially discover bugs.
  Actually, writing tutorials [for Equations](https://github.com/Zimmi48/platform-docs/pull/1#issuecomment-2098810034)
  as already revealed that one of the main features had an unwanted behavior and a bug.
- Most math users are currently unaware of the extent of what has been
  formalised and is available in Coq.
  There are many libraries, and it is not easy to know which library to use, or
  to know on which axioms they rely or their compatibilities. 
  This is obviously not just a documentation issue, but having a clearer
  documentation of what we have and where would help.


### Advantages
Such form of documentation is complementary to other kinds of documentation like the reference manual, and has several advantages:

- Tutorials should enable users to learn and discover specific features on their own, modularly, and according to their needs
- How-tos should provide users practical answers to practical problems that they can refer to when working
- By nature, the documentation should be mostly horizontal, which should:
  - make it easy to navigate and to find specific information
  - prevent users from having to read a bunch of documentation to be able to read a specific tutorial
  - make it possible to build gradually, making new tutorials and how-tos available as we progress
  - allow differentiated learning: depending on your background or objective you can navigate the
    documentation differently, potentially reading different tutorials.
- It will enable us to showcase all that is possible in Coq's ecosystem
- It should be easy to maintain as once fully written a tutorial or how-to should have any reason to change,
  except if the associated feature or known best practices change.

### Plan
This project will necessarily have to be a collaborative undertaking considering how much work there is to do,
and the richness and diversity of our ecosystem.
Yet, as the tutorials can mostly be designed independently, by combining the different expertise of the different communities,
there is good hope to quickly get to a good documentation, and we welcome contributions.
As a base for work, we have established an [informal list](https://github.com/Zimmi48/platform-docs/blob/main/draft_structure_doc.md)
of tutorials and how-tos it could be interesting to have.
This list is not fixed and will necessarily evolve through discussions with the community and experience, 
but it should already give an idea of the potential of this project.




## How to contribute to the documentation

There is a lot of work to be done before having a comprehensive documentation for Coq and its Platform, and we welcome contributions.

There are different possible ways to contribute depending on your time and technical skills:
- As user, do not hesitate to gives us feedback on the project on the dedicated <span style="color:red"><u>Zulip stream</u></span>
- There is need for regular reviewers to test tutorials, both general ones and expert ones
- There is a lot of tutorials and how-tos to write, both about Coq and plugins in its Platform
- There is technical work to be done on the (interactive) web interface side

We detail below the different ways to contribute. 
In all cases, if you wish to contribute, please check the 
[Contribution Guidelines](https://github.com/Zimmi48/platform-docs/blob/main/README.md).

### Writing Tutorials and How-tos
If you have an idea for a tutorial or how-to, you can create a discussion on the dedicated <span style="color:red"><u>Zulip stream</u></span>
to get feedback on your idea, through the writing and to reach others that may be interested.
If there is a stream dedicated to the topic or package that you are covering in your tutorial, you can also create a discussion there.
For instance, if you are working on tutorials for the package
Equation, you can create a discussion in the associated stream.

Once you have a plan and some content, you can create a draft pull request to make your code accessible
and get feedback on it while you (and others) progress on it.

> [!WARNING]
> Before starting to work on a tutorial or a how-to and invest time into it, check if it is not already existing,
> or if someone hasn't already started working on it, either by creating a discussion on the Zulip stream or a draft pull request about it.

> [!WARNING]
> Lots of stuff have already be written about Coq, it can make sense to reuse some of the content. 
> If you wish to do so, be careful that you are indeed allowed by the copyright owners or the content licenses.


