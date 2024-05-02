# Structure of Coq's tutorial documentation

**This an informal draft**, established through informal discussions with the community, of what the documentation could look in terms of content.
**It is not fixed and will evolve with the project** according to the need of the users.

---
# Overall plan

- Preliminary
  - Trying it out (games), Installing, Courses and Books
- Writing proofs in Coq
  - Basic tactics
  - Solvers and Decision procedures
  - SSReflect
  - MetaProgrammation
- Programmation in Coq
  - Writing programs in Coq
  - Extraction
  - Programming by dependent pattern matching with Equations
  - Tools for verifying softwares
  - Verified Softwares in Coq
- Coq functionalities
  - Stuffs that make your life easier
  - Packaging mathematical structures
  - Computing in Coq
  - Others
- Coq's theory
  - Sorts in Coq
  - (Co)Inductive Types
  - Coq and Axioms
  - Coq and Paradoxes
- Libraries
  - General purpose librairies, real numbers, ...


---
# Detailed plan

## Preliminary
- Trying it out (games)
- Installing
- Courses and Books

## Writing proofs in Coq

### Basic tactics
- Reasoning about Logic
- Reasoning about Equality
- Reasoning about Inductive Types
- Proof Search tactics (assumption, easy, trivial, intuition ?)
- Tactics for Forward Reasoning
- Combining Tactics

### Solvers and Decision procedures
- Advanced Proof search tactics :
  - auto / eauto / typeclasses eauto
- Domain Specific Solvers :
  - congruence, bauto, tauto, first-order, lia, itauto, etc...
- Algebraic Solvers :
  - Ring etc... Algebra-tactics
- SMT Solvers
- CoqHammer

### SSReflect
- I guess there is much to say :smile:

### MetaProgrammation, writing your own tactics
- Ltac
- Ltac2
- MTac2
- CoqElpi :
  - Tutorial
  - How to do sth that Elpi is good at
- MetaCoq


## Programming in Coq
- Writing programs in Coq
  - Termination / Well-founded
  - Pattern matching in Coq
  - Coinductive Types
- Programming by dependent pattern matching with Equations
- Extraction
- Tools for verifying softwares
- Verified Softwares in Coq


## Coq's functionalities

### Stuffs that make your life easier
- Searching for lemmas
- Implicit Arguments
- Notations
- Sections
- Modules

### Packaging Mathematical Structures
- Records
- Type Classes
- Canonical Structures
- Hierarchy builders

### Computing in Coq
- Native compute
- Vm compute
- CoqEal
- Trocq

### Else
- Program derivation
- dpdgraphs
- UniCoq
- ParamCoq


## Coq's Theory

### Sorts in Coq
- Types and cumulativity
- Prop
- SProp
- Polymorphism of Sorts

### (Co)Inductive Types
- Inductive Types
  - Inductives Types, Induction, Pattern Matching, WellFounded Recursion
- Coinduction Types

### Coq and Axioms
- Main Axioms and Compatibilities
- Extentionality Principles
- Classical Logic
- Axiom of Choice
- Axiom K / UIP
- Univalence Axiom

### Coq and Paradoxes
- Universe Paradoxes (Type:Type, etc...)
- Guard Conditions Paradoxes (Non Strict Positivity, etc...)
- Positive CoInductive Types



## Libraries

There is work to be done to understand how to introduce the different and many libraries existing in the Coq ecosystem


### General Purpose Libraries :
- StdLib
- MathComp
- UniMath
- Coq Hott
- Corn
- ExtLib
- Stdpp ?

### Real Numbers Libraries :
- Coquelicot
- Flocq
- Gappa
- Coq Interval

### Prime Numbers
- Coq prime numbers generator
- Coqprime

### Computer Science :
- RegLanguage

