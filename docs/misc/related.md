Related References
======================

GA & Lean related
--------------------

### Lean/Mathlib PRs

- [`feat(data/quaternion): define quaternions and prove some basic properties #2339`](https://github.com/leanprover-community/mathlib/pull/2339/)

### Inspiring Lean Code

- [Formalizing Euclid's Axioms](https://github.com/vaibhavkarve/leanteach2020/blob/master/src/euclid.lean)
- [commutative differential graded algebras](https://gist.github.com/kbuzzard/f5ee35457c5d257ceec58c66d7da0c38)
- [free module](https://gist.github.com/sflicht/53bdcdb1e3536e668736f7b4eb63cd79)
- [Huber_pair](https://github.com/leanprover-community/lean-perfectoid-spaces/blob/master/src/Huber_pair.lean#L72)
- https://github.com/jsm28/bmo2-2020-lean/
- https://github.com/GeoCoq/GeoCoq/tree/master/Highschool (in Coq)

### Lean/Mathlib Doc

- https://leanprover-community.github.io/mathlib-overview.html
- https://leanprover-community.github.io/mathlib_docs/
- [data/overview.yaml](https://github.com/leanprover-community/leanprover-community.github.io/blob/newsite/data/overview.yaml)
  - https://leanprover-community.github.io/undergrad.html
  - https://leanprover-community.github.io/undergrad_todo.html
- [style guide](https://github.com/leanprover-community/leanprover-community.github.io/blob/newsite/templates/contribute/style.md)
- https://lean-forward.github.io/
- [tutorial/category_theory/intro](https://github.com/leanprover-community/mathlib/blob/master/docs/tutorial/category_theory/intro.lean)

### Inspiring Papers and Slides

- [The Lean Mathematical Library](https://arxiv.org/abs/1910.09336)
- [Maintaining a library of formal mathematics](https://lean-forward.github.io/mathlib-maintenance/paper.pdf)
- [Formalising perfectoid spaces](https://arxiv.org/abs/1910.12320)
- "ForTheL texts and Lean texts" in http://www.andrew.cmu.edu/user/avigad/meetings/fomm2020/slides/fomm_koepke.pdf
- [Diagram Chasing in Interactive Theorem Proving](https://pp.ipd.kit.edu/uploads/publikationen/himmel20bachelorarbeit.pdf)
- [Homological algebra in Lean](https://github.com/TwoFX/lean-homological-algebra)

### Inspiring Chats

- [grassmann algebra and clifford algebra](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/cleaning.20up.20this.20tactic.20proof.20%28regarding.20closures%29/near/193026381)
- [fold notation](https://gitter.im/leanprover_public/Lobby?at=5a5686366117191e614e3ce4)
    - `(fold* <sep> <fun> <init> <terminator>)`
    - [tests/lean/fold](https://github.com/leanprover-community/lean/blob/master/tests/lean/fold.lean)
    - [tests/lean/over_notation](https://github.com/leanprover-community/lean/blob/master/tests/lean/over_notation.lean)
- [euclidean_vector_space](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Some.20olympiad.20formalisations/near/197858180)

### Notation

- https://github.com/leanprover/vscode-lean/blob/master/translations.json
  - https://en.wikipedia.org/wiki/Unicode_subscripts_and_superscripts
  - https://en.wikipedia.org/wiki/List_of_mathematical_symbols_by_subject
  - [Unicode characters and corresponding LaTeX math mode commands](http://milde.users.sourceforge.net/LUCR/Math/unimathsymbols.pdf)


### Tactics

- [Lean Cheatsheet](https://gist.github.com/utensil/dc635f2991255f76d8da797efdabbf15)
  - https://www.imo.universite-paris-saclay.fr/~pmassot/enseignement/math114/tactiques.pdf (in French)
- https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html
- http://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf
- https://leanprover-community.github.io/extras/tactic_writing.html#marios-monadic-symbols-cheat-sheet

- [A Lean tactic for normalising ring expressions with exponents (short paper)](https://lean-forward.github.io/ring_exp/paper.pdf)
- [Simplifying casts and coercions](https://lean-forward.github.io/norm_cast/norm_cast.pdf)
- https://github.com/lean-forward/field
- https://github.com/lean-forward/ring_exp

GA Formalization Related
--------------------------

- Implementing Geometric Algebra Products with Binary Tree - 2014
    - https://github.com/thery/GeometricAlgebra
- Formalization of Geometric Algebra in HOL Light - li2018.pdf
    - https://github.com/jrh13/hol-light/tree/master/Geometric_Algebra
- A New Formalization of Origami in Geometric - 2016
- Formalization of Conformal Geometric Algebra and Robot Kinematics

- Reference manuals
    - Coq: https://coq.inria.fr/refman/index.html
        - https://github.com/coq/coq/blob/master/doc/tools/coqrst/coqdomain.py
    - HOL Light: https://www.cl.cam.ac.uk/~jrh13/hol-light/reference.html
    - Isabelle/HOL
        - https://isabelle.in.tum.de/documentation.html
        - https://isabelle.in.tum.de/dist/library/HOL/index.html
        - https://devel.isa-afp.org/browser_info/current/AFP/Quaternions/
        - https://www.isa-afp.org/browser_info/current/AFP/Octonions/

GA related
-------------

- https://en.wikipedia.org/wiki/Geometric_algebra
  - https://en.wikipedia.org/wiki/Sedenion
- [Geometrization of the Real Number System by Garret Sobczyk](https://arxiv.org/abs/1707.02338)
- [Projective Geometric Algebra as a Subalgebra of Conformal Geometric algebra](https://arxiv.org/abs/2002.05993)
- [Versor Cheat Sheet](http://versor.mat.ucsb.edu/masters_appendix.pdf)
- https://github.com/pygae/GAlgebra.jl/blob/master/test/runtests.jl
- Chapter 2 Clifford Algebra in [A Theory of Neural Computation
with Clifford Algebras](https://macau.uni-kiel.de/servlets/MCRFileNodeServlet/dissertation_derivate_00001402/d1402.pdf)
- Chapter 14 Definitions of Clifford Algebra in Clifford Algebras and Spinors by Lounesto
- [All Hail Geometric Algebra!](https://crypto.stanford.edu/~blynn/haskell/ga.html)
- [Chris Doran's Geometric Algebra Haskell Package](https://github.com/ga/haskell)
    - http://geometry.mrao.cam.ac.uk/2016/10/geometric-algebra-2016/
- http://math.uga.edu/~pete/quadraticforms.pdf
- [Comparing Complex Numbers to Clifford Algebra](https://www.av8n.com/physics/complex-clifford.pdf)
- [Euclidean Geometry and Geometric Algebra](http://geometry.mrao.cam.ac.uk/2020/06/euclidean-geometry-and-geometric-algebra/)

Related Math Concepts
------------------------

- [Free module](https://en.wikipedia.org/wiki/Free_module)
- [Free algebra](https://en.wikipedia.org/wiki/Free_algebra)
- [Universal algebra](https://en.wikipedia.org/wiki/Universal_algebra)
- [Sedenion](https://en.wikipedia.org/wiki/Sedenion)
- [Alternative algebra](https://en.wikipedia.org/wiki/Alternative_algebra)
- [Metric signature](https://en.wikipedia.org/wiki/Metric_signature)
- [Complete lattice](https://en.wikipedia.org/wiki/Complete_lattice)
- [Filters](https://en.wikipedia.org/wiki/Filter_(mathematics))
  - [Topology in mathlib](https://www.imo.universite-paris-saclay.fr/~pmassot/topology.pdf)
- [examples of fields](https://planetmath.org/examplesoffields)
- [differential forms on simplices](https://ncatlab.org/nlab/show/differential+forms+on+simplices)
  - [Differential graded algebras](https://stacks.math.columbia.edu/tag/061U)

> A [Clifford algebra](https://en.wikipedia.org/wiki/Clifford_algebra) is an algebra generated by a vector space with a quadratic form, and is a unital associative algebra(a K-algebra(K is called the base field of Clifford algebra)), and satisfy a [universal property](https://en.wikipedia.org/wiki/Universal_property).
> Let Q:V→k denote a quadratic form on a vector space V over a field k. The Clifford algebra Cl(V,Q) is defined as T(V)/I_Q where T(V) is the tensor algebra of V and I_Q is the two-sided ideal generated by all elements of the form v⊗v−Q(v) for all v∈V.
> Cl(V,Q) is the exterior algebra ∧V when Q=0.
> Clifford algebra is also a quantization of the exterior algebra.
> To create a Clifford algebra, all one needs to do is specify a quadratic form.
> Cl(V,Q) is a N-[filtered algebra](https://en.wikipedia.org/wiki/Filtered_algebra), Z/2Z-[graded algebra](https://en.wikipedia.org/wiki/Graded_ring#Graded_algebra), the associated graded algebra to the filtration is the exterior algebra
> quantization map q: ∧(V)→Cl(V)
> Clifford algebras may be thought of as quantizations (cf. quantum group) of the exterior algebra, in the same way that the [Weyl algebra](https://en.wikipedia.org/wiki/Weyl_algebra) is a quantization of the symmetric algebra.
> Weyl algebras and Clifford algebras admit a further structure of a [*-algebra](https://en.wikipedia.org/wiki/*-algebra), and can be unified as even and odd terms of a superalgebra, as discussed in CCR and CAR algebras.

- [Clifford Algebras in Sage manual](https://doc.sagemath.org/html/en/reference/algebras/sage/algebras/clifford_algebra.html)
- [Clifford Algebras as Filtered Algebras](http://www-math.mit.edu/~dav/cliffordfilt.pdf)
- [MATH 651: Lie Algebras - Lecture 8 - Universal Enveloping Algebras and Related Concepts, II](https://www.math.upenn.edu/~brweber/Courses/2013/Math651/Notes/L8_UEnvAlgII.pdf)
- [PG course on Spin Geometry - Lecture 1: Clifford algebras: basic notions](https://empg.maths.ed.ac.uk/Activities/Spin/Lecture1.pdf)
- [MAT 1120HF Lie groups and Clifford algebras - CHAPTER 2 Clifford algebras](http://www.math.toronto.edu/mein/teaching/LieClifford/cl2.pdf)
- [Topics in Representation Theory: Clifford Algebras](http://www.math.columbia.edu/~woit/notes17.pdf)
- [Clifford algebras and Lie theory](https://link.springer.com/chapter/10.1007%2F978-3-642-36216-3_2)

- [Geometric Algebra FAQ](https://staff.science.uva.nl/l.dorst/clifford/faq.html)
  - Q11. HOW IS IT DIFFERENT FROM CLIFFORD ALGEBRA?
  - Q12. HOW IS IT DIFFERENT FROM GRASSMANN-CAYLEY ALGEBRA?

Lean related
------------------

- [lean](https://github.com/leanprover-community/lean) - Lean Theorem Prover
- [format_lean](https://github.com/leanprover-community/format_lean) - A Lean file formatter
  - https://sphinx-litprog.readthedocs.io/en/stable/
- [mathlib-tools](https://github.com/leanprover-community/mathlib-tools) - Development tools for https://github.com/leanprover-community/mathlib
- [lean-client-python](https://github.com/leanprover-community/lean-client-python) - Python talking to the Lean theorem prover
- [doc-gen](https://github.com/leanprover-community/doc-gen) - Generate HTML documentation for mathlib and Lean
- [elan](https://github.com/Kha/elan) - A Lean version manager
- [olean-rs](https://github.com/digama0/olean-rs) - parser/viewer for olean files
- [Lean-game-maker](https://github.com/mpedramfar/Lean-game-maker) - This project converts structured Lean code into an interactive browser game.

- [The Lean Reference Manual](https://leanprover.github.io/reference/)
- [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/)
- [The Lean Theorem Prover](http://www.contrib.andrew.cmu.edu/~avigad/Talks/lean_ini.pdf)
- [Logic and Proof](https://leanprover.github.io/logic_and_proof/)
- [The Hitchhiker's Guide to Logical Verification](https://github.com/blanchette/logical_verification_2020/raw/master/hitchhikers_guide.pdf)

- [tutorials](https://github.com/leanprover-community/tutorials) - Some Lean tutorials
- [mathematics_in_lean](https://github.com/leanprover-community/mathematics_in_lean)
- https://github.com/avigad/mathematics_in_lean_source
- [mathlib](https://github.com/leanprover-community/mathlib) - Lean mathematical components library
- [lean-perfectoid-spaces](https://github.com/leanprover-community/lean-perfectoid-spaces) - Perfectoid spaces in the Lean formal theorem prover.
- [natural_number_game](https://github.com/ImperialCollegeLondon/natural_number_game) - Building the natural numbers in Lean.
- [complex-number-game](https://github.com/ImperialCollegeLondon/complex-number-game) - The Complex Number Game. Make the complex numbers in Lean.
- [group-theory-game](https://github.com/ImperialCollegeLondon/group-theory-game) - Building group theory from scratch in Lean
- [real-number-game](https://github.com/ImperialCollegeLondon/real-number-game) - A gamification of the theorems in MATH40002 Analysis 1
- [M1P1-lean](https://github.com/ImperialCollegeLondon/M1P1-lean) - Material from M1P1, formalised in Lean
- [M4000x_LEAN_formalisation](https://github.com/JasonKYi/M4000x_LEAN_formalisation) - Formalising lecture notes from 1st year Imperial Mathematics course.
- [M40001_lean](https://github.com/ImperialCollegeLondon/M40001_lean)
- [Theorem proving hello world: prove a+0=a and 0+a=a](https://www.codewars.com/kata/5c879811bc562909bf65c8e6/train/lean)
- https://leanprover-community.github.io/learn.html

- [formalabstracts](https://github.com/formalabstracts/formalabstracts) - 
- [formal-encoding](https://github.com/IMO-grand-challenge/formal-encoding) - Formal encoding of IMO problems
- [cubical lean](https://github.com/groupoid/lean) - Ground Zero: cubical base library for Lean 3
- [xena](https://github.com/kbuzzard/xena) - Lean Library currently studying for a degree at Imperial College
  - http://wwwf.imperial.ac.uk/~buzzard/xena/
  - [xena-UROP-2018](https://github.com/ImperialCollegeLondon/xena-UROP-2018) - A place to put our 2018 Xena project UROP thoughts and programs.
    - [Geometry in Lean](https://github.com/ImperialCollegeLondon/xena-UROP-2018/tree/master/src/Geometry)
    - [vector space](https://github.com/ImperialCollegeLondon/xena-UROP-2018/blob/master/src/vector_space.lean)
  - [The Xena Project summer projects, 2020](http://wwwf.imperial.ac.uk/~buzzard/xena/UROP2020.html)
- [mathematica](https://github.com/robertylewis/mathematica) - Lean-independent implementation of the MM-Lean link
- [mm-lean](https://github.com/minchaowu/mm-lean) - One direction of the MM-Lean link
- [two-level](https://github.com/annenkov/two-level) - Two-Level Type Theory
- [common-sense-lean](https://github.com/own-pt/common-sense-lean) - The initial ideas of a common sense library in Lean based on SUMO Ontology
- [lean-for-hackers](https://github.com/agentultra/lean-for-hackers)
- [tptp-lean-puzzles](https://github.com/FredsoNerd/tptp-lean-puzzles)
- https://github.com/unitb/temporal-logic

- [chore(*): replace rec_on with induction and match for readability](https://github.com/leanprover-community/mathlib/commit/f02a88b817a86450ce95514851f582dc9bdc460e)

- [An Infinitely Large Napkin](https://github.com/vEnhance/napkin/)

Theorem Prover/Type theory related
-------------------------------------

- [lean-type-theory](https://github.com/digama0/lean-type-theory) - LaTeX code for a paper on lean's type theory
- https://leanprover-community.github.io/lean-perfectoid-spaces/type_theory.html
- [https://manishearth.github.io/blog/2017/03/04/what-are-sum-product-and-pi-types/](https://manishearth.github.io/blog/2017/03/04/what-are-sum-product-and-pi-types/)
- 4 Defining Codatatypes in [Defining (Co)datatypes and Primitively (Co)recursive Functions in Isabelle/HOL](http://isabelle.in.tum.de/dist/doc/datatypes.pdf)
- [A Tutorial on (Co-)Inductive Types in Coq](https://www.labri.fr/perso/casteran/RecTutorial.pdf)
- [Canonical Structures for the working Coq user](https://hal.inria.fr/hal-00816703/file/main.pdf)
- [Comparison of Two Theorem Provers: Isabelle/HOL and Coq](https://arxiv.org/abs/1808.09701)
- [A Survey of Languages for Formalizing Mathematics](https://arxiv.org/abs/2005.12876)
- [Category theory for scientists](https://arxiv.org/abs/1302.6946)
- [Rethinking set theory](https://arxiv.org/abs/1212.6543)
- [Lean versus Coq: The cultural chasm](https://artagnon.com/articles/leancoq)
- [Equality of mathematical structures](https://www.cs.bham.ac.uk/~mhe/.talks/xii-pcc.pdf)