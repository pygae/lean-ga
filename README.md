lean-ga
=========

A work-in-progress formalization of Geometric Algebra (GA) in the [Lean formal proof verification system](https://leanprover-community.github.io/) and using its [Mathematical Library](https://github.com/leanprover-community/mathlib/).

Development Status
--------------------

Early. Currently it's only in the design phase and the infrastructure is being set up and experimented.

Formalization Goals
--------------------

1. Formalize Geometric Algebra in a generic way that
    - doesn't depend on data structures, not even canonical structures
    - contains only how the algebra works and its natural relations to other abstract mathematical structures by leveraging the power of Type Class in Lean 
    - is deeply rooted in its mathematical foundation while keeping its accessibility to common users
2. Formalize Geometry like PGA, CGA etc. based on the generic formalization
3. Verify the equivalence or explore the relations of various formalisms of Geometric Algebra
4. Verify the correctness and computational properties of various Geometric Algebra data structures and algorithms
5. Develops tactics and automations specific to Geometric Algebra using Lean's powerful metaprogramming framework
6. Formalize important or interesting applications of Geometric Algebra
7. Numerical GA Code generator for various programming languages with a rich set of options from various verified Geometric Algebra data structures and algorithms, inspired by https://github.com/vincentnozick/garamon and https://github.com/enkimute/ganja.js
8. Symbolic rewrite rule generator for Rule-based rewriting languages, e.g. https://github.com/JuliaSymbolics/SymbolicUtils.jl
9. Verify GA libraries (e.g. https://github.com/chakravala/Grassmann.jl , https://github.com/jeremyong/gal , https://github.com/RobinKa/tfga , to name a few interested but really challenging ones) by pluggable bridges with them, using tools/APIs summarized in https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Examples.20of.20communicating.20with.20Lean
10. Formalize Geometric Calculus

Project Structure
--------------------

```bash
# Github actions like https://github.com/leanprover-community/mathlib/blob/master/.github/workflows/build.yml
├── .github
# VSCode settings like https://github.com/leanprover-community/mathlib/blob/master/.vscode/settings.json              
├── .vscode
# Docs like https://github.com/leanprover-community/mathlib/tree/master/docs using https://github.com/leanprover-community/doc-gen and possibly https://github.com/leanprover-community/format_lean and https://github.com/leanprover-community/lean-client-python
# also docs like https://github.com/avigad/mathematics_in_lean_source
├── docs
# The accompanying paper like https://arxiv.org/abs/1910.09336 and https://arxiv.org/abs/1910.12320
# Will be written using https://manubot.org/
├── paper
# Scripts like https://github.com/leanprover-community/mathlib/blob/master/scripts/deploy_docs.sh
├── scripts
# Source
├── src
# The root of Geometric Algebra formalization
# Following the layout in mathlib e.g. https://github.com/leanprover-community/mathlib/tree/master/src/linear_algebra
│   ├── geometric_algebra
#           Goal 1
│   │   ├── generic
#           Goal 2
│   │   ├── geometry
#           Goal 3
│   │   ├── formalism
#           Goal 4
│   │   ├── data
│   │   ├── algorithm
#           Goal 5
│   │   ├── tactic
#           Goal 6
│   │   ├── application
#           Goal 7
│   │   ├── codegen
#           Goal 8
│   │   ├── rulegen
#           Goal 9
│   │   ├── libraries
#           Goal 10
│   │   ├── calculus
#           Experimental code
│   │   ├── _nursery
#           Deprecated code that was part of the formalization
│   │   └── _deprecated
# Potential changes to the other directories in mathlib
│   └── ...
# Tests like https://github.com/leanprover-community/mathlib/tree/master/test
└── test
```

Name of the Project
--------------------

Following the practice of https://leanprover-community.github.io/lean-perfectoid-spaces/ , the project should be named `lean-geometric-algebra`, but `lean-ga` is shorter and it sounds not bad.
