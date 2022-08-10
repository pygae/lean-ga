lean-ga
=======

[![Gitpod ready-to-code](https://img.shields.io/badge/Gitpod-ready--to--code-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/pygae/lean-ga)
[![arXiv](https://img.shields.io/badge/arXiv-2110.03551-b31b1b.svg)](https://arxiv.org/abs/2110.03551)
[![DOI](https://zenodo.org/badge/doi/10.1007/s00006-021-01164-1.svg)](http://dx.doi.org/10.1007/s00006-021-01164-1)

A partial formalization of Geometric Algebra (GA) in the [Lean formal proof verification system](https://github.com/leanprover-community/lean) and using its [Mathematical Library](https://github.com/leanprover-community/mathlib/).

A description of the foundations of this work is published as [Formalizing Geometric Algebra in Lean](https://link.springer.com/article/10.1007/s00006-021-01164-1) in _Advances in Applied Clifford Algebras_ (note that the web version has been horrendously typeset by the publisher, but the PDF version is readable). The code in this repository has evolved since that publication to keep up with changes to mathlib.
We presented an early version of this at ICCA 2020 ([slides](https://pygae.github.io/lean-ga/ICCA2020)).

A semi-interactive viewer for the contents of this project can be found at https://pygae.github.io/lean-ga-docs/.
Of particular interest are:

* Parts of mathlib contributed as part of this work. These used to live in this repository, but have graduated to mathlib itself. The links below go to the precise version of mathlib `lean-ga` uses, rather than to the latest mathlib docs.
  * [`clifford_algebra`](https://pygae.github.io/lean-ga-docs/find/clifford_algebra)
    * [`clifford_algebra_ring.equiv`](https://pygae.github.io/lean-ga-docs/find/clifford_algebra_ring.equiv): the real numbers have an isomorphic clifford algebra.
    * [`clifford_algebra_complex.equiv`](https://pygae.github.io/lean-ga-docs/find/clifford_algebra_complex.equiv): the complex numbers have an isomorphic clifford algebra.
    * [`clifford_algebra_quaternion.equiv`](https://pygae.github.io/lean-ga-docs/find/clifford_algebra_quaternion.equiv): the quaternion numbers have an isomorphic clifford algebra.
    * [`clifford_algebra.as_exterior`](https://pygae.github.io/lean-ga-docs/find/clifford_algebra.as_exterior): the exterior algebra has an isomorphic clifford algebra
  * [`exterior_algebra`](https://pygae.github.io/lean-ga-docs/find/exterior_algebra)
  * [`alternating_map`](https://pygae.github.io/lean-ga-docs/find/alternating_map)
* Translations of other formalizations:
  * [`geometric_algebra/translations/hol_light.lean`](https://pygae.github.io/lean-ga-docs/geometric_algebra/translations/hol_light.html)
  * [`geometric_algebra/translations/ida.lean`](https://pygae.github.io/lean-ga-docs/geometric_algebra/translations/ida.html)
  * [`geometric_algebra/translations/laurents.lean`](https://pygae.github.io/lean-ga-docs/geometric_algebra/translations/laurents.html)
* Additional API on top of the mathlib `clifford_algebra`:
  * [`geometric_algebra/from_mathlib/versors.lean`](https://pygae.github.io/lean-ga-docs/geometric_algebra/from_mathlib/versors.html), a formalization of versors
  * [`geometric_algebra/from_mathlib/concrete/cga.lean`](https://pygae.github.io/lean-ga-docs/geometric_algebra/from_mathlib/concrete/cga.html), a formalization of CGA

To get the full experience of using lean-ga without having to install lean, use the GitPod link at the top of this readme.
Wait for the command in the console to finish, then open one of the files referenced above, and wait for compilation to finish (the orange bars to vanish).
At this point, you can move the cursor around to view the proof state, and try adding new statements to the file using our definitions.

See [this visualization](https://eric-wieser.github.io/mathlib-import-graph/?docs_url=https%3A%2F%2Fpygae.github.io%2Flean-ga-docs%2F) to see which parts of Mathlib are used in this formalization (directly or indirectly).

Update for [ICACGA](https://icacga.org/)
----------------------------------------
This repository has been updated to contain some of the examples in the paper _"Computing with the universal properties of the Clifford algebra and the even subalgebra"_, submitted to the ICACGA conference.
In turn, that paper contains permalinks that lead back to this repository.
Many of the examples in that paper are already in mathlib.

Contributing
------------

We welcome contributions, especially those in the areas outlined in the Future Work section of our paper. In some cases though, your contribution may well be better directed at mathlib itself, especially if it only depends on the parts of our work that have already been integrated into Mathlib.

Project Structure
-----------------

This project is configured for use with [`leanproject`](https://leanprover-community.github.io/leanproject.html), and such can be downloaded with `leanproject get pygae/lean-ga`.
The Lean source files can all be found in the `src` directory, which is structured as follows.

* [`src/for_mathlib`](https://github.com/pygae/lean-ga/tree/master/src/for_mathlib): non-GA formalizations intended for contribution to mathlib
* [`src/geometric_algebra`](https://github.com/pygae/lean-ga/tree/master/src/geometric_algebra)
  * [`nursury`](https://github.com/pygae/lean-ga/tree/master/src/geometric_algebra/nursery): various experiments at formalizations approaches
  * [`translations`](https://github.com/pygae/lean-ga/tree/master/src/geometric_algebra/translations): partial translations of formalizations in other languages
  * [`from_mathlib`](https://github.com/pygae/lean-ga/tree/master/src/geometric_algebra/from_mathlib): The core of this formalization, building on top of the `clifford_algebra` contributed to Mathlib

Additionally, there are some miscellaneous resources in [`docs/misc`](https://github.com/pygae/lean-ga/tree/master/docs/misc), which contain a mixture of links to and excepts from related work, and some initial design ideas and goals.

Naming
------

There is little precedent for naming third-party Lean libraries; we mirror the choice made by [lean-perfectoid-spaces](https://leanprover-community.github.io/lean-perfectoid-spaces/) by prefixing the repo name with `lean-`, and use `ga` to abbreviate `geometric-algebra`.
