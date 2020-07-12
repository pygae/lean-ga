# Rethinking the Design of Mathematical Theory Development in Lean

It turns out that we must have a design template in mind in order to carry on further designing of GA in Lean. This document will address this issue.

## Key Insight from Euclidean Geometry

Taking a step back, let's go back to geometry and look at https://github.com/vaibhavkarve/leanteach2020/blob/master/src/euclid.lean .

What's a point? How do we tell this concept to the computer? Do we draw a point? Or do we went to analytic geometry and give it a coordinate? It turns out we don't need to do either, the former is infeasible and the latter is the worst idea in formalizing.

```lean
constant Point : Type
```

How about a line? Same.

```lean
constant Line : Type
```

How about the relations between points and lines?

```lean
constant lies_on : Point → Line → Prop
constant between : Point → Point → Point → Prop  -- (between a b c) means "b is in between a and c"
constant congruent {A : Type} : A → A → Prop
constant distance : Point → Point → ℝ
```

How about axioms?

```lean
axiom distance_not_neg {p1 p2 : Point} : 0 ≤ distance p1 p2
axiom distance_pos {p1 p2 : Point} : p1 ≠ p2 ↔ 0 < distance p1 p2
```

And this keeps on and on. Then we have a lot of lemmas and theorems and we still don't need to know what exactly a point is, we don't even need to know how to compute a distance.

That's it. We don't need concrete types or computibility to reason about them. The semantic can end with their names and we don't need to know more underneath.

This is the key insight one must have before formalizing a piece of mathematics.

## Compatibility with mathlib

A geometric product "contains" an inner product and an exterior product (or wedge product).

They're established mathematic. There's already inner product space in mathlib and there would definitely be Grassmann Algebra in mathlib one day. And obviously we can't escape the general Clifford Algebra too.

We must maintain compatibility with them, at least don't conflict with their existence.

It's not a duplication. The development of mathlib is driven by professional mathematitians, they struggle for math generity but we're working at an abstraction level close to applications.

We want to stand on such shoulders but we want good capsulation so that we don't want to worry about more abstract concepts and some too general cases. This would definitely leak, it might not be obvious in definitions but it would be very clear when you're proving something. For example, you have to deal with lattice and finsupp when proving things about linear algebra, and that should not be.

## Operators

We start with has_* that have absolutely no axioms with them, they don't have any properties and any behaviors. It's almost just a name. And we associate notations with them.

Just like in https://github.com/leanprover-community/lean/blob/master/library/init/core.lean#L321 

```lean
class has_mul      (α : Type u) := (mul : α → α → α)
```

we could just:

```lean
class has_wedge (α : Type u) := (wedge : α → α → α)
class has_inner (α : Type u) := (inner : α → α → α)
```

The latter presumably is already in mathlib and has a lot of structures and properties associated with it. We'll deal with that later.

As for geometric product, I'm thinking about the following short name instead of `geomprod`, `gp` etc.:

```
class has_gmul (α : Type u) := (gmul : α → α → α)
```

## Notations

Now we assoc notations with them:

```lean
-- \circ
infix ∘ := has_gmul.gmul
-- \wedge
infix ∧ := has_wedge.wedge
-- \cdot
infix ⋅ := has_inner.inner
```

We'll always use `local` notations waiting for to be `open_locale`ed. I expect conflicts with notations in mathlib and using this to avoid the conflicts as long as possible.

> TODO: describe how to use them even when there's a confliction.

## Defining without defining

There're really millions of products defined in GA and they're based on geometric product. But the definition might not be the most effient one or the most intuitive one.

So instead of using `def`, we should make these products just a product with a Prop assering that they're equal to the definition based on gp and let the implementation prove it when intantiate the instance.

```lean
class has_ga_wedge (α : Type u) extends has_wedge :=
(defeq : ∀ a b : α, a ∧ b = (a ∘ b - b ∘ a) / 2)
```

The above ignore the fact this only works on vectors instead of multivectors.

So the true story is that we should define `has_sym_mul` and `has_asym_mul` first.

## The complication with mul

mul group diamond

C wrong

## ga extends has_gmul

## ga vs mv

## the standard template

import universe open variables

class with parameter

bundle

prio

marker forgetful_to

directory structure

## defs and lemmas

contains no lemma except for ... see groups/defs.lean

recover the usual for demo but never use them

## R V are not G0 G1

## G is vector space

## linear map

no `:G` or `coe`

## vector_contractible

non-metric

quadratic form?

functional?

induced topology

## attr

## universal algebra

## what to inherit and forget?

## Clifford and Grassmann

## graded comes later

