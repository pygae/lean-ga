/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.clifford_algebra.fold
import linear_algebra.bilinear_form
import linear_algebra.tensor_product
import linear_algebra.prod

/-!
# Recursive computation rules

## Main definitions

-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]
variables {N : Type u3} [add_comm_group N] [module R N]
variables (Q : quadratic_form R M)

namespace clifford_algebra

end clifford_algebra
