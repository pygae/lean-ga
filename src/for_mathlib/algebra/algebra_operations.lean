/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.algebra.operations
import algebra.algebra.subalgebra.basic

/-! # Lemmas for `algebra/algebra/operations.lean` -/

namespace submodule

variables {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A]

def one_eq_algebra_of_id_range : (1 : submodule R A) = (algebra.of_id R A).range.to_submodule :=
begin
  dunfold has_one.one,
  ext,
  simp [algebra.of_id_apply],
end

end submodule
