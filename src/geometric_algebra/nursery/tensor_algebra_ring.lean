import geometric_algebra.nursery.tensor_algebra

namespace tensor_algebra

universes u v
variables (R : Type u) [comm_ring R]
variables (M : Type v) [add_comm_group M] [module R M]

-- from https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/semiring.2Balgebra.20.3D.3E.20ring/near/204968473
instance : ring (tensor_algebra R M) :=
{ neg := λ a, (algebra_map R _  $ -1) * a,
  add_left_neg := λ a,
  begin
    have : (algebra_map R _ 1) * a = a, by simp,
    conv_lhs { congr, skip, rw ←this}, clear this,
    change (algebra_map R _ (-1)) * a + _ = _,
    rw [←right_distrib,← (algebra_map R _).map_add (-1) 1],
    simp,
  end,
  ..show semiring _, by apply_instance }

end tensor_algebra