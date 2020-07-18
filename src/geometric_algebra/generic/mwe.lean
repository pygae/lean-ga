import ring_theory.algebra

universes u₀ u₁ u₂

namespace unbundled

class mwc
(R : Type u₀) [field R]
(V : Type u₁) [add_comm_group V] [vector_space R V]
(G : Type u₂) [ring G]
extends algebra R G
:=
(fᵣ : R →+* G := algebra_map R G)
(fᵥ : V →+ G)

section lemmas

variables (R : Type u₀) [field R]
variables (V : Type u₁) [add_comm_group V] [vector_space R V]
variables (G : Type u₂) [ring G]

variables (r₀ : R)
variables (v₀ : V)

#check mwc.fᵣ

#check mwc.fᵣ V

#check mwc.fᵣ V r₀

#check mwc.fᵥ

#check mwc.fᵥ R v₀

example (v : V) [mwc R V G] : ∃ r : R, 
  ((mwc.fᵥ R v) * (mwc.fᵥ R v)) = ((mwc.fᵥ R v) * (mwc.fᵥ R v) : G)
:= sorry

example (v : V) [mwc R V G] : ∃ r : R, 
  ((mwc.fᵥ R v) * (mwc.fᵥ R v)) = (mwc.fᵣ V r : G)
:= sorry

example [mwc R V G] : ∀ v : V, ∃ r : R, 
  ((mwc.fᵥ R v) * (mwc.fᵥ R v)) = ((mwc.fᵥ R v) * (mwc.fᵥ R v) : G)
:= sorry

example [mwc R V G] : ∀ v : V, ∃ r : R, 
  ((mwc.fᵥ R v) * (mwc.fᵥ R v)) = (mwc.fᵣ V r : G)
:= sorry

end lemmas

end unbundled

namespace V_bundled

class mwc
(R : Type u₀) [field R]
(G : Type u₂) [ring G]
extends algebra R G
:=
(V : Type u₁)
[V_acg : add_comm_group V]
[V_vs : vector_space R V]
(fᵣ : R →+* G := algebra_map R G)
(fᵥ : V →+ G)

section lemmas

variables (R : Type u₀) [field R]
variables (G : Type u₂) [ring G] [mwc R G]

variables (r₀ : R)
variables (v₀ : mwc.V R G)

-- variables {GA : mwc R G}

/-
V_bundled.mwc.fᵣ : Π {R : Type u₀} [_inst_1 : field R] {G : Type u₂} [_inst_2 : ring G] [c : mwc R G], R →+* G
-/
#check mwc.fᵣ

#check mwc.fᵣ r₀

/-
V_bundled.mwc.fᵥ : Π {R : Type u₀} [_inst_1 : field R] {G : Type u₂} [_inst_2 : ring G] [c : mwc R G], mwc.V R G →+ G

-/
#check mwc.fᵥ

/-
mwc.V : Π (R : Type u_2) [_inst_1 : field R] (G : Type u_4) [_inst_2 : ring G] [c : mwc R G], Type u_3
-/
#check mwc.V

#check mwc.V R G

#check mwc.fᵥ v₀

example : ∀ v : mwc.V R G, ∃ r : R,
  mwc.fᵣ r = (mwc.fᵣ r : G)
:= sorry

example : ∀ v : mwc.V R G, ∃ r : R,
  (mwc.fᵥ v) * (mwc.fᵥ v) = mwc.fᵣ r
:= sorry

example {GA : mwc R G} : ∀ v : GA.V, ∃ r : R,
  (mwc.fᵥ v) * (mwc.fᵥ v) = mwc.fᵣ r
:= sorry

end lemmas

end V_bundled

namespace VR_bundled

class mwc
(G : Type u₂) [ring G]
:=
(R : Type u₀)
[R_f : field R]
(V : Type u₁)
[V_acg : add_comm_group V]
[V_vs : vector_space R V]
(to_algebra : algebra R G)
(fᵣ : R →+* G := algebra_map R G)
(fᵥ : V →+ G)

section lemmas

variables (G : Type u₂) [ring G] [mwc G]

variables (r₀ : mwc.R G)
variables (v₀ : mwc.V G)

#check mwc.fᵣ

#check mwc.fᵣ r₀

#check mwc.fᵥ

#check mwc.V

#check mwc.V G

#check mwc.fᵥ v₀

example : ∀ v : mwc.V G, ∃ r : mwc.R G,
  (mwc.fᵥ v) * (mwc.fᵥ v) = mwc.fᵣ r
:= sorry

end lemmas

end VR_bundled