/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Topology.Algebra.Module.StrongTopology

/-!
#Continuity and Sesquilinear Maps

-/

section SeparateContinuity

variable {R R₁ R₂ R₃ M M₁ M₂ M₃ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}
variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] [CommSemiring R₂]
  [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M] [Module R M]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [TopologicalSpace M]

structure separateContinuity (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop where
  left : ∀ (x : M₁), Continuous (B x)
  right : ∀ (y : M₂), Continuous (B.flip y)

lemma separateContinuity_flip_iff {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    separateContinuity B.flip ↔ separateContinuity B  := by
  constructor
  · intro h
    constructor
    · intro x
      exact h.right _
    · intro y
      exact h.left _
  · intro h
    constructor
    · intro y
      exact h.right _
    · intro x
      exact h.left _

end SeparateContinuity

section Hypocontinuous

variable {E F G : Type*} {𝕜₁ 𝕜₂ 𝕜₃} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) (σ₂₃ : 𝕜₂ →+* 𝕜₃) (σ₁₃ : 𝕜₁ →+* 𝕜₃) [AddCommGroup E] [AddCommMonoid F]
  [AddCommGroup G] [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₃ G] [TopologicalSpace E]
  [TopologicalSpace F] [TopologicalSpace G] [ContinuousAdd E] [ContinuousConstSMul 𝕜₃ G]
--  [ContinuousAdd G]
-- TODO [ContinuousAdd G] is enough with
-- instance : AddCommMonoid (UniformConvergenceCLM σ₁₃ G 𝔖) := ContinuousLinearMap.addCommMonoid
variable [IsTopologicalAddGroup G]

variable (𝔖 : Set (Set E))

variable (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G)

#check F →ₛₗ[σ₂₃] E →ₛₗ[σ₁₃] G

#check (B.flip : F →ₛₗ[σ₂₃] E →ₛₗ[σ₁₃] G)

-- instancUniformConvergenceCLM.instModule

--instance : AddCommMonoid (E →SL[σ₁₃] G) := by exact ContinuousLinearMap.addCommMonoid

--instance : Module 𝕜₃ (E →SL[σ₁₃] G) := ContinuousLinearMap.module

--instance : AddCommMonoid (UniformConvergenceCLM σ₁₃ G 𝔖) := ContinuousLinearMap.addCommMonoid

-- I think these are the 𝔖-hypocontinuous maps (also need separate continuity?)
#check F →SL[σ₂₃] UniformConvergenceCLM σ₁₃ G 𝔖


end Hypocontinuous
