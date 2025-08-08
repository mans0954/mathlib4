/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Topology.Algebra.Module.StrongTopology

/-!
# Pointwise or simple convergence

-/


/-
Induced from the product topology

Works over Semirings and AddCommMonoid. Just needs `E` and `F` to be Topological Spaces
-/
section

variable {E F : Type*} {𝕜₁ 𝕜₂} [Semiring 𝕜₁] [Semiring 𝕜₂]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) [AddCommMonoid E] [AddCommMonoid F]
   [Module 𝕜₁ E] [Module 𝕜₂ F] [TopologicalSpace E] [TopologicalSpace F] [SMulCommClass 𝕜₂ 𝕜₂ F]

instance : TopologicalSpace (E →SL[σ₁₂] F) := TopologicalSpace.induced
  (fun T x => (LinearMap.id  (R := 𝕜₂) (M := E →ₛₗ[σ₁₂] F)) T x) Pi.topologicalSpace

end


/-
Use `UniformConvergenceCLM` with the singletons of `E`.

Definition of `UniformConvergenceCLM` requires `𝕜₁` `𝕜₂` to be normed fields
`E` and `F` need to be `AddCommGroup` (might be possible to relax this to `AddCommMonoid`?)
Also need `IsTopologicalAddGroup F` (might be able to relax to )

-/
section

variable {E F G : Type*} {𝕜₁ 𝕜₂ 𝕜₃} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) (σ₂₃ : 𝕜₂ →+* 𝕜₃) (σ₁₃ : 𝕜₁ →+* 𝕜₃) [AddCommGroup E] [AddCommGroup F]
  [AddCommGroup G] [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₃ G] [TopologicalSpace E]
  [TopologicalSpace F] [TopologicalSpace G]

#check UniformConvergenceCLM σ₁₂ F {{x} | (x : E)}

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

#check E →SL[σ₁₂] F

/-
This is the continuous version of `LinearMap.applyₗ`.
def apply' : E →SL[σ₁₂] (E →SL[σ₁₂] F) →L[𝕜₂] F :=
  flip (id 𝕜₂ (E →SL[σ₁₂] F))
-/

#check LinearMap.flip (LinearMap.id  (R := 𝕜₂) (M := E →ₛₗ[σ₁₂] F))

def apply' : E →ₛₗ[σ₁₂] (E →ₛₗ[σ₁₂] F) →ₗ[𝕜₂] F :=
  LinearMap.flip (LinearMap.id  (R := 𝕜₂) (M := E →ₛₗ[σ₁₂] F))

#check LinearMap.id (R := 𝕜₂) (M := E →SL[σ₁₂] F)

#check apply' σ₁₂

--#check (LinearMap.id (M := E →SL[σ₁₂] F)).flip

#check TopologicalSpace.induced (apply' σ₁₂)

instance : TopologicalSpace (E →SL[σ₁₂] F) := TopologicalSpace.induced
  (fun T x => (LinearMap.id  (R := 𝕜₂) (M := E →ₛₗ[σ₁₂] F)) T x) Pi.topologicalSpace

variable (𝔖 : Set (Set E))

#check {{x} | (x : E)}





lemma isInducing : Topology.IsInducing (fun (T : UniformConvergenceCLM σ₁₂ F {{x} | (x : E)}) x =>
  (LinearMap.id  (R := 𝕜₂) (M := E →ₛₗ[σ₁₂] F)) T x) where
  eq_induced := by
    ext U
    constructor
    · intro h
      simp_all only [LinearMap.id_coe, id_eq, LinearMap.coe_coe]
      sorry
    · intro h
      simp_all only [LinearMap.id_coe, id_eq, LinearMap.coe_coe]
      sorry


#check LinearMap.applyₗ

end
