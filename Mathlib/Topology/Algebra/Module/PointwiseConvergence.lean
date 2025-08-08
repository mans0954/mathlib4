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


variable {E F G : Type*} {𝕜₁ 𝕜₂ 𝕜₃} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) (σ₂₃ : 𝕜₂ →+* 𝕜₃) (σ₁₃ : 𝕜₁ →+* 𝕜₃) [AddCommGroup E] [AddCommGroup F]
  [AddCommGroup G] [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₃ G] [TopologicalSpace E]
  [TopologicalSpace F] [TopologicalSpace G] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

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

#check LinearMap.applyₗ
