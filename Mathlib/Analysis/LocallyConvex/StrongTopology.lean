/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.SesquilinearMap

/-!
# Local convexity of the strong topology

In this file we prove that the strong topology on `E →L[ℝ] F` is locally convex provided that `F` is
locally convex.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## TODO

* Characterization in terms of seminorms

## Tags

locally convex, bounded convergence
-/


open Topology UniformConvergence

variable {R 𝕜₁ 𝕜₂ E F : Type*}

variable [AddCommGroup E] [TopologicalSpace E] [AddCommGroup F] [TopologicalSpace F]
  [IsTopologicalAddGroup F]

section General

namespace UniformConvergenceCLM

variable (R)
variable [Semiring R] [PartialOrder R]
variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

theorem locallyConvexSpace (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    LocallyConvexSpace R (UniformConvergenceCLM σ F 𝔖) := by
  apply LocallyConvexSpace.ofBasisZero _ _ _ _
    (UniformConvergenceCLM.hasBasis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
      (LocallyConvexSpace.convex_basis_zero R F)) _
  rintro ⟨S, V⟩ ⟨_, _, hVconvex⟩ f hf g hg a b ha hb hab x hx
  exact hVconvex (hf x hx) (hg x hx) ha hb hab

end UniformConvergenceCLM

end General

section BoundedSets

namespace ContinuousLinearMap

variable [Semiring R] [PartialOrder R]
variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

#check ContinuousLinearMap.topologicalSpace

instance : TopologicalSpace (E →SL[σ] F) := by exact topologicalSpace

instance instLocallyConvexSpace : LocallyConvexSpace R (E →SL[σ] F) :=
  UniformConvergenceCLM.locallyConvexSpace R _ ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)

end ContinuousLinearMap

end BoundedSets



-- Bilinear

namespace ContinuousLinearMap

section prod

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

variable [Semiring R] [PartialOrder R]
variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
variable [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₃ G]

variable [Module R E] [ContinuousConstSMul R E] [LocallyConvexSpace R E] [SMulCommClass 𝕜₁ R E]
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]
variable [Module R G] [ContinuousConstSMul R G] [LocallyConvexSpace R G] [SMulCommClass 𝕜₃ R G]

variable [ContinuousConstSMul 𝕜₃ G]

--variable (B : E × F →L[𝕜] G)

#check RingHom.prod

#check MonoidHom.prod

#check LinearMap.prod

#check LinearMap.llcomp

variable {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜₁ →+* 𝕜₃} -- [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

--variable (f : E →SL[σ₁₃] F →SL[σ₂₃] G)

variable (y : F)

instance : TopologicalSpace (F →SL[σ₂₃] G) := by exact instTopologicalSpace

variable (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (x : E) -- (h : Continuous (B x))

#check B x

#check ContinuousLinearMap.mk

#check ContinuousLinearMap.mk (B x) h



lemma sepcon1 (B : E →SL[σ₁₃] F →SL[σ₂₃] G) : separateContinuity B.toLinearMap₁₂ where
  left x := (B x).2
  right := by
    intro y
    sorry



def mkstp1 (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (h : separateContinuity B) : E →ₛₗ[σ₁₃] F →SL[σ₂₃] G where
  toFun x := ⟨B x, h.left x⟩
  map_add' _ _:= by
    simp only [map_add]
    rfl
  map_smul' _ _ := by
    simp only [LinearMap.map_smulₛₗ]
    rfl

omit [IsTopologicalAddGroup F] in
lemma mkstp_apply (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (h : separateContinuity B) (x : E) :
  mkstp1 B h x = B x := rfl

def mkContinuousOfSepCon (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G)
    (h : separateContinuity B) : E →SL[σ₁₃] F →SL[σ₂₃] G := ⟨mkstp1 B h, by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    refine continuous_iff_continuousAt.mpr ?_
    intro x

    --simp_rw [mkstp_apply]
    norm_cast
    simp [mkstp1, mkstp_apply]

    convert h.right _
    sorry
    sorry
    ⟩

#check separateContinuity



--def mk₂ (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (h : ∀ (y : F), Continuous (B.flip y)) :



lemma test1 (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) :
    separateContinuity B ↔ ∀ (y : F), Continuous (B.flip y) ∧ Continuous B := sorry



def l1 (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : (E × F) → G := fun (x, y) => f x y

-- Bourbaki TVS III.28-30 sufficient and necessary conditions for separate continuity




lemma c1 : Continuous (l1 f) where
  isOpen_preimage := by
    intro U hU
    sorry


#check (f : E × F → G)

variable (X : E × F) (K : 𝕜₁ × 𝕜₂)

#check K • X


--lemma p1 (B : E × F →L[𝕜] G) :

end prod





variable [Semiring R] [PartialOrder R]
variable {𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜₁ →+* 𝕜₃}

   {G : Type*} [TopologicalSpace G] [AddCommGroup G]
  --{M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄]
variable [Module 𝕜₁ E] --[Module 𝕜₁ M'₁]
  [Module 𝕜₂ F] [Module 𝕜₃ G]
variable [Module R E] [ContinuousConstSMul R E] [LocallyConvexSpace R E] [SMulCommClass 𝕜₁ R E]
variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]
variable [Module R G] [ContinuousConstSMul R G] [LocallyConvexSpace R G] [SMulCommClass 𝕜₃ R G]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (B : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G)

#check  Continuous B


variable (L : E →SL[σ₁₃] F →SL[σ₂₃] G)

#check (L : E × F → G)

lemma contprod : Continuous L := sorry


/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `LinearIsometryEquiv`, see
`ContinuousLinearMap.flipL`. -/
def flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
    ‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq <| by simp only [mul_right_comm]


end ContinuousLinearMap
