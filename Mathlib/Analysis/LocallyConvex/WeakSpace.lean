/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.AbsConvex

/-! # Closures of convex sets in locally convex spaces

This file contains the standard result that if `E` is a vector space with two locally convex
topologies, then the closure of a convex set is the same in either topology, provided they have the
same collection of continuous linear functionals. In particular, the weak closure of a convex set
in a locally convex space coincides with the closure in the original topology.
Of course, we phrase this in terms of linear maps between locally convex spaces, rather than
creating two separate topologies on the same space.
-/

variable {𝕜 E F : Type*}
variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

open ComplexOrder
lemma convex_real_of_convex_RCLike {s : Set E} (hs : Convex 𝕜 s) : Convex ℝ s := by
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  have e1 : (RCLike.ofReal (K := 𝕜) a) • u + (RCLike.ofReal (K := 𝕜) b) • v = a • u + b • v := by
    rw [algebraMap_smul, algebraMap_smul]
  rw [← e1]
  apply hs hu hv (RCLike.ofReal_nonneg.mpr ha) (RCLike.ofReal_nonneg.mpr hb)
  rw [← RCLike.ofReal_add, hab, RCLike.ofReal_one]

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]
variable [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [LocallyConvexSpace ℝ F]

/-
open ComplexOrder in
theorem toWeakSpace_closedAbsConvexHull {s : Set E} :
    (toWeakSpace 𝕜 E) '' (closedConvexHull 𝕜 s) =
    closedConvexHull 𝕜 (toWeakSpace 𝕜 E '' s) := by
  rw [le_antisymm_iff]
  constructor
  · rw [closedConvexHull_eq_closure_convexHull]
    rw [closedConvexHull_eq_closure_convexHull]
    apply (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    intro x hx
    simp at hx
    obtain ⟨w, hw1, hw2⟩ := hx
    sorry
  · intro x hx
    --apply (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    --simp only [toWeakSpaceCLM_eq_toWeakSpace, Set.mem_image]
    sorry


variable (𝕜) in
theorem Convex.toWeakSpace_closure' {s : Set E} (hs : Convex ℝ s) :
    (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E '' s) := by
  --apply le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure


  rw [le_antisymm_iff]
  constructor
  · apply (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
  · sorry

    sorry
-/

variable (𝕜) in
/-- If `E` is a locally convex space over `𝕜` (with `RCLike 𝕜`), and `s : Set E` is `ℝ`-convex, then
the closure of `s` and the weak closure of `s` coincide. More precisely, the topological closure
commutes with `toWeakSpace 𝕜 E`.

This holds more generally for any linear equivalence `e : E ≃ₗ[𝕜] F` between locally convex spaces
such that precomposition with `e` and `e.symm` preserves continuity of linear functionals. See
`LinearEquiv.image_closure_of_convex`. -/
theorem Convex.toWeakSpace_closure {s : Set E} (hs : Convex ℝ s) :
    (toWeakSpace 𝕜 E) '' (closure s) = closure (toWeakSpace 𝕜 E '' s) := by
  refine le_antisymm (map_continuous <| toWeakSpaceCLM 𝕜 E).continuousOn.image_closure
    (Set.compl_subset_compl.mp fun x hx ↦ ?_)
  obtain ⟨x, -, rfl⟩ := (toWeakSpace 𝕜 E).toEquiv.image_compl (closure s) |>.symm.subset hx
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨f, u, hus, hux⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    hs.closure isClosed_closure (by simpa using hx)
  let f' : StrongDual 𝕜 (WeakSpace 𝕜 E) :=
    { toLinearMap := (f : E →ₗ[𝕜] 𝕜).comp ((toWeakSpace 𝕜 E).symm : WeakSpace 𝕜 E →ₗ[𝕜] E)
      cont := WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip _ }
  have hux' : u < RCLike.reCLM.comp (f'.restrictScalars ℝ) (toWeakSpace 𝕜 E x) := by simpa [f']
  have hus' : closure (toWeakSpace 𝕜 E '' s) ⊆
      {y | RCLike.reCLM.comp (f'.restrictScalars ℝ) y ≤ u} := by
    refine closure_minimal ?_ <| isClosed_le (by fun_prop) (by fun_prop)
    rintro - ⟨y, hy, rfl⟩
    simpa [f'] using (hus y <| subset_closure hy).le
  exact (hux'.not_ge <| hus' ·)

--#check Convex.convex_isRCLikeNormedField
/-
open ComplexOrder
lemma test_star_convex {s : Set E} (x : E) (hs : StarConvex 𝕜 x s) : StarConvex ℝ x s := by
  intro y hy a b ha hb hab
  rw [StarConvex] at hs
  sorry
-/




/-
open ComplexOrder
#check LinearMap.image_convexHull (toWeakSpace 𝕜 E).toLinearMap

instance : ContinuousSMul 𝕜 E := by (expose_names; exact inst_11)

instance : ContinuousSMul 𝕜 (WeakSpace 𝕜 E) where
  continuous_smul := by
    apply WeakBilin.continuous_of_continuous_eval
    intro y
    simp_all only [map_smul, LinearMap.smul_apply, LinearMap.flip_apply]
    simp_rw [topDualPairing_apply]
    simp_rw [← LinearMap.smul_apply]
    --apply ContinuousSMul.continuous_smul
    --apply WeakBilin.eval_continuous
    sorry


instance : ContinuousConstSMul 𝕜 E := ContinuousSMul.continuousConstSMul

instance : ContinuousConstSMul 𝕜 (WeakSpace 𝕜 E) := by
  apply ContinuousSMul.continuousConstSMul
-/


-- [ContinuousSMul 𝕜 𝕜]
open ComplexOrder in
theorem toWeakSpace_closedAbsConvexHull [ContinuousSMul 𝕜 𝕜] {s : Set E} :
    (toWeakSpace 𝕜 E) '' (closedConvexHull 𝕜 s) =
    closedConvexHull 𝕜 (toWeakSpace 𝕜 E '' s) := by
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜)]
  rw [Convex.toWeakSpace_closure _ (convex_real_of_convex_RCLike (𝕜 := 𝕜) (convex_convexHull 𝕜 s))]
  have : ContinuousSMul 𝕜 (WeakSpace 𝕜 E) := WeakBilin.instContinuousSMul _
  rw [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜)]
  congr
  refine LinearMap.image_convexHull (toWeakSpace 𝕜 E).toLinearMap s

/-
theorem LinearMap.image_closedAbsConvexHull {s : Set E} (e : E →ₗ[𝕜] F)
    (he : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f)) :
    e '' (closedAbsConvexHull ℝ s) ⊆ closedAbsConvexHull ℝ (e '' s) := by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex ℝ (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective, h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toWeakSpace_closure 𝕜, LinearEquiv.symm_apply_apply]
      using he'.continuousOn.image_closure (s := toWeakSpace 𝕜 E '' s)
  exact WeakBilin.continuous_of_continuous_eval _ fun f ↦
    WeakBilin.eval_continuous _ { toLinearMap := e.dualMap f : StrongDual 𝕜 E }
-/

/-- If `e : E →ₗ[𝕜] F` is a linear map between locally convex spaces, and `f ∘ e` is continuous
for every continuous linear functional `f : StrongDual 𝕜 F`, then `e` commutes with the closure on
convex sets. -/
theorem LinearMap.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E →ₗ[𝕜] F)
    (he : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f)) :
    e '' (closure s) ⊆ closure (e '' s) := by
  suffices he' : Continuous (toWeakSpace 𝕜 F <| e <| (toWeakSpace 𝕜 E).symm ·) by
    have h_convex : Convex ℝ (e '' s) := hs.linear_image (F := F) e
    rw [← Set.image_subset_image_iff (toWeakSpace 𝕜 F).injective, h_convex.toWeakSpace_closure 𝕜]
    simpa only [Set.image_image, ← hs.toWeakSpace_closure 𝕜, LinearEquiv.symm_apply_apply]
      using he'.continuousOn.image_closure (s := toWeakSpace 𝕜 E '' s)
  exact WeakBilin.continuous_of_continuous_eval _ fun f ↦
    WeakBilin.eval_continuous _ { toLinearMap := e.dualMap f : StrongDual 𝕜 E }

/-- If `e` is a linear isomorphism between two locally convex spaces, and `e` induces (via
precomposition) an isomorphism between their continuous duals, then `e` commutes with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeakSpace_closure`. -/
theorem LinearEquiv.image_closure_of_convex {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (he₁ : ∀ f : StrongDual 𝕜 F, Continuous (e.dualMap f))
    (he₂ : ∀ f : StrongDual 𝕜 E, Continuous (e.symm.dualMap f)) :
    e '' (closure s) = closure (e '' s) := by
  refine le_antisymm ((e : E →ₗ[𝕜] F).image_closure_of_convex hs he₁) ?_
  simp only [Set.le_eq_subset, ← Set.image_subset_image_iff e.symm.injective]
  simpa [Set.image_image]
    using (e.symm : F →ₗ[𝕜] E).image_closure_of_convex (hs.linear_image (e : E →ₗ[𝕜] F)) he₂

/-- If `e` is a linear isomorphism between two locally convex spaces, and `e` induces (via
precomposition) an isomorphism between their continuous duals, then `e` commutes with the closure
on convex sets.

The hypotheses hold automatically for `e := toWeakSpace 𝕜 E`, see `Convex.toWeakSpace_closure`. -/
theorem LinearEquiv.image_closure_of_convex' {s : Set E} (hs : Convex ℝ s) (e : E ≃ₗ[𝕜] F)
    (e_dual : StrongDual 𝕜 F ≃ StrongDual 𝕜 E)
    (he : ∀ f : StrongDual 𝕜 F, (e_dual f : E →ₗ[𝕜] 𝕜) = e.dualMap f) :
    e '' (closure s) = closure (e '' s) := by
  have he' (f : StrongDual 𝕜 E) : (e_dual.symm f : F →ₗ[𝕜] 𝕜) = e.symm.dualMap f := by
    simp only [DFunLike.ext'_iff, ContinuousLinearMap.coe_coe] at he ⊢
    have (g : StrongDual 𝕜 E) : ⇑g = e_dual.symm g ∘ e := by
      have := he _ ▸ congr(⇑$(e_dual.apply_symm_apply g)).symm
      simpa
    ext x
    conv_rhs => rw [LinearEquiv.dualMap_apply, ContinuousLinearMap.coe_coe, this]
    simp
  refine e.image_closure_of_convex hs ?_ ?_
  · simpa [← he] using fun f ↦ map_continuous (e_dual f)
  · simpa [← he'] using fun f ↦ map_continuous (e_dual.symm f)
