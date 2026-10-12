module

public import AcExtensionPrinciple.Interpolation.Uniform
public import AcExtensionPrinciple.Cylinder.Curve
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiability of regular cylinders

Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670.
The partial derivatives of r come from its characteristic primitives.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Interior off-axis points, used only for ordinary two-sided derivatives.
Paper `e1a0fd5`, lines 661–670. -/
@[expose] def late_cylinderInterior (ui : ℝ) : Set (ℝ × ℝ) :=
  {p | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < 0}

/-- The interior off-axis triangle is open. Paper `e1a0fd5`, lines 661–670. -/
theorem isOpen_late_cylinderInterior (ui : ℝ) : IsOpen (late_cylinderInterior ui) :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const))

/-- Interior points lie in the class domain. Paper `e1a0fd5`, lines 661–670. -/
theorem late_cylinderInterior_subset (ui : ℝ) : late_cylinderInterior ui ⊆ pastTriangle ui :=
  fun _ hp => ⟨hp.1.le, hp.2.1.trans hp.2.2, hp.2.1.le, hp.2.2.le⟩

/-- Scalar multiplication as a continuous linear map. Paper `e1a0fd5`,
`eq:cylinder-tangent`, calculus helper for lines 661–670. -/
@[expose] noncomputable def late_cylinderLinear (c : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ c

/-- Nonzero scalar multiplication is invertible. Paper `e1a0fd5`,
`eq:cylinder-tangent`, calculus helper for lines 661–670. -/
theorem late_cylinderLinear_invertible {c : ℝ} (hc : c ≠ 0) :
    (late_cylinderLinear c).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := late_cylinderLinear c⁻¹)
  · ext
    simp [late_cylinderLinear, hc]
  · ext
    simp [late_cylinderLinear, hc]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming radius partial derivative at an interior point.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_radius_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ late_cylinderInterior ui) :
    HasDerivAt (fun s => S.r s v) (S.nu u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hs := inSeg_subset_triangle (le_refl ui) (hdv.trans hp.2.2) hdv.le hp.2.2.le
  apply intervalPrimitive_hasDerivAt ⟨hp.1, hud⟩
    (continuous_in h.regularCenter.continuous_nu hs)
  intro x hx
  exact h.regularCenter.localBV.radius_in v ui x hx.1
    (inSeg_subset_triangle le_rfl (hx.2.trans_lt (hdv.trans hp.2.2))
      (hx.2.trans hdv.le) hp.2.2.le)

/-- r has a strict total derivative (ν,λ) away from the domain's edges.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_radius_hasStrictFDerivAt {p : ℝ × ℝ} (hp : p ∈ late_cylinderInterior ui) :
    HasStrictFDerivAt (fun p => S.r p.1 p.2)
      ((late_cylinderLinear (S.nu p.1 p.2)).coprod (late_cylinderLinear (S.lam p.1 p.2))) p := by
  have hn := (isOpen_late_cylinderInterior ui).mem_nhds hp
  apply hasStrictFDerivAt_uncurry_coprod (f := S.r)
    (f₁ := fun u v => late_cylinderLinear (S.nu u v))
    (f₂ := fun u v => late_cylinderLinear (S.lam u v))
  · filter_upwards [hn] with q hq
    exact (h.late_radius_hasDerivAt_in hq).hasFDerivAt
  · filter_upwards [hn] with q hq
    exact (h.acdatum_radius_hasDerivAt_out hq.1.le
      (hq.2.1.trans hq.2.2) hq.2.1 hq.2.2).hasFDerivAt
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      ((h.regularCenter.continuous_nu.mono (late_cylinderInterior_subset ui)).continuousAt hn)
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      ((h.regularCenter.continuous_lam.mono (late_cylinderInterior_subset ui)).continuousAt hn)

/-- At every interior cylinder point, a differentiable local radius-b graph exists.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_exists_local_cylinder {u v : ℝ} (hp : (u, v) ∈ late_cylinderInterior ui) :
    ∃ w : ℝ → ℝ, HasDerivAt w (-S.nu u v / S.lam u v) u ∧
      w u = v ∧ ∀ᶠ s in 𝓝 u, S.r s (w s) = S.r u v := by
  have hd := h.late_radius_hasStrictFDerivAt hp
  have hl := late_cylinderLinear_invertible
    (ne_of_gt (h.lam_pos (late_cylinderInterior_subset ui hp)))
  have hi : (((late_cylinderLinear (S.nu u v)).coprod (late_cylinderLinear (S.lam u v))) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by simpa using hl
  let w := hd.implicitFunctionOfProdDomain hi
  have hw := hd.hasStrictFDerivAt_implicitFunctionOfProdDomain hi
  have hw0 : w u = v :=
    (hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi).self_of_nhds.mp rfl
  refine ⟨w, ?_, hw0, hd.eventually_apply_implicitFunctionOfProdDomain hi⟩
  convert hw.hasFDerivAt.hasDerivAt using 1
  have hinv : (late_cylinderLinear (S.lam u v)).inverse (S.nu u v) =
      S.nu u v / S.lam u v := by
    apply hl.inverse_apply_eq.mpr
    simp only [late_cylinderLinear, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    exact (div_mul_cancel₀ _ (ne_of_gt (h.lam_pos (late_cylinderInterior_subset ui hp)))).symm
  simpa [ContinuousLinearMap.coprod_comp_inl, ContinuousLinearMap.coprod_comp_inr,
    ContinuousLinearMap.comp_apply, late_cylinderLinear, hinv, neg_div] using hinv.symm

/-- The canonical cylinder has the stated positive tangent at every interior ray.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_cylinderV_hasDerivAt {b u : ℝ} (hb : 0 < b)
    (hu : u ∈ cylinderDomain ui b S) (hui : ui < u) :
    HasDerivAt (cylinderV h b)
      (-S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u)) u := by
  have hv := h.cylinderV_spec hb hu
  have hp : (u, cylinderV h b u) ∈ late_cylinderInterior ui := ⟨hui, hv.1⟩
  obtain ⟨w, hd, hw, he⟩ := h.late_exists_local_cylinder hp
  have ht : Tendsto (fun s => (s, w s)) (𝓝 u) (𝓝 (u, cylinderV h b u)) := by
    simpa only [hw, id_eq] using tendsto_id.prodMk_nhds hd.continuousAt
  have hm := ht.eventually ((isOpen_late_cylinderInterior ui).mem_nhds hp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hm, he] with s hs heq
  have hr : S.r s (w s) = b := heq.trans hv.2
  have hsD : s ∈ cylinderDomain ui b S := by
    refine ⟨hs.1.le, hs.2.1.trans hs.2.2, ?_⟩
    rw [← hr]
    exact h.radius_strictMono hs.1.le (hs.2.1.trans hs.2.2)
      ⟨hs.2.1.le, hs.2.2.le⟩ ⟨(hs.2.1.trans hs.2.2).le, le_rfl⟩ hs.2.2
  exact h.cylinderV_eq hb hsD hs.2 hr

/-- The cylinder tangent is positive. Paper `e1a0fd5`, `eq:cylinder-tangent`. -/
theorem late_cylinderV_tangent_pos {b u : ℝ} (hb : 0 < b)
    (hu : u ∈ cylinderDomain ui b S) :
    0 < -S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u) :=
  div_pos (neg_pos.mpr (h.nu_neg (h.cylinder_mem hb hu)))
    (h.lam_pos (h.cylinder_mem hb hu))

/-- The canonical cylinder is continuous on every interval strictly after ui.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_cylinderV_continuousOn {b a0 a1 : ℝ} (hb : 0 < b) (ha : ui < a0)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ContinuousOn (cylinderV h b) (Icc a0 a1) := by
  intro u hu
  exact (h.late_cylinderV_hasDerivAt hb (hI hu) (ha.trans_le hu.1)).continuousAt.continuousWithinAt

/-- The cylinder tangent is continuous on regular compact intervals after ui.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_cylinderV_tangent_continuousOn {b a0 a1 : ℝ} (hb : 0 < b) (ha : ui < a0)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ContinuousOn (fun u => -S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u))
      (Icc a0 a1) := by
  have hc := continuousOn_id.prodMk (h.late_cylinderV_continuousOn hb ha hI)
  have hm : MapsTo (fun u => (u, cylinderV h b u)) (Icc a0 a1) (pastTriangle ui) :=
    fun u hu => h.cylinder_mem hb (hI hu)
  exact ((h.regularCenter.continuous_nu.comp hc hm).neg).div
    (h.regularCenter.continuous_lam.comp hc hm)
    (fun u hu => ne_of_gt (h.lam_pos (hm hu)))

/-- The canonical cylinder is C¹ on every nondegenerate compact regular interval after ui.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_cylinderV_contDiffOn {b a0 a1 : ℝ} (hb : 0 < b) (ha : ui < a0)
    (hab : a0 < a1) (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ContDiffOn ℝ 1 (cylinderV h b) (Icc a0 a1) := by
  have hd (u : ℝ) (hu : u ∈ Icc a0 a1) :=
    h.late_cylinderV_hasDerivAt hb (hI hu) (ha.trans_le hu.1)
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)]
  refine ⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt, ?_⟩
  apply (h.late_cylinderV_tangent_continuousOn hb ha hI).congr
  intro u hu
  exact (hd u hu).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hab) u hu)

/-- Compact regular cylinders are Lipschitz, so their monotone coordinate preserves AC data.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670, 731–737. -/
theorem late_cylinderV_exists_lipschitzOnWith {b a0 a1 : ℝ} (hb : 0 < b) (ha : ui < a0)
    (hab : a0 < a1) (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ∃ K : NNReal, LipschitzOnWith K (cylinderV h b) (Icc a0 a1) :=
  (h.late_cylinderV_contDiffOn hb ha hab hI).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc

/-- The cylinder graph is strictly increasing on each compact regular interval after ui.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem late_cylinderV_strictMonoOn {b a0 a1 : ℝ} (hb : 0 < b) (ha : ui < a0)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    StrictMonoOn (cylinderV h b) (Icc a0 a1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (h.late_cylinderV_continuousOn hb ha hI)
  intro u hu
  have huC : u ∈ Icc a0 a1 := interior_subset hu
  rw [(h.late_cylinderV_hasDerivAt hb (hI huC) (ha.trans_le huC.1)).deriv]
  exact h.late_cylinderV_tangent_pos hb (hI huC)

end StandingFull

end AcExtensionPrinciple

end
