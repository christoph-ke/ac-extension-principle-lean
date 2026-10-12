module

public import AcExtensionPrinciple.Main.AssemblyData
public import AcExtensionPrinciple.Gauge.Gluing

/-!
# Compact terminal bounds and the final BV consequences

Paper `e1a0fd5`, `equations.tex` `eq:terminal-bv-bound`, lines 1439–1445.
The earlier segment is controlled directly by the standing class. The final
two derivative bounds follow from the three primary terminal bounds.
-/

public section

namespace AcExtensionPrinciple

open Set
open scoped ENNReal

/-- Negation preserves BV of a real terminal field.
Paper `e1a0fd5`, `eq:terminal-bv-bound`, lines 1439–1445. -/
theorem terminal_boundedVariation_neg {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) : BoundedVariationOn (fun x => -f x) s := by
  change eVariationOn (fun x => -f x) s ≠ ⊤
  have he : (fun x => -f x) = (fun x => (-1 : ℝ) * f x) := by funext x; ring
  rw [he, variation_const_mul]
  simpa using (show eVariationOn f s ≠ ⊤ from hf)

/-- Logarithm on a positive half-line preserves bounded variation.
Paper `e1a0fd5`, `eq:terminal-bv-bound`, lines 1439–1445. -/
theorem terminal_boundedVariation_log_of_lower {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hc : 0 < c) (hb : ∀ x ∈ s, c ≤ f x) (hBV : BoundedVariationOn f s) :
    BoundedVariationOn (fun x => Real.log (f x)) s := by
  let C : NNReal := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  have hLip : LipschitzOnWith C Real.log (Ici c) := by
    apply (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (Real.hasDerivAt_log (ne_of_gt (hc.trans_le hx))).hasDerivWithinAt)
    intro x hx
    change ‖x⁻¹‖₊ ≤ C
    apply NNReal.coe_le_coe.mp
    change ‖x⁻¹‖ ≤ c⁻¹
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hc.trans_le hx)]
    exact inv_anti₀ hc hx
  exact hLip.comp_boundedVariationOn hb hBV

/-- The earlier compact terminal segment has all five required BV bounds.
Paper `e1a0fd5`, `eq:terminal-bv-bound`, lines 1441–1445. -/
theorem StandingFull.terminal_compact_bv {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) :
    BoundedVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Icc ui ū) ∧
    BoundedVariationOn (fun u => S.phi u 0) (Icc ui ū) ∧
    BoundedVariationOn (fun u => Real.log (-S.nu u 0)) (Icc ui ū) ∧
    BoundedVariationOn (fun u => S.nu u 0) (Icc ui ū) ∧
    BoundedVariationOn (fun u => S.dupsi u 0) (Icc ui ū) := by
  have hs : inSeg 0 ui ū ⊆ pastTriangle ui :=
    inSeg_subset_triangle le_rfl hū.2 hū.2.le le_rfl
  rcases h.regularCenter.localBV.expansion_variation (inSeg 0 ui ū)
    (isCompact_Icc.prod isCompact_singleton) hs with ⟨Cν, _, hνin⟩
  have hnuBV : BoundedVariationOn (fun u => S.nu u 0) (Icc ui ū) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hνin 0 ui ū hū.1.le (Subset.refl _))
  obtain ⟨c, hc, hcb⟩ : ∃ c, 0 < c ∧ ∀ u ∈ Icc ui ū, c ≤ -S.nu u 0 := by
    obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hū.1.le)
      (continuous_in h.regularCenter.continuous_nu hs).neg
    exact ⟨-S.nu x 0, neg_pos.mpr (h.nu_neg (p := (x, 0)) ⟨hx.1, hx.2.trans_lt hū.2,
      (hx.2.trans hū.2.le), le_rfl⟩), fun u hu => hmin hu⟩
  have hnegBV := terminal_boundedVariation_neg hnuBV
  have hi := boundedVariation_inv_of_lower hc hcb hnegBV
  have hlog := terminal_boundedVariation_log_of_lower hc hcb hnegBV
  rcases h.regularCenter.localBV.psi_variation (inSeg 0 ui ū)
    (isCompact_Icc.prod isCompact_singleton) hs with ⟨C, _, hdu⟩
  have hduBV : BoundedVariationOn (fun u => S.dupsi u 0) (Icc ui ū) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdu 0 ui ū hū.1.le (Subset.refl _))
  rcases h.regularCenter.localBV.scalar_ac_variation (inSeg 0 ui ū)
    (isCompact_Icc.prod isCompact_singleton) hs with ⟨_, _, hphi⟩
  have hphiBV := (hphi 0 ui ū hū.1.le (Subset.refl _)).1.boundedVariationOn
  have hinvBV : BoundedVariationOn (fun u => (S.nu u 0)⁻¹) (Icc ui ū) := by
    have he : (fun u => (S.nu u 0)⁻¹) = (fun u => -((-S.nu u 0)⁻¹)) := by
      funext u
      simp
    rw [he]
    exact terminal_boundedVariation_neg hi
  refine ⟨?_, ?_, ?_, hnuBV, hduBV⟩
  · simpa only [div_eq_mul_inv] using hduBV.fun_mul hinvBV
  · simpa only [uIcc_of_le hū.1.le] using hphiBV
  · exact hlog

/-- Exact variation additivity between the earlier compact segment and the
late half-open terminal segment. Paper `e1a0fd5`, lines 1441–1443. -/
theorem terminal_variation_add (f : ℝ → ℝ) {ui ū : ℝ} (hū : ū ∈ Ioo ui 0) :
    eVariationOn f (Ico ui 0) =
      eVariationOn f (Icc ui ū) + eVariationOn f (Ico ū 0) := by
  rw [← Icc_union_Ico_eq_Ico hū.1.le hū.2]
  exact eVariationOn.union f ⟨⟨hū.1.le, le_rfl⟩, fun _ hx => hx.2⟩
    ⟨⟨le_rfl, hū.2⟩, fun _ hx => hx.1⟩

/-- The log Jacobian in the terminal expansion law is BV on the complete
selected cone. This follows directly from the original class.
Paper `e1a0fd5`, `eq:terminal-expansion-gauge`, lines 1435–1443;
Luk–Oh Definition 2.1(2), with the standing local AC refinement. -/
theorem StandingFull.selected_log_jacobian_bv {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) :
    BoundedVariationOn (fun u => Real.log (2 * S.lam ū u)) (Icc ū 0) := by
  have hs : outSeg ū ū 0 ⊆ pastTriangle ui :=
    outSeg_subset_triangle hū.1.le hū.2 le_rfl le_rfl
  have hl := h.regularCenter.ac_lam_out ū ū 0 hū.2.le hs
  have htwo : AbsolutelyContinuousOnInterval (fun _ : ℝ => (2 : ℝ)) ū 0 :=
    (LipschitzWith.const 2).lipschitzOnWith.absolutelyContinuousOnInterval
  have hlog := positive_ac_log (htwo.fun_mul hl) (fun u hu => by
    rw [uIcc_of_le hū.2.le] at hu
    exact mul_pos (by norm_num) (h.lam_pos (p := (ū, u)) ⟨hū.1.le, hū.2, hu⟩))
  simpa only [uIcc_of_le hū.2.le] using hlog.boundedVariationOn

/-- Finite BV of log f implies finite BV of a positive f by the exponential
map on the bounded logarithmic range. Paper `e1a0fd5`, lines 1444–1445. -/
theorem boundedVariation_of_log {f : ℝ → ℝ} {s : Set ℝ}
    (hpos : ∀ x ∈ s, 0 < f x) (hlog : BoundedVariationOn (fun x => Real.log (f x)) s) :
    BoundedVariationOn f s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  let R := (eVariationOn (fun x => Real.log (f x)) s).toReal + |Real.log (f x₀)|
  have hb : ∀ x ∈ s, Real.log (f x) ∈ Icc (-R) R := by
    intro x hx
    exact abs_le.mp (boundedVariation_abs_bound hlog hx hx₀)
  have hexp : ContDiffOn ℝ 1 Real.exp (Icc (-R) R) := Real.contDiff_exp.contDiffOn
  obtain ⟨K, hK⟩ := hexp.exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc
  have hcomp := hK.comp_boundedVariationOn hb hlog
  change eVariationOn f s ≠ ⊤
  rw [← eVariationOn.congr (f := fun x => Real.exp (Real.log (f x)))
    (g := f) (fun x hx => Real.exp_log (hpos x hx))]
  exact hcomp

/-- The last two terminal bounds follow from the normalized derivative and
logarithmic expansion bounds, with no extra source hypothesis.
Paper `e1a0fd5`, `thm:main`, lines 145–146 and 1444–1445. -/
theorem StandingFull.terminal_derivative_bv_of_primary {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S)
    (hβ : BoundedVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ico ui 0))
    (hlog : BoundedVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0)) :
    BoundedVariationOn (fun u => S.nu u 0) (Ico ui 0) ∧
    BoundedVariationOn (fun u => S.dupsi u 0) (Ico ui 0) := by
  have hneg : ∀ u ∈ Ico ui 0, S.nu u 0 < 0 := fun u hu =>
    h.nu_neg (p := (u, 0)) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have hnu := boundedVariation_of_log (fun u hu => neg_pos.mpr (hneg u hu)) hlog
  have hn : BoundedVariationOn (fun u => S.nu u 0) (Ico ui 0) := by
    simpa using terminal_boundedVariation_neg hnu
  refine ⟨hn, ?_⟩
  change eVariationOn (fun u => S.dupsi u 0) (Ico ui 0) ≠ ⊤
  have he : EqOn (fun u => S.nu u 0 * (S.dupsi u 0 / S.nu u 0))
      (fun u => S.dupsi u 0) (Ico ui 0) := fun u hu =>
    mul_div_cancel₀ _ (ne_of_lt (hneg u hu))
  rw [← eVariationOn.congr he]
  exact hn.fun_mul hβ

end AcExtensionPrinciple

end
