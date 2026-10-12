module

public import AcExtensionPrinciple.Observability.LemmaA3Flux

/-!
# AC comparison and weighted Cauchy–Schwarz for Lemma A.3

Internal calculus helpers for paper `e1a0fd5`, `equations.tex` lines
1567–1611. Their AC and integrability premises are supplied by the chart
characteristic primitives, not added to the paper statement.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- An AC function with nonnegative a.e. derivative increases between its
endpoints. Paper `e1a0fd5`, `eq:observability-annular-lapse-bounds`, lines 1576–1583. -/
theorem lemmaA3_ac_endpoint_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, x ∈ Ioo a b → 0 ≤ deriv f x) : f a ≤ f b := by
  have hi : 0 ≤ ∫ x in a..b, deriv f x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact hd
  rw [hf.integral_deriv_eq_sub] at hi
  linarith

/-- Weighted Cauchy–Schwarz, using an integrable `f²/w` and a positive
continuous weight. Paper `e1a0fd5`, `eq:observability-annular-scalar`, lines 1585–1591. -/
theorem lemmaA3_weighted_sq_le {f w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hw : ContinuousOn w (Icc a b)) (hwp : ∀ x ∈ Icc a b, 0 < w x)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2 / w x) volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2 / w x) * (∫ x in a..b, w x) := by
  rcases hab.eq_or_lt with he | hlt
  · subst b
    simp
  have hwi : IntervalIntegrable w volume a b := by
    exact (hw.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hW : 0 < ∫ x in a..b, w x :=
    intervalIntegral.integral_pos hlt hw (fun x hx => (hwp x ⟨hx.1.le, hx.2⟩).le)
      ⟨b, ⟨hab, le_rfl⟩, hwp b ⟨hab, le_rfl⟩⟩
  let c := (∫ x in a..b, f x) / (∫ x in a..b, w x)
  have hc : c * (∫ x in a..b, w x) = ∫ x in a..b, f x :=
    div_mul_cancel₀ _ hW.ne'
  have hn : 0 ≤ ∫ x in a..b, f x ^ 2 / w x - 2 * c * f x + c ^ 2 * w x := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    have := div_nonneg (sq_nonneg (f x - c * w x)) (hwp x hx).le
    have he : (f x - c * w x) ^ 2 / w x =
        f x ^ 2 / w x - 2 * c * f x + c ^ 2 * w x := by
      field_simp [(hwp x hx).ne']
      ring
    rwa [he] at this
  rw [intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) (hwi.const_mul _),
    intervalIntegral.integral_sub hf2 (hf.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hn
  have := mul_nonneg hW.le hn
  nlinarith [sq_nonneg (∫ x in a..b, f x)]

end AcExtensionPrinciple

end
