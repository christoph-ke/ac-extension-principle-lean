module

public import AcExtensionPrinciple.Observability.LemmaA3Flux
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Lemma A.3: an explicit integrating factor for the annular Gronwall estimate

Paper `e1a0fd5`, `eq:observability-annular-gronwall` and
`eq:observability-annular-exponent`, lines 1607–1621.
The factor retains the coefficient two in the logarithmic exponent.
-/

public section

namespace AcExtensionPrinciple

/-- Inverse annular amplification. Paper `e1a0fd5`,
`eq:observability-annular-exponent`, lines 1613–1621.
Its logarithmic derivative is the printed exponent majorant. -/
@[expose] noncomputable def lemmaA3Weight (p r : ℝ) : ℝ :=
  (r - 2 * p) ^ 2 * Real.exp (-4 * p / (r - 2 * p))

/-- The annular integrating factor has the required derivative. Paper
`e1a0fd5`, `eq:observability-annular-exponent`, lines 1613–1621. -/
theorem lemmaA3Weight_hasDerivAt {p r : ℝ} (hr : 2 * p < r) :
    HasDerivAt (lemmaA3Weight p)
      (lemmaA3Weight p r * (2 / (r - 2 * p) + 4 * p / (r - 2 * p) ^ 2)) r := by
  have hne : r - 2 * p ≠ 0 := by linarith
  have hd := (hasDerivAt_id r).sub_const (2 * p)
  have he := ((hasDerivAt_const r (-4 * p)).div hd hne).exp
  convert (hd.pow 2).mul he using 1
  · rfl
  · unfold lemmaA3Weight
    simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one, id_eq, Pi.div_apply, Pi.pow_apply]
    field_simp [hne]
    ring

/-- Positivity and the simple upper bound for the integrating factor. Paper
`e1a0fd5`, `eq:observability-annular-gronwall`, lines 1607–1621. -/
theorem lemmaA3Weight_bounds {p r b : ℝ} (hp : 0 ≤ p) (hr : 2 * p < r) (hrb : r ≤ b) :
    0 < lemmaA3Weight p r ∧ lemmaA3Weight p r ≤ b ^ 2 := by
  have hx : 0 < r - 2 * p := by linarith
  have he : Real.exp (-4 * p / (r - 2 * p)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hx.le
  unfold lemmaA3Weight
  constructor
  · exact mul_pos (sq_pos_of_pos hx) (Real.exp_pos _)
  · have hh := mul_le_mul_of_nonneg_left he (sq_nonneg (r - 2 * p))
    nlinarith

/-- AC of the integrating factor along an AC ray staying in the annulus.
Paper `e1a0fd5`, `eq:observability-annular-gronwall`, lines 1607–1611.
The radius AC premise comes from the characteristic radius primitive. -/
theorem lemmaA3Weight_ac {z : ℝ → ℝ} {p a b : ℝ}
    (hz : AbsolutelyContinuousOnInterval z a b)
    (hpos : ∀ s ∈ Set.uIcc a b, 2 * p < z s) :
    AbsolutelyContinuousOnInterval (fun s => lemmaA3Weight p (z s)) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => 2 * p) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hsub := hz.sub hc
  have hcomp := positive_ac_comp (F := fun x => x ^ 2 * Real.exp (-4 * p / x)) hsub
    (by intro s hs; exact sub_pos.mpr (hpos s hs)) (by
      apply ContDiffOn.mul (contDiffOn_id.pow 2)
      apply ContDiffOn.exp
      exact contDiffOn_const.div contDiffOn_id (fun x hx => ne_of_gt hx))
  exact hcomp

/-- Quantitative lower bound for the inverse amplification, uniform in ε.
Paper `e1a0fd5`, `eq:observability-annular-exponent`, lines 1613–1621. -/
theorem lemmaA3Weight_lower {p r M δ : ℝ} (_hp : 0 ≤ p) (hM : 0 < M) (hδ : 0 < δ)
    (hpM : p ≤ 2 * M) (hgap : δ * M ≤ r - 2 * p) :
    δ ^ 2 * M ^ 2 * Real.exp (-8 / δ) ≤ lemmaA3Weight p r := by
  have hx : 0 < r - 2 * p := (mul_pos hδ hM).trans_le hgap
  have hfrac : 4 * p / (r - 2 * p) ≤ 8 / δ := by
    apply (div_le_div_iff₀ hx hδ).mpr
    have hh := mul_le_mul_of_nonneg_left hpM (show 0 ≤ 4 * δ by positivity)
    nlinarith [hgap]
  have hneg : -8 / δ ≤ -4 * p / (r - 2 * p) := by
    simpa only [neg_div, neg_mul] using neg_le_neg hfrac
  have he := Real.exp_le_exp.mpr hneg
  have hs : δ ^ 2 * M ^ 2 ≤ (r - 2 * p) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hgap) (show 0 ≤ r - 2 * p + δ * M by positivity)]
  unfold lemmaA3Weight
  exact mul_le_mul hs he (Real.exp_pos _).le (by positivity)

/-- The integrating factor cancels the annular differential coefficient along
an incoming ray. Paper `e1a0fd5`, `eq:observability-annular-gronwall`,
lines 1607–1611. The speed premise is the annular lapse lower bound. -/
theorem lemmaA3Weight_drift {p r b v : ℝ} (hp : 0 ≤ p) (hr : 2 * p < r)
    (hb : r ≤ b) (hv : v ≤ -(1 - 2 * p / r)) :
    (2 / (r - 2 * p) + 4 * p / (r - 2 * p) ^ 2) * v +
      2 * (r⁻¹ - b⁻¹) / (1 - 2 * p / r) ≤ 0 := by
  have hr0 : 0 < r := by linarith
  have hb0 : 0 < b := hr0.trans_le hb
  have hx : 0 < r - 2 * p := by linarith
  have hcoef : 0 ≤ 2 / (r - 2 * p) + 4 * p / (r - 2 * p) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hv hcoef
  have he : (2 / (r - 2 * p) + 4 * p / (r - 2 * p) ^ 2) * (-(1 - 2 * p / r)) +
      2 * (r⁻¹ - b⁻¹) / (1 - 2 * p / r) = -2 * r / (b * (r - 2 * p)) := by
    field_simp [hr0.ne', hb0.ne', hx.ne']
    ring
  have hn : -2 * r / (b * (r - 2 * p)) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

end AcExtensionPrinciple

end
