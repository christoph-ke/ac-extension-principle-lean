module

public import AcExtensionPrinciple.External.ChristodoulouDerivedGeometry
public import AcExtensionPrinciple.Solution.PositiveAC
public import AcExtensionPrinciple.Weighted.Transport

/-!
# AC comparison tools for Christodoulou's sign conditions

Internal helpers for paper `e1a0fd5`, `equations.tex` `eq:mass`, `eq:radius`,
lines 220–275 and 1411; Christodoulou pp. 1147–1148. All coefficient
integrability premises are discharged on compact off-axis segments in
`ChristodoulouDerivedMass` and `ChristodoulouDerivedSigns`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A nonnegative numerator divided by a uniformly positive integrable function
remains integrable. Paper `e1a0fd5`, `eq:mass`, lines 220–275.
The mass application uses BV θ² and the class lower bound for λ. -/
theorem chr_intervalIntegrable_div_pos {f g : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ f x ∧ c ≤ g x) :
    IntervalIntegrable (fun x => f x / g x) volume a b := by
  apply (hf.div_const c).mono_fun'
  · simpa only [uIoc_of_le hab, Pi.div_def] using
      hf.aestronglyMeasurable.div₀ hg.aestronglyMeasurable
  · rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hb := hpos x (Ioc_subset_Icc_self hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb.1 (hc.le.trans hb.2))]
    exact div_le_div_of_nonneg_left hb.1 hc hb.2

/-- The integrating factor cancels an integrable linear coefficient in an AC ODE.
Paper `e1a0fd5`, `eq:mass`, `eq:radius`, lines 220–275;
Christodoulou pp. 1147–1148. AC follows from characteristic primitives. -/
theorem chr_weighted_primitive {f q g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hq : IntervalIntegrable q volume a b)
    (hd : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (-q x * f x + g x) x) :
    IntervalPrimitive (fun x => Real.exp (∫ t in a..x, q t) * f x)
      (fun x => Real.exp (∫ t in a..x, q t) * g x) a b := by
  have hA := hq.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  apply ac_integral_eq_sub hab ((ac_exp hA).fun_mul hf)
  filter_upwards [hd, hq.ae_hasDerivAt_integral] with x hdx hAx
  intro hx
  have hx' : x ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨hx.1.le, hx.2.le⟩
  convert ((hAx hx' a (by simp)).exp).mul (hdx hx) using 1
  ring

/-- A dissipative linear equation with nonnegative source cannot fall below
the lesser of its initial value and zero. Paper `e1a0fd5`, `eq:mass`,
lines 220–275; Christodoulou p. 1147. No integrability at the axis is required. -/
theorem chr_linear_lower_bound {f q g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hq : IntervalIntegrable q volume a b)
    (hd : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (-q x * f x + g x) x)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ q x ∧ 0 ≤ g x) : min (f a) 0 ≤ f b := by
  have hw := chr_weighted_primitive hab hf hq hd
  have hI : 0 ≤ ∫ x in a..b, Real.exp (∫ t in a..x, q t) * g x :=
    intervalIntegral.integral_nonneg hab
      (fun x hx => mul_nonneg (Real.exp_pos _).le (hpos x hx).2)
  have hE : 1 ≤ Real.exp (∫ t in a..b, q t) := by
    exact Real.one_le_exp_iff.mpr
      (intervalIntegral.integral_nonneg hab (fun x hx => (hpos x hx).1))
  have hle : f a ≤ Real.exp (∫ t in a..b, q t) * f b := by
    simpa using (show f a ≤ Real.exp (∫ t in a..b, q t) * f b by
      have he := hw.2
      simp only [intervalIntegral.integral_same, Real.exp_zero, one_mul] at he
      linarith)
  by_cases hb : 0 ≤ f b
  · exact (min_le_right _ _).trans hb
  · have hm : Real.exp (∫ t in a..b, q t) * f b ≤ f b := by
      simpa using mul_le_mul_of_nonpos_right hE (le_of_not_ge hb)
    exact (min_le_left _ _).trans (hle.trans hm)

/-- A uniformly positive source makes a nonnegative initial value strictly
positive at the other endpoint. Paper `e1a0fd5`, `eq:mass`, lines 220–275;
Christodoulou p. 1147. The mass-gap source is λ ≥ c > 0. -/
theorem chr_linear_pos {f q g : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hc : 0 < c) (hf : AbsolutelyContinuousOnInterval f a b)
    (hq : IntervalIntegrable q volume a b)
    (hd : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (-q x * f x + g x) x)
    (hfa : 0 ≤ f a) (hpos : ∀ x ∈ Icc a b, 0 ≤ q x ∧ c ≤ g x) :
    0 < f b := by
  have hw := chr_weighted_primitive hab.le hf hq hd
  have hle : c * (b - a) ≤
      ∫ x in a..b, Real.exp (∫ t in a..x, q t) * g x := by
    calc
      _ = ∫ _ in a..b, c := by simp [mul_comm]
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hw.1
        intro x hx
        have hE : 1 ≤ Real.exp (∫ t in a..x, q t) := by
          apply Real.one_le_exp_iff.mpr
          exact intervalIntegral.integral_nonneg hx.1
            (fun t ht => (hpos t ⟨ht.1, ht.2.trans hx.2⟩).1)
        exact (hpos x hx).2.trans (by
          simpa using mul_le_mul_of_nonneg_right hE (hc.le.trans (hpos x hx).2))
  have he := hw.2
  simp only [intervalIntegral.integral_same, Real.exp_zero, one_mul] at he
  have hp : 0 < Real.exp (∫ t in a..b, q t) * f b := by
    have hcba := mul_pos hc (sub_pos.mpr hab)
    linarith
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hp

/-- Zero one-sided boundary value and compact-segment comparisons imply
nonnegativity. Paper `e1a0fd5`, `eq:regular-axis`, `eq:mass`, lines 220–275;
Christodoulou (1.7a,b), p. 1147. -/
theorem chr_nonneg_of_axis_comparison {f : ℝ → ℝ} {u v : ℝ}
    (huv : u < v) (hzero : Tendsto f (𝓝[>] u) (𝓝 0))
    (hcomp : ∀ a ∈ Ioo u v, min (f a) 0 ≤ f v) : 0 ≤ f v := by
  have ht : Tendsto (fun a => min (f a) 0) (𝓝[>] u) (𝓝 0) := by
    simpa using hzero.min (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) _ _)
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT huv] with a ha
  exact hcomp a ha

end AcExtensionPrinciple

end
