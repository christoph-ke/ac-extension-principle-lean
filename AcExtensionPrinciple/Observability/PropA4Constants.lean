module

public import AcExtensionPrinciple.Observability.PropA4Statements

/-!
# Constant choices in the small-mass contradiction

Paper `e1a0fd5`, `equations.tex` lines 1855–1865 and 1906–1909.
The analytic upper and lower inner observation bounds are supplied in
`Observability/PropA4SmallMass.lean`. These helpers verify their algebraic
contradiction and the independence of the choices from `M/b`.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Filter
open scoped Topology

/-- The exact inner-cylinder duration grows at most logarithmically in L,
with its coefficient depending only on K. Paper `e1a0fd5`, lines 1902–1906. -/
theorem inner_duration_le {K L : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L) :
    positiveMassDuration K (1 / (2 * K * (K + 2) * L)) ≤
      (K + 2 + |Real.log (32 * K ^ 2 * (K + 2))|) * (1 + Real.log L) := by
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hK2 : 0 < K + 2 := by linarith
  have hC0 : 0 < 32 * K ^ 2 * (K + 2) := by positivity
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have heq : 2 / ((1 / (2 * K * (K + 2) * L)) * (1 / (8 * K))) =
      (32 * K ^ 2 * (K + 2)) * L := by
    field_simp
    ring
  unfold positiveMassDuration
  rw [heq, Real.log_mul hC0.ne' hL0.ne']
  apply max_le
  · nlinarith [abs_nonneg (Real.log (32 * K ^ 2 * (K + 2))),
      mul_nonneg (show 0 ≤ K + 2 + |Real.log (32 * K ^ 2 * (K + 2))| by positivity) hl0]
  · have habs := le_abs_self (Real.log (32 * K ^ 2 * (K + 2)))
    nlinarith [mul_nonneg (show 0 ≤ K + 1 + |Real.log (32 * K ^ 2 * (K + 2))| by positivity) hl0]

/-- The exact logarithmic denominator in the inner observation is bounded
by a constant depending only on K times `1+log L`. Paper `e1a0fd5`,
`eq:observability-inner-boundary-lower-bound`, lines 1902–1903. -/
theorem inner_log_denominator_le {K L : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L) :
    1 + |Real.log (1 / (2 * K * (K + 2) * L))| ≤
      (1 + Real.log (2 * K * (K + 2))) * (1 + Real.log L) := by
  have hD : 1 ≤ 2 * K * (K + 2) := by nlinarith
  have hD0 : 0 < 2 * K * (K + 2) := by linarith
  have hL0 : 0 < L := by linarith
  have hlogD := Real.log_nonneg hD
  have hlogL := Real.log_nonneg hL
  rw [one_div, Real.log_inv, abs_neg, Real.log_mul hD0.ne' hL0.ne',
    abs_of_nonneg (add_nonneg hlogD hlogL)]
  nlinarith [mul_nonneg hlogD hlogL]

/-- The cubic logarithmic loss is dominated by the scale. Paper `e1a0fd5`,
line 1906. -/
theorem logarithmic_scale_ratio_tendsto :
    Tendsto (fun L : ℝ => (1 + Real.log L) ^ 3 / L) atTop (𝓝 0) := by
  have hn (n : ℕ) : Tendsto (fun L : ℝ => Real.log L ^ n / L) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  convert (((hn 3).add ((hn 2).const_mul 3)).add ((hn 1).const_mul 3)).add (hn 0) using 1
  · funext L
    ring
  · norm_num

/-- Choose L first, exceeding any already required lower bound. The scale
depends only on the constants, not on mass or radius. Paper `e1a0fd5`,
line 1906. -/
theorem exists_large_scale {C q : ℝ} (hq : 0 < q) (B : ℝ) :
    ∃ L : ℝ, B ≤ L ∧ C * (1 + Real.log L) ^ 3 / L < q := by
  have ht : Tendsto (fun L : ℝ => C * (1 + Real.log L) ^ 3 / L) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using logarithmic_scale_ratio_tendsto.const_mul C
  exact ((eventually_ge_atTop B).and (ht.eventually (gt_mem_nhds hq))).exists

/-- A.3's exact lower bound at radius `LP` implies the printed
`P/(L²(1+log L)²)` bound, with explicit coefficient depending only on K
and the A.3 constant. The hypothesis is discharged by
`inner_observation_of_chart`. Paper `e1a0fd5`,
`eq:observability-inner-boundary-lower-bound`, lines 1902–1903. -/
theorem inner_observation_lower_scaled {K L P E c : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hP : 0 ≤ P) (hc : 0 ≤ c)
    (hE : c * (1 / (2 * K * (K + 2) * L)) ^ 3 * (L * P) /
      (1 + |Real.log (1 / (2 * K * (K + 2) * L))|) ^ 2 ≤ E) :
    (c / ((2 * K * (K + 2)) ^ 3 * (1 + Real.log (2 * K * (K + 2))) ^ 2)) * P /
      (L ^ 2 * (1 + Real.log L) ^ 2) ≤ E := by
  have hD : 1 ≤ 2 * K * (K + 2) := by nlinarith
  have hD0 : 0 < 2 * K * (K + 2) := by linarith
  have hL0 : 0 < L := by linarith
  have hlogD := Real.log_nonneg hD
  have hlogL := Real.log_nonneg hL
  have hB : 0 < 1 + Real.log (2 * K * (K + 2)) := by linarith
  have hBL : 0 < 1 + Real.log L := by linarith
  have hden : 0 < 1 + |Real.log (1 / (2 * K * (K + 2) * L))| := by positivity
  have hb := pow_le_pow_left₀ hden.le (inner_log_denominator_le hK hL) 2
  have hn : 0 ≤ c * (1 / (2 * K * (K + 2) * L)) ^ 3 * (L * P) := by positivity
  have hfrac := div_le_div_of_nonneg_left hn (pow_pos hden 2) hb
  calc
    _ = c * (1 / (2 * K * (K + 2) * L)) ^ 3 * (L * P) /
        ((1 + Real.log (2 * K * (K + 2))) * (1 + Real.log L)) ^ 2 := by
      field_simp
    _ ≤ c * (1 / (2 * K * (K + 2) * L)) ^ 3 * (L * P) /
        (1 + |Real.log (1 / (2 * K * (K + 2) * L))|) ^ 2 := hfrac
    _ ≤ E := hE

/-- A small mass ratio fits both the inner radius and its observation
interval within the outer cylinder. Paper `e1a0fd5`, lines 1907–1908.
Here `P = (K+2)M`, `a = LP`, and `H` is the inner duration factor. -/
theorem inner_interval_fits {K L H ε M b : ℝ}
    (hK : 1 ≤ K) (hL : 0 < L) (hH : 0 ≤ H) (hb : 0 < b)
    (hεa : 2 * L * (K + 2) * ε ≤ 1)
    (hεT : 2 * H * L * (K + 2) * ε ≤ 1)
    (hratio : M / b ≤ ε) :
    2 * (L * ((K + 2) * M)) ≤ b ∧
      2 * H * (L * ((K + 2) * M)) ≤ b := by
  have hMb := (div_le_iff₀ hb).mp hratio
  have hK2 : 0 ≤ K + 2 := by linarith
  constructor
  · have hh := mul_le_mul_of_nonneg_left hMb (show 0 ≤ 2 * L * (K + 2) by positivity)
    have hfit := mul_le_mul_of_nonneg_right hεa hb.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hMb
      (show 0 ≤ 2 * H * L * (K + 2) by positivity)
    have hfit := mul_le_mul_of_nonneg_right hεT hb.le
    nlinarith

/-- After L and the inner duration have been fixed, choose the outer
mass-ratio threshold independently of M and b. Paper `e1a0fd5`,
lines 1907–1908 and the inner-mass error choice at lines 1860–1865. -/
theorem choose_outer_threshold {K L H C q : ℝ} (hK : 1 ≤ K)
    (hL : 0 < L) (hH : 0 ≤ H) (hC : 0 ≤ C) (hq : 0 < q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      2 * L * (K + 2) * ε ≤ 1 ∧ 2 * H * L * (K + 2) * ε ≤ 1 ∧
      C * (K + 2) ^ 2 * ε ≤ q := by
  have hK2 : 0 < K + 2 := by linarith
  let A := 2 * L * (K + 2)
  let B := 2 * H * L * (K + 2)
  let D := C * (K + 2) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let ε := min (1 / 4 : ℝ) (min (1 / A) (min (1 / (1 + B)) (q / (1 + D))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he₁ : ε ≤ 1 / 4 := min_le_left _ _
  have heA : ε ≤ 1 / A := (min_le_right _ _).trans (min_le_left _ _)
  have heB : ε ≤ 1 / (1 + B) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heD : ε ≤ q / (1 + D) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hboundA := (le_div_iff₀ hA).mp heA
  have hboundB := (le_div_iff₀ (show 0 < 1 + B by linarith)).mp heB
  have hboundD := (le_div_iff₀ (show 0 < 1 + D by linarith)).mp heD
  refine ⟨ε, hε, by linarith, ?_, ?_, ?_⟩
  · change A * ε ≤ 1
    nlinarith
  · change B * ε ≤ 1
    nlinarith
  · change D * ε ≤ q
    nlinarith

/-- Choose δ last, controlling both the total-mass bound and the terms
containing outer observation in the inner-cylinder estimate. Paper `e1a0fd5`,
lines 1683–1684 and 1908–1909. The two positive budgets are fixed before δ. -/
theorem choose_observation_threshold {K C H L q qObs : ℝ}
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 < L)
    (hq : 0 < q) (hqObs : 0 < qObs) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / (2 * K) ∧ C * δ ≤ q ∧
      C * (1 + H / L ^ 2) * δ ≤ qObs := by
  have hK0 : 0 < K := by linarith
  let D := C * (1 + H / L ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let δ := min (1 / (2 * K)) (min (q / (1 + C)) (qObs / (1 + D)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδK : δ ≤ 1 / (2 * K) := min_le_left _ _
  have hδC : δ ≤ q / (1 + C) := (min_le_right _ _).trans (min_le_left _ _)
  have hδD : δ ≤ qObs / (1 + D) := (min_le_right _ _).trans (min_le_right _ _)
  have hboundC := (le_div_iff₀ (show 0 < 1 + C by linarith)).mp hδC
  have hboundD := (le_div_iff₀ (show 0 < 1 + D by linarith)).mp hδD
  refine ⟨δ, hδ, hδK, by nlinarith, ?_⟩
  change D * δ ≤ qObs
  nlinarith

/-- The displayed error terms retain at least `M/(4K)` once their
dimensionless sum is small. Paper `e1a0fd5`,
`eq:observability-inner-mass-lower-bound`, lines 1855–1865. -/
theorem retain_inner_mass {K C L δ ε M E b m : ℝ}
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hE : E ≤ δ * M) (hratio : M / b ≤ ε)
    (hsmall : C * (δ + (K + 2) / L + (K + 2) ^ 2 * ε) ≤ 3 / (4 * K))
    (hm : M / K - C * (E + (K + 2) * M / L + ((K + 2) * M) ^ 2 / b) ≤ m) :
    M / (4 * K) ≤ m := by
  have hK0 : 0 < K := by linarith
  have hquad : ((K + 2) * M) ^ 2 / b ≤ (K + 2) ^ 2 * ε * M := by
    have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg (sq_nonneg (K + 2)) hM)
    convert hh using 1 <;> ring
  have herror : C * (E + (K + 2) * M / L + ((K + 2) * M) ^ 2 / b) ≤
      (3 / (4 * K)) * M := by
    calc
      _ ≤ C * (δ * M + (K + 2) * M / L + (K + 2) ^ 2 * ε * M) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hC
      _ = C * (δ + (K + 2) / L + (K + 2) ^ 2 * ε) * M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hM
  have heq : M / K - (3 / (4 * K)) * M = M / (4 * K) := by field_simp; ring
  rw [← heq]
  linarith

/-- The two inner observation bounds contradict small outer observation
after their fixed scale and δ choices. Paper `e1a0fd5`,
`eq:observability-inner-boundary-upper-bound`,
`eq:observability-inner-boundary-lower-bound`, lines 1894–1909. -/
theorem inner_energy_contradiction {P E Ea C H L q δ : ℝ}
    (hP : 0 < P) (hC : 0 ≤ C) (hH : 0 ≤ H) (hL : 0 < L) (hq : 0 < q)
    (hscale : C * H / L ^ 3 ≤ q / 4)
    (hδ : C * (1 + H / L ^ 2) * δ ≤ q / 4)
    (hE : E ≤ δ * P) (hlower : q * P ≤ Ea)
    (hupper : Ea ≤ C * (E + H * (P / L ^ 3 + E / L ^ 2))) : False := by
  have hcoeff : 0 ≤ C * (1 + H / L ^ 2) := by positivity
  have he := mul_le_mul_of_nonneg_left hE hcoeff
  have heδ := mul_le_mul_of_nonneg_right hδ hP.le
  have hscaleP := mul_le_mul_of_nonneg_right hscale hP.le
  have heq : C * (E + H * (P / L ^ 3 + E / L ^ 2)) =
      C * (1 + H / L ^ 2) * E + (C * H / L ^ 3) * P := by ring
  rw [heq] at hupper
  have hqP : 0 < q * P := mul_pos hq hP
  linarith

end PropA4
end AcExtensionPrinciple

end
