module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# A vanishing subsequence from finite logarithmically weighted square integral

Internal helpers for paper commit `e1a0fd5`, `equations.tex`
lines 1352–1356 (`eq:logarithmic-remainder-integrability`).
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Every terminal subinterval contains a point where `|f| < ε`; paper `e1a0fd5`,
`equations.tex` lines 1352–1356 (`eq:logarithmic-remainder-integrability`).
Only the measurable lower bound is used, so `f` need not be measurable. -/
theorem exists_abs_lt_of_logarithmic_lintegral_finite {u0 a eps : ℝ} {f : ℝ → ℝ}
    (hu0a : u0 ≤ a) (ha : a < 0) (heps : 0 < eps)
    (hfin : (∫⁻ u in Ioo u0 0, ENNReal.ofReal (f u ^ 2 / (-u))) < ∞) :
    ∃ u ∈ Ioo a 0, |f u| < eps := by
  by_contra! hnot
  have hlo : (∫⁻ u in Ioo a 0, ENNReal.ofReal (eps ^ 2 / (-u))) < ∞ := by
    apply lt_of_le_of_lt _ hfin
    calc
      _ ≤ ∫⁻ u in Ioo a 0, ENNReal.ofReal (f u ^ 2 / (-u)) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro u hu
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (by linarith [hu.2])
        nlinarith [hnot u hu, sq_abs (f u), abs_nonneg (f u)]
      _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioo hu0a le_rfl)
  have hmeas : AEStronglyMeasurable (fun u : ℝ ↦ eps ^ 2 / (-u))
      (volume.restrict (Ioo a 0)) :=
    ((measurable_const.pow_const 2).div measurable_id.neg).aestronglyMeasurable
  have hpos : 0 ≤ᵐ[volume.restrict (Ioo a 0)] (fun u : ℝ ↦ eps ^ 2 / (-u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact div_nonneg (sq_nonneg _) (by linarith [hu.2])
  have hi := (lintegral_ofReal_ne_top_iff_integrable hmeas hpos).mp (ne_of_lt hlo)
  have hiinv : IntegrableOn (fun u : ℝ ↦ (-u)⁻¹) (Ioo a 0) := by
    change Integrable _ _
    convert hi.div_const (eps ^ 2) using 1
    funext u
    rw [div_right_comm, div_self (pow_ne_zero 2 heps.ne'), one_div]
  have hii : IntervalIntegrable (fun u : ℝ ↦ (-u)⁻¹) volume a 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr hiinv
  rw [IntervalIntegrable.iff_comp_neg] at hii
  simp only [neg_neg, neg_zero] at hii
  rw [intervalIntegrable_inv_iff] at hii
  simp only [neg_eq_zero] at hii
  rcases hii with heq | hnotmem
  · exact ha.ne heq
  · exact hnotmem right_mem_uIcc

/-- A sequence inside `(u₀,0)` tends to zero and makes `f` tend to zero; paper
`e1a0fd5`, `equations.tex` lines 1352–1356 (`eq:logarithmic-remainder-integrability`).
No measurability hypothesis on `f` is imposed. -/
theorem exists_sequence_tendsto_zero_of_logarithmic_lintegral_finite
    {u0 : ℝ} {f : ℝ → ℝ} (hu0 : u0 < 0)
    (hfin : (∫⁻ u in Ioo u0 0, ENNReal.ofReal (f u ^ 2 / (-u))) < ∞) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo u0 0) ∧
      Tendsto u atTop (𝓝 0) ∧ Tendsto (fun n ↦ f (u n)) atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ u ∈ Ioo (max u0 (-(1 / ((n : ℝ) + 1)))) 0,
      |f u| < 1 / ((n : ℝ) + 1) := by
    apply exists_abs_lt_of_logarithmic_lintegral_finite (le_max_left _ _)
      (max_lt hu0 (neg_neg_of_pos (by positivity))) (by positivity) hfin
  choose u hu hfu using hex
  have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hneg : Tendsto (fun n : ℕ ↦ -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [neg_zero] using hlim.neg
  refine ⟨u, fun n ↦ ⟨(le_max_left _ _).trans_lt (hu n).1, (hu n).2⟩, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hneg tendsto_const_nhds
    · exact fun n ↦ (le_max_right _ _).trans (hu n).1.le
    · exact fun n ↦ (hu n).2.le
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero (fun n ↦ abs_nonneg _) (fun n ↦ (hfu n).le) hlim

end AcExtensionPrinciple

end
