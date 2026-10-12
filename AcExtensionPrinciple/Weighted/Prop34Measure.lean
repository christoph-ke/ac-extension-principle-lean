module

public import AcExtensionPrinciple.Weighted.ClassWeights
public import AcExtensionPrinciple.Weighted.CauchySchwarz
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weighted measure, L¹ identification space, and terminal monotone convergence

Helpers for paper `e1a0fd5`, `prop:weighted-remainder-control`,
`equations.tex` lines 1292–1318. Finiteness of the proper-domain weighted
measure is derived from the class's compact geometric bounds.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The terminal triangle, without its possibly singular endpoint.
Paper `e1a0fd5`, `eq:coercive-remainder-bound`, lines 1233–1236. -/
@[expose] def weightedFullDomain (u₀ : ℝ) : Set (ℝ × ℝ) :=
  {p | u₀ ≤ p.1 ∧ p.1 < 0 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 0}

/-- Squared weighted L¹ is bounded by weighted energy times weighted measure.
Paper `e1a0fd5`, `eq:remainder-difference-l1`, lines 1292–1302. -/
theorem lintegral_weighted_l1_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ≥0∞} {W : α → ℝ}
    (hw : AEMeasurable w μ) (hW : AEMeasurable W μ) :
    (∫⁻ p, w p * ENNReal.ofReal |W p| ∂μ) ^ 2 ≤
      (∫⁻ p, w p ∂μ) * ∫⁻ p, w p * ENNReal.ofReal (|W p| ^ 2) ∂μ := by
  have he := lintegral_sqrt_mul_sq_le hw
    (hw.mul ((hW.norm.pow_const 2).ennreal_ofReal))
  simp only [Pi.mul_apply, Real.norm_eq_abs] at he
  convert he using 2
  apply lintegral_congr
  intro p
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num
  rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
    (by norm_num) (by norm_num)]
  norm_num

/-- A uniform bound on proper truncations passes to the full terminal
triangle by monotone convergence. Paper `e1a0fd5`, line 1318.
No measurability of the integrand is needed for this lower-integral form. -/
theorem weighted_full_lintegral_le_of_truncations {u₀ : ℝ}
    (f : ℝ × ℝ → ℝ≥0∞) {B : ℝ≥0∞}
    (hbound : ∀ U : ℝ, U < 0 → (∫⁻ p in weightedTruncatedDomain u₀ U, f p) ≤ B) :
    (∫⁻ p in weightedFullDomain u₀, f p) ≤ B := by
  let U := fun n : ℕ => -(1 / ((n : ℝ) + 1))
  have hU (n : ℕ) : U n < 0 := by
    dsimp [U]
    exact neg_neg_of_pos (by positivity)
  have hmono : Monotone U := by
    intro m n hmn
    dsimp [U]
    apply neg_le_neg
    apply one_div_le_one_div_of_le (by positivity)
    have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    exact add_le_add hmn' le_rfl
  have hlim : Tendsto U atTop (𝓝 0) := by
    have hl : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [U, neg_zero] using hl.neg
  have heq : weightedFullDomain u₀ = ⋃ n, weightedTruncatedDomain u₀ (U n) := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hp.2.1)).exists
      exact mem_iUnion.mpr ⟨n, hp.1, hn.le, hp.2.2⟩
    · intro hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact ⟨hn.1, hn.2.1.trans_lt (hU n), hn.2.2⟩
  have hd : Directed (· ⊆ ·) (fun n => weightedTruncatedDomain u₀ (U n)) := by
    intro m n
    exact ⟨max m n, weightedTruncatedDomain_mono (hmono (le_max_left _ _)),
      weightedTruncatedDomain_mono (hmono (le_max_right _ _))⟩
  rw [heq, setLIntegral_iUnion_of_directed f hd]
  exact iSup_le (fun n => hbound (U n) (hU n))

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Each proper truncation has finite weighted measure. Paper `e1a0fd5`,
lines 1298–1302. Compact expansion bounds and the global mass gap suffice;
no bound on the remainder is assumed. -/
theorem weighted_truncated_measure_lt_top {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    (∫⁻ p in weightedTruncatedDomain u₀ U,
      ENNReal.ofReal (weightedRemainderDensity S p)) < ⊤ := by
  let D := weightedTruncatedDomain u₀ U
  have hD := isCompact_weightedTruncatedDomain u₀ U
  have hsub := weightedTruncatedDomain_subset_triangle hi hU
  obtain ⟨c, hc, he⟩ := h.regularCenter.localBV.expansion_bounds D hD hsub
  let g := weightedGapConstant ui S
  have hg : 0 < g := h.weightedGapConstant_pos
  have hbound (p : ℝ × ℝ) (hp : p ∈ D) :
      weightedRemainderDensity S p ≤ (1 / c) / (g ^ 2 * c) := by
    have hgap := h.mass_gap_lower (hsub hp)
    have hden : g ^ 2 * c ≤ (1 - S.mu p.1 p.2) ^ 2 * S.lam p.1 p.2 :=
      mul_le_mul (pow_le_pow_left₀ hg.le hgap 2) (he p hp).1 hc.le (sq_nonneg _)
    exact div_le_div₀ (by positivity) (he p hp).2 (by positivity) hden
  calc
    _ ≤ ∫⁻ _p in D, ENNReal.ofReal ((1 / c) / (g ^ 2 * c)) := by
      apply setLIntegral_mono' (measurableSet_weightedTruncatedDomain u₀ U)
      exact fun p hp => ENNReal.ofReal_le_ofReal (hbound p hp)
    _ < ⊤ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD.measure_lt_top

/-- The finite-energy constructed remainder is in the weighted L¹
identification space. Paper `e1a0fd5`, lines 1298–1302.
Both the energy and the weighted measure refer to the full proper
triangle, including radii below an eventual energy cutoff. -/
theorem weighted_remainder_l1_lt_top_of_energy {u₀ U : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W)
    (henergy : weightedRemainderNormSq S u₀ U W < ⊤) :
    weightedRemainderL1 S u₀ U W < ⊤ := by
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density hi hU
  have hL : weightedRemainderL1 S u₀ U W =
      ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal (ω p) * ENNReal.ofReal |W p| := by
    apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
    intro p hp
    dsimp only
    rw [heω hp, mul_comm (ω p), ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  have hE : weightedRemainderNormSq S u₀ U W =
      ∫⁻ p in weightedTruncatedDomain u₀ U,
        ENNReal.ofReal (ω p) * ENNReal.ofReal (|W p| ^ 2) := by
    apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
    intro p hp
    dsimp only
    rw [heω hp, mul_comm (ω p), ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  have hM : (∫⁻ p in weightedTruncatedDomain u₀ U,
      ENNReal.ofReal (weightedRemainderDensity S p)) =
      ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal (ω p) := by
    apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
    intro p hp
    dsimp only
    rw [heω hp]
  have hcs := lintegral_weighted_l1_sq_le
    (μ := volume.restrict (weightedTruncatedDomain u₀ U))
    hω.ennreal_ofReal.aemeasurable hW.aemeasurable
  rw [← hL, ← hE, ← hM] at hcs
  have hsq : weightedRemainderL1 S u₀ U W ^ 2 < ⊤ := hcs.trans_lt
    (ENNReal.mul_lt_top (h.weighted_truncated_measure_lt_top hi hU) henergy)
  by_contra hnot
  have he : weightedRemainderL1 S u₀ U W = ⊤ := le_antisymm le_top (le_of_not_gt hnot)
  simp only [he, ENNReal.top_pow (by decide : (2 : ℕ) ≠ 0), lt_self_iff_false] at hsq

end StandingFull

end AcExtensionPrinciple

end
