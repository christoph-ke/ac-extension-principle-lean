module

public import AcExtensionPrinciple.Weighted.Prop34UniformEnergy
public import AcExtensionPrinciple.Integration.DecayChain

/-!
# Terminal coercive energy in the main theorem's actual interface

Paper `e1a0fd5`, `eq:coercive-remainder-bound`, lines 1233–1236
and 1316–1318. Monotone convergence acts directly on the outgoing
iterated lower integral of the actual radial derivative remainder.
The decay premises are proved by `StandingFull.uniform_mass_decay` and
`StandingFull.common_scalar_limit` in `Integration/DecayComplete.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal Topology

/-- Uniform proper incoming-time truncations control the terminal lower
integral by monotone convergence, with no measurability premise on the
cone energy. Paper `e1a0fd5`, line 1318. -/
theorem terminal_iterated_lintegral_le_of_truncations {u₀ : ℝ}
    (f : ℝ → ℝ≥0∞) {B : ℝ≥0∞}
    (hbound : ∀ U : ℝ, U < 0 → (∫⁻ u in Icc u₀ U, f u) ≤ B) :
    (∫⁻ u in Ioo u₀ 0, f u) ≤ B := by
  let U := fun n : ℕ => -(1 / ((n : ℝ) + 1))
  have hU (n : ℕ) : U n < 0 := by dsimp [U]; exact neg_neg_of_pos (by positivity)
  have hmono : Monotone U := by
    intro m n hmn
    dsimp [U]
    apply neg_le_neg
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add (Nat.cast_le.mpr hmn) le_rfl
  have hlim : Tendsto U atTop (𝓝 0) := by
    have hl : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [U, neg_zero] using hl.neg
  have he : Ico u₀ 0 = ⋃ n, Icc u₀ (U n) := by
    ext u
    constructor
    · intro hu
      obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hu.2)).exists
      exact mem_iUnion.mpr ⟨n, hu.1, hn.le⟩
    · intro hu
      obtain ⟨n, hn⟩ := mem_iUnion.mp hu
      exact ⟨hn.1, hn.2.trans_lt (hU n)⟩
  have hd : Directed (· ⊆ ·) (fun n => Icc u₀ (U n)) := by
    intro m n
    exact ⟨max m n, Icc_subset_Icc_right (hmono (le_max_left _ _)),
      Icc_subset_Icc_right (hmono (le_max_right _ _))⟩
  calc
    _ ≤ ∫⁻ u in Ico u₀ 0, f u := lintegral_mono_set Ioo_subset_Ico_self
    _ = _ := by rw [he, setLIntegral_iUnion_of_directed f hd]
    _ ≤ _ := iSup_le (fun n => hbound (U n) (hU n))

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Proposition 3.4's terminal iterated energy bound and finiteness for
the actual radial derivative remainder, conditional only on the stated
late-smallness input and its numerical thresholds.
Paper `e1a0fd5`, `eq:coercive-remainder-bound`, lines 1233–1236 and 1318. -/
theorem prop34_terminal_actual_energy {u₀ δ ε : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (hbudget : ε ^ 2 ≤ (1 - 3 * δ) * weightedGapConstant ui S * (3 - δ) / 24)
    (hcontract : (3 * ε / (1 - 3 * δ)) *
      ((weightedGapConstant ui S ^ 2)⁻¹ /
        (Real.exp (-Bstar ui S) * (1 - δ)) * ε) < 1) :
    (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0, ENNReal.ofReal
      (weightedRemainderDensity S (u, v) *
        |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) ≤
          weightedCoerciveBound ui S u₀ δ ε ∧
    (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0, ENNReal.ofReal
      (weightedRemainderDensity S (u, v) *
        |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤ := by
  have hb := terminal_iterated_lintegral_le_of_truncations
    (fun u => ∫⁻ v in Ioc u 0, ENNReal.ofReal
      (weightedRemainderDensity S (u, v) *
        |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2))
    (h.prop34_truncated_actual_iterated_energy_bound hi hu₀ hδ hε hsmall hbudget hcontract)
  exact ⟨hb, hb.trans_lt (h.weightedCoerciveBound_lt_top hi hu₀)⟩

/-- The exact E(a) premise of `main_of_small_mass_and_energy`, with Proposition 3.4 and both
numerical thresholds discharged. The remaining inputs are exactly Propositions 2.7 and 2.8, which
supply late smallness. Paper `e1a0fd5`, `eq:coercive-remainder-bound`, lines 1233–1236 and 1318. -/
theorem coercive_energy_of_decay
    (hmass : UniformMassDecayStatement ui S)
    (hamp : NormalizedScalarAmplitudesVanishStatement ui S) :
    ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤ := by
  obtain ⟨ε, hε, hbudget, hcontract⟩ := exists_weighted_identification_epsilon
    (δ := 1 / 6) (by norm_num) h.weightedGapConstant_pos (Real.exp_pos (-Bstar ui S))
  obtain ⟨a, hi, ha, hsmall⟩ := h.weighted_late_smallness_of_decay hmass hamp
    (by norm_num : (0 : ℝ) < 1 / 6) hε
  exact ⟨a, hi, ha, (h.prop34_terminal_actual_energy hi ha (by norm_num)
    hε.le hsmall hbudget hcontract).2⟩

end StandingFull

end AcExtensionPrinciple

end
