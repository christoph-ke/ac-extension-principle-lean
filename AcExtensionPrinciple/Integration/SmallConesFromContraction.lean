module

public import AcExtensionPrinciple.Integration.SmallCones
public import AcExtensionPrinciple.Integration.DecayFromContraction

/-!
# Small outgoing cones from contraction and finite coercive energy

Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, equations.tex lines 1324–1356.
The decay chain supplies late smallness on a further truncation of any cone
where the Proposition 3.4 energy is finite.
The premises are supplied by `StandingFull.lemma25` in
`Integration/ObservabilityComplete.lean` and `StandingFull.proposition34`
in `Weighted/Prop34.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The exact sequence conclusion of Proposition 3.5 with only Lemma 2.5 and
finite coercive energy on one late region remaining.
Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem small_outgoing_cones_of_contraction_and_energy {H C rho : ℝ}
    (h25 : Lemma25Statement ui S H C rho)
    (henergy : ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  obtain ⟨a, hai, ha0, haE⟩ := henergy
  obtain ⟨b, hbi, hb0, hb⟩ := h.weighted_late_smallness_of_decay
    (h.uniform_mass_decay_of_contraction h25) (h.common_scalar_limit_of_contraction h25).2
    (show 0 < (1 / 4 : ℝ) by norm_num) (show 0 < (1 / 2 : ℝ) by norm_num)
  apply h.small_outgoing_cones_of_coercive_energy (u₀ := max a b) (δ := 1 / 4)
    (ε := 1 / 2) (hai.trans (le_max_left _ _)) (max_lt ha0 hb0) (by norm_num)
    (fun p hp hu => hb p hp ((le_max_right _ _).trans hu))
  exact (lintegral_mono_set (Ioo_subset_Ioo (le_max_left _ _) le_rfl)).trans_lt haE

/-- Proposition 3.5 with the paper's increasing sequence, after selecting a
subsequence of the convergent cones. Only contraction and coercive energy remain.
Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem small_outgoing_bv_cones_of_contraction_and_energy {H C rho : ℝ}
    (h25 : Lemma25Statement ui S H C rho)
    (henergy : ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    ∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  classical
  obtain ⟨u, humem, hu0, hvar⟩ := h.small_outgoing_cones_of_contraction_and_energy h25 henergy
  have hnext : ∀ k : ℕ, ∃ n : ℕ, k < n ∧ u k < u n := fun k =>
    ((eventually_gt_atTop k).and (hu0.eventually (lt_mem_nhds (humem k).2))).exists
  choose N hN huN using hnext
  let f := fun k => N^[k] 0
  have hf : StrictMono f := strictMono_nat_of_lt_succ (fun k => by
    dsimp only [f]; rw [Function.iterate_succ_apply']; exact hN _)
  have huf : StrictMono (fun k => u (f k)) := strictMono_nat_of_lt_succ (fun k => by
    dsimp only [f]; rw [Function.iterate_succ_apply']; exact huN _)
  exact ⟨fun k => u (f k), huf, fun k => humem (f k),
    hu0.comp hf.tendsto_atTop, hvar.comp hf.tendsto_atTop⟩

end AcExtensionPrinciple.StandingFull

end
