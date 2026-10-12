module

public import AcExtensionPrinciple.Main.Statement
public import AcExtensionPrinciple.ACDatum.Propagation
public import AcExtensionPrinciple.Continuation.Agreement

/-!
# Selecting and extending small outgoing data

Paper `e1a0fd5`, `equations.tex` `prop:small-outgoing-bv-cones`,
`eq:small-outgoing-bv-cones`,
lines 1324–1330, and the construction in lines 1390–1402.
Proposition 3.5 remains an explicit premise.
The small-cone premise is supplied by `StandingFull.small_outgoing_cones_of_energy`
in `Integration/SmallConesFromEnergy.lean`, using `StandingFull.proposition34`
from `Weighted/Prop34.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- The outgoing-cone sequence supplied by Proposition 3.5.
Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1330. -/
@[expose] def SmallOutgoingConesStatement (ui : ℝ) (S : SSFields) : Prop :=
  ∃ us : ℕ → ℝ, (∀ n, us n ∈ Ioo ui 0) ∧
    Tendsto us atTop (𝓝 0) ∧
    Tendsto (fun n => eVariationOn
      (fun v => S.dvpsi (us n) v / S.lam (us n) v) (Icc (us n) 0)) atTop (𝓝 0)

/-- Multiplication of a real datum scales its variation exactly.
Paper `e1a0fd5`, `eq:continuation-initial-datum`, lines 1396–1402. -/
theorem variation_const_mul (c : ℝ) (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => c * f x) s = ENNReal.ofReal |c| * eVariationOn f s := by
  unfold eVariationOn
  rw [ENNReal.mul_iSup]
  congr 1
  funext p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [edist_eq_enorm_sub, edist_eq_enorm_sub, ← mul_sub, enorm_mul,
    Real.enorm_eq_ofReal_abs]

/-- Choose a cone whose half-variation is below any positive threshold.
Paper `e1a0fd5`, lines 1390–1391. -/
theorem SmallOutgoingConesStatement.choose {ui : ℝ} {S : SSFields}
    (h : SmallOutgoingConesStatement ui S) {ε : ℝ} (hε : 0 < ε) :
    ∃ ū ∈ Ioo ui 0, ENNReal.ofReal (1 / 2 : ℝ) *
      eVariationOn (fun v => S.dvpsi ū v / S.lam ū v) (Icc ū 0) < ENNReal.ofReal ε := by
  rcases h with ⟨us, hus, _, hTV⟩
  have ht : Tendsto (fun n => ENNReal.ofReal (1 / 2 : ℝ) * eVariationOn
      (fun v => S.dvpsi (us n) v / S.lam (us n) v) (Icc (us n) 0)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul
      (a := ENNReal.ofReal (1 / 2 : ℝ)) (b := 0) tendsto_const_nhds (Or.inr (by simp)) hTV
      (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  exact ⟨us n, hus n, hn⟩

/-- Constant extension of the half-normalized datum in the selected chart.
Paper `e1a0fd5`, `eq:continuation-initial-datum`, lines 1396–1402.
Its values below zero have no role in the external existence input. -/
@[expose] noncomputable def selectedInitialDatum (S : SSFields) (ū : ℝ)
    (T : ℝ ≃o ℝ) (v : ℝ) : ℝ :=
  1 / 2 * (S.dvpsi ū (T.symm (min v (T 0))) / S.lam ū (T.symm (min v (T 0))))

/-- The extension agrees with the radial-gauge datum on the selected segment.
Paper `e1a0fd5`, `eq:continuation-initial-datum`, lines 1396–1400. -/
theorem selectedInitialDatum_on_segment (S : SSFields) (ū : ℝ) (T : ℝ ≃o ℝ)
    {v : ℝ} (hv : v ≤ T 0) :
    selectedInitialDatum S ū T v = 1 / 2 * (S.dvpsi ū (T.symm v) / S.lam ū (T.symm v)) := by
  simp [selectedInitialDatum, min_eq_left hv]

/-- The derivative datum stays constant beyond the selected endpoint.
Paper `e1a0fd5`, lines 1401–1402. -/
theorem selectedInitialDatum_constant (S : SSFields) (ū : ℝ) (T : ℝ ≃o ℝ)
    {v : ℝ} (hv : T 0 ≤ v) :
    selectedInitialDatum S ū T v = 1 / 2 * (S.dvpsi ū 0 / S.lam ū 0) := by
  simp [selectedInitialDatum, min_eq_right hv]

/-- Continuity on the complete initial cone, hence the right continuity E1
requires, follows from the standing class. Paper `e1a0fd5`, lines 1396–1402. -/
theorem StandingFull.selectedInitialDatum_continuous {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ}
    (hv : T ū = 0) : ContinuousOn (selectedInitialDatum S ū T) (Ici 0) := by
  apply ((h.normalized_datum_continuous_out hū.1.le hū.2).comp
    (T.symm.continuous.comp (continuous_id.min continuous_const)).continuousOn ?_).const_mul
  intro v hv0
  constructor
  · rw [← T.symm_apply_apply ū, hv]
    exact T.symm.monotone (le_min hv0 (by simpa only [hv] using T.monotone hū.2.le))
  · exact T.symm.monotone (min_le_right _ _) |>.trans_eq (T.symm_apply_apply 0)

/-- The complete datum has exactly half the original closed-cone variation.
The vertex is omitted by E1; continuity makes its contribution zero.
Paper `e1a0fd5`, lines 1401–1402. -/
theorem StandingFull.selectedInitialDatum_variation {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ}
    (hv : T ū = 0) :
    eVariationOn (selectedInitialDatum S ū T) (Ioi 0) = ENNReal.ofReal (1 / 2 : ℝ) *
      eVariationOn (fun v => S.dvpsi ū v / S.lam ū v) (Icc ū 0) := by
  have hb : 0 < T 0 := by simpa only [hv] using T.strictMono hū.2
  have himage : (fun v => T.symm (min v (T 0))) '' Ioi 0 = Ioc ū 0 := by
    ext x
    constructor
    · rintro ⟨v, hv0, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← T.symm_apply_apply ū, hv]
        exact T.symm.strictMono (lt_min hv0 hb)
      · simpa only [T.symm_apply_apply] using T.symm.monotone (min_le_right v (T 0))
    · intro hx
      refine ⟨T x, ?_, ?_⟩
      · rw [← hv]
        exact T.strictMono hx.1
      · dsimp only
        rw [min_eq_left (T.monotone hx.2), T.symm_apply_apply]
  have hcont := h.normalized_datum_continuous_out hū.1.le hū.2 ū ⟨le_rfl, hū.2.le⟩
  have hvertex : ContinuousWithinAt (fun v => S.dvpsi ū v / S.lam ū v) (Ici ū) ū := by
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hū.2] using hcont
  change eVariationOn (fun v => (1 / 2 : ℝ) *
    (S.dvpsi ū (T.symm (min v (T 0))) / S.lam ū (T.symm (min v (T 0))))) _ = _
  rw [variation_const_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have he := variation_comp_monotoneOn (fun v => S.dvpsi ū v / S.lam ū v)
    (fun v => T.symm (min v (T 0))) (Ioi 0) (fun _ _ _ _ hab =>
      T.symm.monotone (min_le_min_right _ hab))
  rw [he, himage,
    eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt hvertex]

end AcExtensionPrinciple

end
