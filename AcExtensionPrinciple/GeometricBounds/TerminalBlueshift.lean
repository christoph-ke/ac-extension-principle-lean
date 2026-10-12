module

public import AcExtensionPrinciple.Solution.Geometry
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Terminal incoming blueshift via Fatou

Paper `e1a0fd5`, `eq:terminal-blueshift-bound`,
`eq:terminal-blueshift-limit` (lines 301–303 and 352–359). Fatou is applied
with expanding incoming domains; this handles the final improper limit in
the same lower-integral argument.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The blueshift density is continuous away from the axis, including the terminal ray.
Paper `e1a0fd5`, lines 66, 220–275, 352–358. -/
theorem continuous_blueshift :
    ContinuousOn (fun p => -(S.gamma p.1 p.2 * S.varkappa p.1 p.2))
      {p ∈ pastTriangle ui | p.1 < p.2} := by
  let D := {p ∈ pastTriangle ui | p.1 < p.2}
  have hs : D ⊆ pastTriangle ui := fun _ hp => hp.1
  have hr := h.regularCenter.continuous_r.mono hs
  have hm := h.regularCenter.continuous_m.mono hs
  have hn := h.regularCenter.continuous_nu.mono hs
  have hr0 : ∀ p ∈ D, S.r p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (h.r_pos hp.1 hp.2)
  have hmu : ContinuousOn (fun p => S.mu p.1 p.2) D :=
    (continuousOn_const.mul hm).div hr hr0
  have hgap : ∀ p ∈ D, 1 - S.mu p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (sub_pos.mpr (h.mu_bounds hp.1).2)
  exact ((hn.div (continuousOn_const.sub hmu) hgap).mul (hmu.div hr hr0)).neg

/-- G5: the terminal blueshift integral is bounded by the supremum over v < 0.
Paper `e1a0fd5`, `eq:terminal-blueshift-bound`, `eq:terminal-blueshift-limit`. -/
theorem terminal_blueshift_le :
    (∫⁻ u in Ioo ui 0, ENNReal.ofReal (-(S.gamma u 0 * S.varkappa u 0))) ≤
      blueshiftSup ui S := by
  let v : ℕ → ℝ := fun n => ui / ((n : ℝ) + 2)
  have hv : ∀ n, v n ∈ Ioo ui 0 := by
    intro n
    have hn : 1 < (n : ℝ) + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hn0 := lt_trans zero_lt_one hn
    constructor
    · dsimp [v]
      apply (lt_div_iff₀ hn0).mpr
      nlinarith [h.initial_negative]
    · exact div_neg_of_neg_of_pos h.initial_negative hn0
  have ht : Tendsto v atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  let F : ℕ → ℝ → ℝ≥0∞ := fun n =>
    (Ioo ui (v n)).indicator (fun u => ENNReal.ofReal (-(S.gamma u (v n) * S.varkappa u (v n))))
  have hmeas : ∀ n, AEMeasurable (F n) volume := by
    intro n
    apply (aemeasurable_indicator_iff measurableSet_Ioo).mpr
    have hc : ContinuousOn (fun u => -(S.gamma u (v n) * S.varkappa u (v n)))
        (Ioo ui (v n)) := by
      exact h.continuous_blueshift.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨⟨hu.1.le, hu.2.trans (hv n).2, hu.2.le, (hv n).2.le⟩, hu.2⟩)
    exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable measurableSet_Ioo
  have hbound : ∀ n, (∫⁻ u, F n u) ≤ blueshiftSup ui S := by
    intro n
    rw [show (∫⁻ u, F n u) =
        ∫⁻ u in Ioo ui (v n), ENNReal.ofReal (-(S.gamma u (v n) * S.varkappa u (v n))) by
      exact lintegral_indicator measurableSet_Ioo _]
    exact le_iSup_of_le (v n) (le_iSup_of_le (hv n) le_rfl)
  have hlim : ∀ u : ℝ, Tendsto (fun n => F n u) atTop
      (𝓝 ((Ioo ui 0).indicator (fun u => ENNReal.ofReal (-(S.gamma u 0 * S.varkappa u 0))) u)) := by
    intro u
    by_cases hu : u ∈ Ioo ui 0
    · have heu : ∀ᶠ n in atTop, u < v n := ht.eventually (Ioi_mem_nhds hu.2)
      have hp : (u, 0) ∈ {p ∈ pastTriangle ui | p.1 < p.2} :=
        ⟨⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩, hu.2⟩
      have hpair : Tendsto (fun n => (u, v n)) atTop
          (𝓝[{p ∈ pastTriangle ui | p.1 < p.2}] (u, 0)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_const_nhds.prodMk_nhds ht, ?_⟩
        exact heu.mono (fun n hn => ⟨⟨hu.1.le, hu.2, hn.le, (hv n).2.le⟩, hn⟩)
      have hcAt : Tendsto (fun p : ℝ × ℝ => -(S.gamma p.1 p.2 * S.varkappa p.1 p.2))
          (𝓝[{p ∈ pastTriangle ui | p.1 < p.2}] (u, 0))
          (𝓝 (-(S.gamma u 0 * S.varkappa u 0))) := h.continuous_blueshift (u, 0) hp
      have hc0 : Tendsto (fun n => -(S.gamma u (v n) * S.varkappa u (v n)))
          atTop (𝓝 (-(S.gamma u 0 * S.varkappa u 0))) :=
        hcAt.comp hpair
      have hc := (ENNReal.continuous_ofReal.tendsto _).comp hc0
      rw [indicator_of_mem hu]
      apply hc.congr'
      filter_upwards [heu] with n hn
      simp only [F, Function.comp_def, indicator_of_mem (show u ∈ Ioo ui (v n) from ⟨hu.1, hn⟩)]
    · have hout : ∀ n, u ∉ Ioo ui (v n) := by
        intro n hn
        exact hu ⟨hn.1, hn.2.trans (hv n).2⟩
      simp only [F, indicator_of_notMem hu, indicator_of_notMem (hout _)]
      exact tendsto_const_nhds
  calc
    _ = ∫⁻ u, liminf (fun n => F n u) atTop := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro u
      exact (hlim u).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ u, F n u) atTop := lintegral_liminf_le' hmeas
    _ ≤ blueshiftSup ui S := liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently

end StandingFull

end AcExtensionPrinciple

end
