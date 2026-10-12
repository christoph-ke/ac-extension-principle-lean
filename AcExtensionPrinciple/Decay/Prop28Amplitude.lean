module

public import AcExtensionPrinciple.Decay.ClassRayConsequences

/-!
# Uniform smallness of the outgoing scalar amplitude

Paper `e1a0fd5`, lines 952–953: Lemma 2.3, the initial AC tail, and uniform
mass decay imply smallness on every late cone, including its regular vertex.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A one-sided eventual property admits a closed late threshold after ui.
Paper `e1a0fd5`, lines 859 and 964–971; a filter-to-interval helper. -/
theorem decay_exists_threshold {ui : ℝ} {P : ℝ → Prop} (hui : ui < 0)
    (hP : ∀ᶠ u in 𝓝[<] (0 : ℝ), P u) :
    ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧ ∀ u, a ≤ u → u < 0 → P u := by
  obtain ⟨d, hd, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hP
  obtain ⟨a, ha, ha0⟩ := exists_between (show max ui d < 0 from max_lt hui hd)
  refine ⟨a, (le_max_left _ _).trans ha.le, ha0, ?_⟩
  intro u hau hu0
  exact hsub ⟨(le_max_right _ _).trans_lt (ha.trans_le hau), hu0⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Interpolation and uniform mass decay give a uniform vanishing amplitude.
Paper `e1a0fd5`, `eq:ac-interpolation`, lines 952–953. -/
theorem decay_outgoing_amplitude_small (h23 : Lemma23Statement ui S)
    (hmass : UniformMassDecayStatement ui S) :
    ∀ eps : ℝ, 0 < eps → ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      ∀ u v, a ≤ u → u < 0 → u ≤ v → v ≤ 0 →
        |S.dvpsi u v / S.lam u v - S.phi u v| < eps := by
  obtain ⟨C, hC, h23⟩ := h23
  intro eps heps
  let eta := min 1 (eps ^ 3 / (4 * C))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hetae : eta ≤ eps ^ 3 / (4 * C) := min_le_right _ _
  obtain ⟨am, ham, ham0, hmass⟩ := hmass eta heta
  obtain ⟨aw, haw, haw0, hw⟩ := decay_exists_threshold h.initial_negative
    (h.decay_tail_tendsto.eventually (gt_mem_nhds heta))
  refine ⟨max am aw, ham.trans (le_max_left _ _), max_lt ham0 haw0, ?_⟩
  intro u v hau hu0 huv hv0
  have hp : (u, v) ∈ pastTriangle ui := ⟨ham.trans ((le_max_left _ _).trans hau), hu0, huv, hv0⟩
  rcases huv.eq_or_lt with huv | huv
  · subst v
    rw [h.regularCenter.axis_dvpsi_value u ⟨hp.1, hu0, rfl⟩]
    simpa using heps
  · have hm := hmass u v ((le_max_left _ _).trans hau) hu0 huv.le hv0
    have hwlt := hw u ((le_max_right _ _).trans hau) hu0
    have hw0 := decay_tail_nonneg (ui := ui) (S := S) hu0.le
    have hw1 : initialACTail ui S u ≤ 1 := hwlt.le.trans heta1
    have hwcube : initialACTail ui S u ^ 3 ≤ initialACTail ui S u := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1),
        mul_nonneg (sq_nonneg (initialACTail ui S u)) (sub_nonneg.mpr hw1)]
    have hc := h23 u v hp (h.r_pos hp huv)
    rw [h.decay_outgoing_amplitude hp] at hc
    have hm0 := (h.mu_bounds hp).1
    rw [abs_of_nonneg hm0] at hm
    have hsum : S.mu u v + initialACTail ui S u ^ 3 < 2 * eta := by linarith
    have he' : eta * (4 * C) ≤ eps ^ 3 :=
      (le_div_iff₀ (show 0 < 4 * C by positivity)).mp hetae
    have he : 4 * C * eta ≤ eps ^ 3 := by nlinarith [he']
    have hcube : |S.dvpsi u v / S.lam u v - S.phi u v| ^ 3 < eps ^ 3 := by
      have hs := mul_lt_mul_of_pos_left hsum hC
      nlinarith [pow_pos heps 3]
    by_contra hnot
    have hpow := pow_le_pow_left₀ heps.le (not_lt.mp hnot) 3
    linarith

end StandingFull

end AcExtensionPrinciple

end
