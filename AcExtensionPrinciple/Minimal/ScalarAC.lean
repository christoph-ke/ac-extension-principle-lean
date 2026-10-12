module

public import AcExtensionPrinciple.Minimal.ScalarAxis
public import AcExtensionPrinciple.Redundancy.ExpansionAC

/-!
# Recover scalar AC after scalar continuity
Paper `e1a0fd5`, `equations.tex` lines 66–84 and 220–275.
Off-axis quotients of primitives are AC. The retained scalar TV bounds
make the derivative integrable; continuity removes the sole endpoint jump.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A continuous BV function AC away from its right endpoint is AC on the entire interval.
For incoming φ the primitive quotient, retained TV bound and derived continuity discharge
these premises. Paper `e1a0fd5`, line 222. -/
theorem minimal_ac_extend_right {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hbv : BoundedVariationOn f (Icc a b))
    (hloc : ∀ c ∈ Ico a b, AbsolutelyContinuousOnInterval f a c) :
    AbsolutelyContinuousOnInterval f a b := by
  have hi : IntervalIntegrable (deriv f) volume a b := by
    have hv : BoundedVariationOn f (uIcc a b) := by
      simpa only [uIcc_of_le hab.le] using hbv
    exact hv.intervalIntegrable_deriv
  let G := fun x => ∫ t in a..x, deriv f t
  have hG : AbsolutelyContinuousOnInterval G a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hfb : Tendsto f (𝓝[<] b) (𝓝 (f b)) := by
    have ht := hc b ⟨hab.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab] at ht
    exact ht.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hGb : Tendsto G (𝓝[<] b) (𝓝 (G b)) := by
    have ht := hG.continuousOn b (by simp [hab.le])
    rw [uIcc_of_le hab.le, ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab] at ht
    exact ht.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have he : ∀ x ∈ Icc a b, f x = G x + (f b - G b) := by
    intro x hx
    rcases hx.2.eq_or_lt with he | he
    · subst x
      ring
    have ht := (hfb.sub hGb).add_const (G x)
    have heq : (fun c => f c - G c + G x) =ᶠ[𝓝[<] b] fun _ => f x := by
      filter_upwards [self_mem_nhdsWithin,
        ((continuous_id.tendsto b).mono_left nhdsWithin_le_nhds).eventually
          (Ioi_mem_nhds he)] with c hc hxc
      change c < b at hc
      change x < c at hxc
      have hac : AbsolutelyContinuousOnInterval f x c :=
        (hloc c ⟨hx.1.trans hxc.le, hc⟩).mono (by
          rw [uIcc_of_le (hx.1.trans hxc.le), uIcc_of_le hxc.le]
          exact Icc_subset_Icc hx.1 le_rfl)
      have hicx : IntervalIntegrable (deriv f) volume a x := hi.mono_set (by
        rw [uIcc_of_le hab.le, uIcc_of_le hx.1]
        exact Icc_subset_Icc le_rfl hx.2)
      have hixc : IntervalIntegrable (deriv f) volume x c := hi.mono_set (by
        rw [uIcc_of_le hab.le, uIcc_of_le hxc.le]
        exact Icc_subset_Icc hx.1 hc.le)
      have hisub := intervalIntegral.integral_add_adjacent_intervals hicx hixc
      have hAc := hac.integral_deriv_eq_sub
      dsimp [G]
      linarith
    have hu := tendsto_nhds_unique (ht.congr' heq) tendsto_const_nhds
    linarith
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f b - G b) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hG.fun_add hconst).congr
  intro x hx
  exact (he x (by simpa only [uIcc_of_le hab.le] using hx)).symm

/-- Outgoing scalar AC on an off-axis segment is the quotient of the ψ and r primitives.
No deleted field is consumed. Paper `e1a0fd5`, `eq:wave-psi`, lines 78–84 and 222. -/
theorem StandingAssumptions.phi_out_ac_offAxis {ui u a b : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hab : a ≤ b) (hs : outSeg u a b ⊆ pastTriangle ui)
    (hua : u < a) : AbsolutelyContinuousOnInterval (S.phi u) a b := by
  have hr := intervalPrimitive_ac hab (fun x hx =>
    h.regularCenter.localBV.radius_out u a x hx.1
      (fun p hp => hs ⟨hp.1, ⟨hp.2.1, hp.2.2.trans hx.2⟩⟩))
  have hψ := intervalPrimitive_ac hab (fun x hx =>
    h.regularCenter.localBV.psi_out u a x hx.1
      (fun p hp => hs ⟨hp.1, ⟨hp.2.1, hp.2.2.trans hx.2⟩⟩))
  have hpos : ∀ x ∈ uIcc a b, 0 < S.r u x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.r_pos (hs ⟨mem_singleton u, hx⟩) (hua.trans_le hx.1)
  apply (hψ.fun_mul (positive_ac_inv hr hpos)).congr
  intro x hx
  simpa only [div_eq_mul_inv] using mul_div_cancel_left₀ _ (hpos x hx).ne'

/-- Incoming scalar AC off-axis follows from the ψ and r primitives.
Paper `e1a0fd5`, `eq:wave-psi`, lines 78–84 and 222. -/
theorem StandingAssumptions.phi_in_ac_offAxis {ui v a b : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui)
    (hbv : b < v) : AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b := by
  have hr := intervalPrimitive_ac hab (fun x hx =>
    h.regularCenter.localBV.radius_in v a x hx.1
      (fun p hp => hs ⟨⟨hp.1.1, hp.1.2.trans hx.2⟩, hp.2⟩))
  have hψ := intervalPrimitive_ac hab (fun x hx =>
    h.regularCenter.localBV.psi_in v a x hx.1
      (fun p hp => hs ⟨⟨hp.1.1, hp.1.2.trans hx.2⟩, hp.2⟩))
  have hpos : ∀ x ∈ uIcc a b, 0 < S.r x v := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.r_pos (hs ⟨hx, mem_singleton v⟩) (hx.2.trans_lt hbv)
  apply (hψ.fun_mul (positive_ac_inv hr hpos)).congr
  intro x hx
  simpa only [div_eq_mul_inv] using mul_div_cancel_left₀ _ (hpos x hx).ne'

/-- Every outgoing scalar trace is AC, including its axis endpoint, from retained TV.
Paper `e1a0fd5`, line 222 and `eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.phi_out_ac {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (u a b : ℝ) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ pastTriangle ui) :
    AbsolutelyContinuousOnInterval (S.phi u) a b := by
  rcases hab.eq_or_lt with he | he
  · subst b; exact AbsolutelyContinuousOnInterval.refl _ _
  have haQ := hs (show (u, a) ∈ outSeg u a b from ⟨mem_singleton u, le_rfl, hab⟩)
  rcases haQ.2.2.1.eq_or_lt with hea | hla
  · change u = a at hea
    subst a
    apply q1_ac_extend_left he
    · exact h.continuous_phi.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun v hv => hs ⟨mem_singleton u, hv⟩)
    · obtain ⟨C, hC, _⟩ := h.regularCenter.localBV.scalar_variation
        (outSeg u u b) (isCompact_singleton.prod isCompact_Icc) hs
      exact ne_top_of_lt ((hC u u b hab Subset.rfl).trans_lt ENNReal.ofReal_lt_top)
    · intro c hc
      exact h.phi_out_ac_offAxis hc.2
        (fun p hp => hs ⟨hp.1, ⟨hc.1.le.trans hp.2.1, hp.2.2⟩⟩) hc.1
  · exact h.phi_out_ac_offAxis hab hs hla

/-- Every incoming scalar trace is AC, including its axis endpoint, from retained TV.
Paper `e1a0fd5`, line 222 and `eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.phi_in_ac {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (v a b : ℝ) (hab : a ≤ b)
    (hs : inSeg v a b ⊆ pastTriangle ui) :
    AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b := by
  rcases hab.eq_or_lt with he | he
  · subst b; exact AbsolutelyContinuousOnInterval.refl _ _
  have hbQ := hs (show (b, v) ∈ inSeg v a b from ⟨⟨hab, le_rfl⟩, mem_singleton v⟩)
  rcases hbQ.2.2.1.eq_or_lt with heb | hlb
  · change b = v at heb
    subst v
    apply minimal_ac_extend_right he
    · exact h.continuous_phi.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => hs ⟨hu, mem_singleton b⟩)
    · obtain ⟨C, _, hC⟩ := h.regularCenter.localBV.scalar_variation
        (inSeg b a b) (isCompact_Icc.prod isCompact_singleton) hs
      exact ne_top_of_lt ((hC b a b hab Subset.rfl).trans_lt ENNReal.ofReal_lt_top)
    · intro c hc
      exact h.phi_in_ac_offAxis hc.1
        (fun p hp => hs ⟨⟨hp.1.1, hp.1.2.trans hc.2.le⟩, hp.2⟩) hc.2
  · exact h.phi_in_ac_offAxis hab hs hlb

end AcExtensionPrinciple

end
