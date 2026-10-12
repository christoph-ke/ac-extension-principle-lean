module

public import AcExtensionPrinciple.Minimal.Conventions
public import AcExtensionPrinciple.Redundancy.IncomingScalarConvention

/-!
# Outgoing differentiability of the incoming λ coefficient
Paper `e1a0fd5`, `equations.tex` lines 220–275.
All coefficient continuities have already been derived; outgoing λ AC is absent.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The outgoing mass, radius and logarithmic derivative integrands are continuous off-axis
without outgoing AC of λ. Incoming scalar transport supplies the missing derivative continuity.
Paper `e1a0fd5`, `eq:radius`, `eq:mass`, `eq:wave-psi`, lines 66–92, 222. -/
theorem minimal_expansion_coefficients_continuous {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
    ContinuousOn (fun p => S.massV p.1 p.2) (cylinderScalarRegion ui) ∧
    ContinuousOn (fun p => S.radiusCoeff p.1 p.2) (cylinderScalarRegion ui) ∧
    ContinuousOn (fun p => S.gamma p.1 p.2 * S.varkappa p.1 p.2)
      (cylinderScalarRegion ui) ∧
    ContinuousOn (fun p => q1_blueshift_out_derivative S p.1 p.2)
      (cylinderScalarRegion ui) := by
  have hQ := cylinderScalarRegion_subset ui
  have hr := h.continuous_r.mono hQ
  have hm := h.continuous_m.mono hQ
  have hl := h.continuous_lam.mono hQ
  have hn := h.continuous_nu.mono hQ
  have hφ := h.continuous_phi.mono hQ
  have hrne := fun p (hp : p ∈ cylinderScalarRegion ui) =>
    (h.toQ1StandingCore.r_pos (hQ hp) hp.2.1).ne'
  have hlne := fun p (hp : p ∈ cylinderScalarRegion ui) =>
    (h.toQ1StandingCore.lam_pos (hQ hp)).ne'
  have hμ : ContinuousOn (fun p => S.mu p.1 p.2) (cylinderScalarRegion ui) :=
    (continuousOn_const.mul hm).div hr hrne
  have hμne := fun p (hp : p ∈ cylinderScalarRegion ui) =>
    (sub_pos.mpr (h.toQ1StandingCore.mu_bounds (hQ hp)).2).ne'
  have hden : ContinuousOn (fun p => (1 - S.mu p.1 p.2) * S.r p.1 p.2)
      (cylinderScalarRegion ui) := (continuousOn_const.sub hμ).mul hr
  have hdenne := fun p (hp : p ∈ cylinderScalarRegion ui) =>
    mul_ne_zero (hμne p hp) (hrne p hp)
  have hc : ContinuousOn (fun p => S.radiusCoeff p.1 p.2)
      (cylinderScalarRegion ui) := ((hμ.mul hl).mul hn).div hden hdenne
  have hf := q1_forcing_continuous h.toQ1StandingCore h.continuous_r h.continuous_m
    h.continuous_lam h.continuous_nu h.continuous_phi
  have hψ := q1_dvpsi_continuous_offAxis h.toQ1StandingCore hf
  have hv : ContinuousOn (fun p => S.massV p.1 p.2)
      (cylinderScalarRegion ui) :=
    ((continuousOn_const.sub hμ).mul ((hψ.sub (hl.mul hφ)).pow 2)).div
      (continuousOn_const.mul hl) (fun p hp => mul_ne_zero (by norm_num) (hlne p hp))
  have hA : ContinuousOn (fun p => S.gamma p.1 p.2 * S.varkappa p.1 p.2)
      (cylinderScalarRegion ui) := (hn.div (continuousOn_const.sub hμ) hμne).mul
        (hμ.div hr hrne)
  have hd : ContinuousOn (fun p => q1_mu_out_derivative S p.1 p.2)
      (cylinderScalarRegion ui) :=
    (((continuousOn_const.mul hv).mul hr).sub ((continuousOn_const.mul hm).mul hl)).div
      (hr.pow 2) (fun p hp => pow_ne_zero 2 (hrne p hp))
  refine ⟨hv, hc, hA, ?_⟩
  exact ((((hd.mul hn).add (hμ.mul hc)).mul hden).sub
    ((hμ.mul hn).mul ((hd.neg.mul hr).add ((continuousOn_const.sub hμ).mul hl)))).div
      (hden.pow 2) (fun p hp => pow_ne_zero 2 (hdenne p hp))

/-- The incoming logarithmic coefficient is uniformly Lipschitz in v on proper rectangles.
The compact bound is on its explicitly continuous outgoing derivative. All premises come from
the exact class with outgoing λ AC deleted. Paper `e1a0fd5`, lines 66–92 and 220–275. -/
theorem minimal_blueshift_uniform_outgoing_lipschitz {ui U a b : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) (hab : a ≤ b)
    (hUa : U < a) (hb : b ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Icc ui U, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      dist (S.gamma u x * S.varkappa u x) (S.gamma u y * S.varkappa u y) ≤
        B * dist x y := by
  have hs : Icc ui U ×ˢ Icc a b ⊆ cylinderScalarRegion ui := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans_lt (hUa.trans_le hp.2.1), hp.2.2.trans hb⟩
  obtain ⟨hv, hc, hA, hD⟩ := minimal_expansion_coefficients_continuous h
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.mono hs)
  refine ⟨|B|, abs_nonneg B, ?_⟩
  intro u hu x hx y hy
  have hslice : MapsTo (fun v : ℝ => (u, v)) (Icc a b) (cylinderScalarRegion ui) :=
    fun v hv => hs ⟨hu, hv⟩
  have hlam : ContinuousOn (S.lam u) (Icc a b) :=
    h.continuous_lam.comp (f := fun v : ℝ => (u, v))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => cylinderScalarRegion_subset ui (hslice hw))
  have hmass : ContinuousOn (S.massV u) (Icc a b) :=
    hv.comp (f := fun v : ℝ => (u, v))
      (continuous_const.prodMk continuous_id).continuousOn hslice
  have hcoeff : ContinuousOn (S.radiusCoeff u) (Icc a b) :=
    hc.comp (f := fun v : ℝ => (u, v))
      (continuous_const.prodMk continuous_id).continuousOn hslice
  have hd : ∀ v ∈ Icc a b, HasDerivWithinAt
      (fun w => S.gamma u w * S.varkappa u w)
      (q1_blueshift_out_derivative S u v) (Icc a b) v := by
    intro v hv'
    exact q1_blueshift_hasDerivWithinAt h.toQ1StandingCore hab hu.1
      (hu.2.trans_lt hUa) hb hv' hlam hmass hcoeff
  have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w => S.gamma u w * S.varkappa u w)
    (f' := fun v => q1_blueshift_out_derivative S u v) hd
    (fun v hv' => (hB (u, v) ⟨hu, hv'⟩).trans (le_abs_self B)) (convex_Icc a b) hy hx
  simpa only [dist_eq_norm] using hle


end AcExtensionPrinciple

end
