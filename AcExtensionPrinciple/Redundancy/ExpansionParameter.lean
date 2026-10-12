module

public import AcExtensionPrinciple.Redundancy.OutgoingScalarConvention
public import AcExtensionPrinciple.Redundancy.ExpansionInterior
public import AcExtensionPrinciple.GeometricBounds.RayBounds

/-!
# Outgoing regularity of incoming expansion transport
Paper commit `e1a0fd5`, `equations.tex` lines 66–92 and 220–275,
`eq:radius`, `eq:mass`, `eq:logarithmic-expansions`.
The incoming integrating factor has a bounded outgoing derivative on every
proper off-axis rectangle, without assuming outgoing AC of λ.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A continuous interval integrand gives the prescribed derivative within the closed interval.
The characteristic primitives discharge these premises. Paper `e1a0fd5`, lines 66–84, 222. -/
theorem q1_primitive_hasDerivWithinAt {f g : ℝ → ℝ} {a b x : ℝ}
    (_hab : a ≤ b) (hx : x ∈ Icc a b) (hg : ContinuousOn g (Icc a b))
    (h : ∀ y ∈ Icc a b, IntervalPrimitive f g a y) :
    HasDerivWithinAt f (g x) (Icc a b) x := by
  have : Fact (x ∈ Icc a b) := ⟨hx⟩
  have hd := (intervalIntegral.integral_hasDerivWithinAt_right (h x hx).1
    (s := Icc a b) (t := Icc a b)
    ⟨Icc a b, self_mem_nhdsWithin, hg.aestronglyMeasurable measurableSet_Icc⟩
    (hg x hx)).add_const (f a)
  apply hd.congr
  · intro y hy
    linarith [(h y hy).2]
  · linarith [(h x hx).2]

/-- Incoming log λ transport requires no additional expansion regularity.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 87–89 and 222. -/
theorem Q1StandingCore.log_lam_primitive {ui v a b : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => Real.log (S.lam u v))
      (fun u => S.gamma u v * S.varkappa u v) a b := by
  have hp := fun x (hx : x ∈ Icc a b) => h.regularCenter.localBV.lam_in v a x hx.1
    (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)
  have hac := intervalPrimitive_ac hab hp
  apply ac_integral_eq_sub hab (positive_ac_log hac ?_)
  · have hd := intervalPrimitive_ae_hasDerivAt hab hp
    filter_upwards [hd] with x hx
    intro hxI
    have hxQ : (x, v) ∈ pastTriangle ui :=
      ⟨ha.trans hxI.1.le, hxI.2.trans hb0, (hxI.2.trans hbv).le, hv0⟩
    exact IncomingRay.log_lam (r := fun s => S.r s v) (m := fun s => S.m s v)
      (nu := fun s => S.nu s v)
      ((hx hxI).congr_deriv (S.radiusCoeff_eq x v)) (h.lam_pos hxQ)
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.lam_pos (p := (x, v))
      ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩

/-- Outgoing derivative of μ, expressed using the primitive integrands.
Paper `e1a0fd5`, `eq:mass`, lines 74–77. -/
@[expose] noncomputable def q1_mu_out_derivative (S : SSFields) (u v : ℝ) : ℝ :=
  (2 * S.massV u v * S.r u v - 2 * S.m u v * S.lam u v) / S.r u v ^ 2

/-- Outgoing derivative of the incoming logarithmic expansion coefficient.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 87–89. -/
@[expose] noncomputable def q1_blueshift_out_derivative (S : SSFields) (u v : ℝ) : ℝ :=
  let d := q1_mu_out_derivative S u v
  ((d * S.nu u v + S.mu u v * S.radiusCoeff u v) * ((1 - S.mu u v) * S.r u v) -
    S.mu u v * S.nu u v * (-d * S.r u v + (1 - S.mu u v) * S.lam u v)) /
      ((1 - S.mu u v) * S.r u v) ^ 2

/-- The incoming logarithmic coefficient has its explicit outgoing derivative on a rectangle.
Only r, m and ν are differentiated. Their primitive equations discharge the premises.
Paper `e1a0fd5`, `eq:radius`, `eq:mass`, `eq:logarithmic-expansions`, lines 66–92, 222. -/
theorem q1_blueshift_hasDerivWithinAt {ui u a b v : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hab : a ≤ b) (hu : ui ≤ u) (hua : u < a)
    (hb : b ≤ 0) (hv : v ∈ Icc a b)
    (hr : ContinuousOn (S.lam u) (Icc a b))
    (hm : ContinuousOn (S.massV u) (Icc a b))
    (hn : ContinuousOn (S.radiusCoeff u) (Icc a b)) :
    HasDerivWithinAt (fun w => S.gamma u w * S.varkappa u w)
      (q1_blueshift_out_derivative S u v) (Icc a b) v := by
  have hp : (u, v) ∈ pastTriangle ui :=
    ⟨hu, hua.trans_le (hab.trans hb), (hua.trans_le hv.1).le, hv.2.trans hb⟩
  have hs := fun x (hx : x ∈ Icc a b) =>
    outSeg_subset_triangle hu hp.2.1 hua.le (hx.2.trans hb)
  have hdr := q1_primitive_hasDerivWithinAt hab hv hr (fun x hx =>
    h.regularCenter.localBV.radius_out u a x hx.1 (hs x hx))
  have hdm := q1_primitive_hasDerivWithinAt hab hv hm (fun x hx =>
    h.regularCenter.localBV.mass_out u a x hx.1 (hs x hx))
  have hdn := q1_primitive_hasDerivWithinAt hab hv hn (fun x hx =>
    h.regularCenter.localBV.nu_out u a x hx.1
      (outSeg_subset_offAxis hu hp.2.1 hua (hx.2.trans hb)))
  have hμ : HasDerivWithinAt (S.mu u) (q1_mu_out_derivative S u v) (Icc a b) v := by
    exact (hdm.const_mul 2).div hdr (h.r_pos hp (hua.trans_le hv.1)).ne'
  have hden := (hμ.const_sub 1).mul hdr
  have hd := (hμ.mul hdn).div hden
    (mul_ne_zero (sub_pos.mpr (h.mu_bounds hp).2).ne'
      (h.r_pos hp (hua.trans_le hv.1)).ne')
  convert hd using 1
  · funext w
    simp only [SSFields.gamma, SSFields.varkappa, gammaOf, varkappaOf,
      Pi.mul_apply, Pi.div_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  · rfl

/-- The outgoing mass, radius and logarithmic derivative integrands are continuous off-axis
without outgoing AC of λ. Incoming scalar transport supplies the missing derivative continuity.
Paper `e1a0fd5`, `eq:radius`, `eq:mass`, `eq:wave-psi`, lines 66–92, 222. -/
theorem q1_expansion_coefficients_continuous {ui : ℝ} {S : SSFields}
    (h : StandingWithout_ac_lam_out ui S) :
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
theorem q1_blueshift_uniform_outgoing_lipschitz {ui U a b : ℝ} {S : SSFields}
    (h : StandingWithout_ac_lam_out ui S) (hab : a ≤ b)
    (hUa : U < a) (hb : b ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Icc ui U, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      dist (S.gamma u x * S.varkappa u x) (S.gamma u y * S.varkappa u y) ≤
        B * dist x y := by
  have hs : Icc ui U ×ˢ Icc a b ⊆ cylinderScalarRegion ui := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans_lt (hUa.trans_le hp.2.1), hp.2.2.trans hb⟩
  obtain ⟨hv, hc, hA, hD⟩ := q1_expansion_coefficients_continuous h
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
