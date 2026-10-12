module

public import AcExtensionPrinciple.Renormalized.ClassCalculus

/-!
# Renormalized transport on compact characteristic segments

Paper `e1a0fd5`, `equations.tex` lines 1028–1078.
Only the AC datum and its incoming transport, assigned to Lemma 2.2,
remain explicit inputs of the class-level helpers.
These inputs are supplied by `StandingFull.sectionThreeDatumInputs` in
`Integration/DatumRepresentative.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- AC of the pointwise renormalization on a positive-radius segment.
Paper `e1a0fd5`, `eq:renormalized-derivative`, lines 1020–1021 and 1069. -/
theorem ac_renormalized_derivative {r lam m phiV q : ℝ → ℝ} {a b : ℝ}
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hl : AbsolutelyContinuousOnInterval lam a b)
    (hm : AbsolutelyContinuousOnInterval m a b)
    (hv : AbsolutelyContinuousOnInterval phiV a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hr0 : ∀ x ∈ uIcc a b, 0 < r x) (hl0 : ∀ x ∈ uIcc a b, 0 < lam x) :
    AbsolutelyContinuousOnInterval
      (fun x => Renormalized.renormalizedDerivativeOf (r x) (lam x) (m x) (phiV x) (q x))
      a b := by
  have hi := positive_ac_inv hr hr0
  have hl' := positive_ac_inv hl hl0
  have hmu := (hm.const_mul 2).fun_mul hi
  have hA := (hr.fun_mul hl').fun_mul hv
  have hcube : AbsolutelyContinuousOnInterval
      (fun x => (r x / lam x * phiV x) ^ 3 / r x) a b := by
    convert (hA.fun_mul (hA.fun_mul hA)).fun_mul hi using 1
    funext x
    ring
  have hone : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  exact ((hone.fun_sub hmu).fun_mul hl).fun_mul (hq.fun_sub hcube)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming component AC needed by the renormalization follows from the class.
Paper `e1a0fd5`, lines 1043–1069. -/
theorem incoming_components_ac {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => S.r u v) a b ∧
    AbsolutelyContinuousOnInterval (fun u => S.lam u v) a b ∧
    AbsolutelyContinuousOnInterval (fun u => S.m u v) a b ∧
    AbsolutelyContinuousOnInterval (fun u => S.dvphi u v) a b := by
  have ht (x : ℝ) (hx : x ∈ Icc a b) :=
    inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0
  have ho (x : ℝ) (hx : x ∈ Icc a b) :=
    inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0
  have hr := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.radius_in v a x hx.1 (ht x hx))
  have hm := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.mass_in v a x hx.1 (ht x hx))
  have hd := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.dvpsi_in v a x hx.1 (ho x hx))
  have hl := h.lam_ac_in hab ha hb0 hbv hv0
  have hs := inSeg_subset_triangle ha hb0 hbv.le hv0
  obtain ⟨_, _, hf⟩ := h.regularCenter.localBV.scalar_ac_variation (inSeg v a b)
    (isCompact_Icc.prod isCompact_singleton) hs
  have hp := (hf v a b hab Subset.rfl).1
  have hi := positive_ac_inv hr (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact h.r_pos ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩
      (hx.2.trans_lt hbv))
  exact ⟨hr, hl, hm, (hd.fun_sub (hl.fun_mul hp)).fun_mul hi⟩

/-- Incoming renormalized derivative is AC, using the incoming AC datum
provided by Lemma 2.2. Paper `e1a0fd5`, lines 1043 and 1069. -/
theorem renormalizedDerivative_ac_in_of_ac_datum {q : ℝ → ℝ → ℝ} {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hq : AbsolutelyContinuousOnInterval (fun u => q u v) a b) :
    AbsolutelyContinuousOnInterval (fun u => S.renormalizedDerivative q u v) a b := by
  obtain ⟨hr, hl, hm, hv⟩ := h.incoming_components_ac hab ha hb0 hbv hv0
  apply ac_renormalized_derivative hr hl hm hv hq
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.r_pos ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩
      (hx.2.trans_lt hbv)
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.lam_pos (p := (x, v))
      ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩

/-- Incoming renormalized equation a.e., with exactly Lemma 2.2's
`eq:radial-datum-transport` as input. Paper `e1a0fd5`,
`eq:renormalized-incoming-transport`, lines 1028–1030. -/
theorem renormalized_incoming_ae_of_datum_transport {q : ℝ → ℝ → ℝ} {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hq : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => q u v)
      (-2 * S.gamma x v * S.varkappa x v * q x v -
        (S.gamma x v / S.r x v ^ 2) * (S.r x v / S.lam x v * S.dvphi x v) *
          ((S.r x v / S.lam x v * S.dvphi x v) ^ 2 - 3 * S.mu x v)) x) :
    ∀ᵐ x, x ∈ Ioo a b →
      HasDerivAt (fun u => S.renormalizedDerivative q u v)
        (S.incomingFlux x v * S.renormalizedDerivative q x v +
          (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x := by
  filter_upwards [h.incoming_reduced_ae hab ha hb0 hbv hv0, hq] with x hx hqx
  intro hxI
  obtain ⟨hr, hl, hm, _, hv⟩ := hx hxI
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hxI.1.le, hxI.2.trans hb0, (hxI.2.trans hbv).le, hv0⟩
  exact Renormalized.Incoming.renormalized_transport
    (r := fun u => S.r u v) (lam := fun u => S.lam u v) (nu := fun u => S.nu u v)
    (m := fun u => S.m u v) (phiU := fun u => S.duphi u v)
    (phiV := fun u => S.dvphi u v) (q := fun u => q u v) hr hl hm hv (hqx hxI)
    (h.r_pos hp (hxI.2.trans hbv)) (h.lam_pos hp) (h.nu_neg hp) (h.mu_bounds hp).2

/-- Integral form of the incoming renormalized equation on compact segments.
Paper `e1a0fd5`, `eq:renormalized-incoming-transport`, lines 1028–1043.
The two datum inputs are precisely the Lemma 2.2 conclusions. -/
theorem renormalized_incoming_primitive_of_ac_datum {q : ℝ → ℝ → ℝ} {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hqac : AbsolutelyContinuousOnInterval (fun u => q u v) a b)
    (hq : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => q u v)
      (-2 * S.gamma x v * S.varkappa x v * q x v -
        (S.gamma x v / S.r x v ^ 2) * (S.r x v / S.lam x v * S.dvphi x v) *
          ((S.r x v / S.lam x v * S.dvphi x v) ^ 2 - 3 * S.mu x v)) x) :
    IntervalPrimitive (fun u => S.renormalizedDerivative q u v)
      (fun u => S.incomingFlux u v * S.renormalizedDerivative q u v +
        (3 * S.nu u v / S.r u v) * S.dvphi u v * S.renormalizedInteraction u v) a b :=
  ac_integral_eq_sub hab (h.renormalizedDerivative_ac_in_of_ac_datum hab ha hb0 hbv hv0 hqac)
    (h.renormalized_incoming_ae_of_datum_transport hab ha hb0 hbv hv0 hq)

/-- Radial renormalized equation a.e. on compact off-axis cone segments.
Paper `e1a0fd5`, `eq:renormalized-radial-transport`, lines 1032–1069.
The datum derivative premise is Lemma 2.2's definition of `q`. -/
theorem renormalized_radial_ae_of_datum_derivative {q : ℝ → ℝ → ℝ} {u a b : ℝ}
    (hab : a ≤ b) (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0)
    (hq : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (S.outgoingDatum u) (S.lam u x * q u x) x) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (S.renormalizedInteraction u)
      ((S.r u x / S.nu u x * S.duphi u x) * S.renormalizedDerivative q u x -
        (S.lam u x / S.r u x) * S.renormalizedInteraction u x) x := by
  filter_upwards [h.outgoing_reduced_ae hab hu hu0 hua hb0, hq] with x hx hqx
  intro hxI
  obtain ⟨hr, hn, hm, hphi, hv⟩ := hx hxI
  have hp : (u, x) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans hxI.1).le, hxI.2.le.trans hb0⟩
  have hr0 := h.r_pos hp (hua.trans hxI.1)
  have hlpos : ∀ᶠ s in 𝓝 x, 0 < S.lam u s := by
    have hc := continuous_out h.regularCenter.continuous_lam
      (outSeg_subset_triangle hu hu0 hua.le hb0)
    exact (hc.continuousAt (Icc_mem_nhds hxI.1 hxI.2)).eventually
      (lt_mem_nhds (h.lam_pos hp))
  have he : (fun s => (S.lam u s * S.phi u s + S.r u s * S.dvphi u s) / S.lam u s)
      =ᶠ[𝓝 x] S.outgoingDatum u := by
    filter_upwards [hr.continuousAt.eventually_ne (ne_of_gt hr0)] with s hs
    dsimp [SSFields.outgoingDatum, SSFields.dvphi, SSFields.theta]
    field_simp
    ring
  exact Renormalized.Outgoing.interaction_transport hr hn hm hv
    ((hqx hxI).congr_of_eventuallyEq he) hphi hlpos hr0 (h.nu_neg hp) (h.mu_bounds hp).2

/-- Actual radial derivative definition supplies the a.e. datum derivative.
Paper `e1a0fd5`, `eq:radial-datum-derivative`, lines 555–558 and 1064–1065. -/
theorem radialDatumDerivative_ae {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u ≤ a) (hb0 : b ≤ 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) a b) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (S.outgoingDatum u)
      (S.lam u x * S.radialDatumDerivative u x) x := by
  filter_upwards [hP.ae_differentiableAt] with x hx
  intro hxI
  have hp : (u, x) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans hxI.1.le), hxI.2.le.trans hb0⟩
  convert (hx (by simpa [uIcc_of_le hab] using Ioo_subset_Icc_self hxI)).hasDerivAt using 1
  dsimp [SSFields.radialDatumDerivative]
  rw [mul_div_cancel₀ _ (ne_of_gt (h.lam_pos hp))]

/-- The interaction is AC on off-axis segments from cone datum AC and class
component AC. Paper `e1a0fd5`, lines 1043 and 1069. -/
theorem renormalizedInteraction_ac_out_of_ac_datum {u a b : ℝ}
    (hab : a ≤ b) (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) a b) :
    AbsolutelyContinuousOnInterval (S.renormalizedInteraction u) a b := by
  have ht (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb0)
  have ho (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0)
  have hr := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.radius_out u a x hx.1 (ht x hx))
  have hm := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.mass_out u a x hx.1 (ht x hx))
  have hd := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.dupsi_out u a x hx.1 (ho x hx))
  have hn := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.nu_out u a x hx.1 (ho x hx))
  obtain ⟨_, hf, _⟩ := h.regularCenter.localBV.scalar_ac_variation (outSeg u a b)
    (isCompact_singleton.prod isCompact_Icc) (outSeg_subset_triangle hu hu0 hua.le hb0)
  have hp := (hf u a b hab Subset.rfl).1
  have hpoint (x : ℝ) (hx : x ∈ uIcc a b) : (u, x) ∈ pastTriangle ui ∧ u < x := by
    rw [uIcc_of_le hab] at hx
    exact ⟨⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩, hua.trans_le hx.1⟩
  have hi := positive_ac_inv hr (fun x hx => h.r_pos (hpoint x hx).1 (hpoint x hx).2)
  have hni := (positive_ac_inv hn.fun_neg
    (fun x hx => neg_pos.mpr (h.nu_neg (hpoint x hx).1))).fun_neg
  have hmu := (hm.const_mul 2).fun_mul hi
  have hB := (hd.fun_sub (hn.fun_mul hp)).fun_mul hni
  have hone : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hmu.fun_add (((hone.fun_sub hmu).fun_mul (hP.fun_sub hp)).fun_mul hB)).congr
  intro x hx
  have hxp := (hpoint x hx).1
  have hxoff := (hpoint x hx).2
  dsimp [SSFields.renormalizedInteraction, Renormalized.interactionOf,
    massRatio, SSFields.duphi, SSFields.zeta]
  rw [h.outgoing_amplitude_eq hxp hxoff]
  field_simp [ne_of_gt (h.r_pos hxp hxoff), ne_of_lt (h.nu_neg hxp)]

/-- Integral form of radial renormalized transport on off-axis segments.
Paper `e1a0fd5`, `eq:renormalized-radial-transport`, lines 1032–1043. -/
theorem renormalized_radial_primitive_of_ac_datum {q : ℝ → ℝ → ℝ} {u a b : ℝ}
    (hab : a ≤ b) (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) a b)
    (hq : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (S.outgoingDatum u) (S.lam u x * q u x) x) :
    IntervalPrimitive (S.renormalizedInteraction u)
      (fun v => (S.r u v / S.nu u v * S.duphi u v) * S.renormalizedDerivative q u v -
        (S.lam u v / S.r u v) * S.renormalizedInteraction u v) a b :=
  ac_integral_eq_sub hab (h.renormalizedInteraction_ac_out_of_ac_datum hab hu hu0 hua hb0 hP)
    (h.renormalized_radial_ae_of_datum_derivative hab hu hu0 hua hb0 hq)

end StandingFull

end AcExtensionPrinciple

end
