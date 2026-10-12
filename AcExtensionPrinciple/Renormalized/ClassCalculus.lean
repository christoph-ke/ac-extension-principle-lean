module

public import AcExtensionPrinciple.Renormalized.ClassVariation
public import AcExtensionPrinciple.Solution.Raychaudhuri

/-!
# Reduced characteristic equations recovered from the integral class

Paper `e1a0fd5`, `equations.tex` lines 1043–1069.
All component derivative premises are discharged from the solution class.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A scalar derivative follows from the radius and scalar-product derivatives.
Paper `e1a0fd5`, `eq:normalized-scalar-derivatives`, lines 94–99 and 1069. -/
theorem scalar_derivative_of_product {r phi : ℝ → ℝ} {x rd P : ℝ}
    (hr : HasDerivAt r rd x) (hp : HasDerivAt (fun s => r s * phi s) P x)
    (hr0 : r x ≠ 0) : HasDerivAt phi ((P - rd * phi x) / r x) x := by
  apply ((hp.div hr hr0).congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp
  · filter_upwards [hr.continuousAt.eventually_ne hr0] with s hs
    exact (mul_div_cancel_left₀ (phi s) hs).symm

/-- Differentiating the opposite scalar amplitude gives the wave equation.
Paper `e1a0fd5`, `eq:wave-phi`, lines 78–80 and 1062–1069. -/
theorem mixed_scalar_derivative {r e phi P : ℝ → ℝ} {x rd ed D : ℝ}
    (hr : HasDerivAt r rd x) (he : HasDerivAt e ed x)
    (hP : HasDerivAt P (ed * phi x) x) (hphi : HasDerivAt phi D x)
    (hr0 : r x ≠ 0) :
    HasDerivAt (fun s => (P s - e s * phi s) / r s)
      (-(rd / r x) * ((P x - e x * phi x) / r x) - (e x / r x) * D) x := by
  convert (hP.sub (he.mul hphi)).div hr hr0 using 1
  dsimp
  field_simp
  ring

/-- Outgoing mass integrand in the reduced ray notation. Paper `e1a0fd5`,
`eq:mass`, lines 74–77 and 1062–1063. -/
theorem SSFields.massV_eq (S : SSFields) {u v : ℝ} (hr : S.r u v ≠ 0)
    (hl : S.lam u v ≠ 0) (hgap : 1 - S.mu u v ≠ 0) :
    S.massV u v = S.r u v ^ 2 / (2 * S.kappa u v) * S.dvphi u v ^ 2 := by
  unfold SSFields.massV SSFields.kappa kappaOf SSFields.dvphi
  field_simp

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The five reduced incoming equations needed by the renormalization hold a.e.
Paper `e1a0fd5`, `eq:radius`, `eq:mass`, `eq:wave-phi`, lines 1043–1059.
The separate radial-datum transport is the Lemma 2.2 input. -/
theorem incoming_reduced_ae {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b →
      HasDerivAt (fun u => S.r u v) (S.nu x v) x ∧
      HasDerivAt (fun u => S.lam u v) (S.kappa x v * S.varkappa x v * S.nu x v) x ∧
      HasDerivAt (fun u => S.m u v)
        (S.r x v ^ 2 / (2 * S.gamma x v) * S.duphi x v ^ 2) x ∧
      HasDerivAt (fun u => S.phi u v) (S.duphi x v) x ∧
      HasDerivAt (fun u => S.dvphi u v)
        (-(S.nu x v / S.r x v) * S.dvphi x v -
          (S.lam x v / S.r x v) * S.duphi x v) x := by
  have ht (x : ℝ) (hx : x ∈ Icc a b) :=
    inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0
  have ho (x : ℝ) (hx : x ∈ Icc a b) :=
    inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0
  have hr := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.radius_in v a x hx.1 (ht x hx))
  have hp := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.psi_in v a x hx.1 (ht x hx))
  have hm := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.mass_in v a x hx.1 (ht x hx))
  have hl := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.lam_in v a x hx.1 (ho x hx))
  have hd := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.dvpsi_in v a x hx.1 (ho x hx))
  filter_upwards [hr, hp, hm, hl, hd] with x hrx hpx hmx hlx hdx
  intro hx
  have hxp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hx.1.le, hx.2.trans hb0, (hx.2.trans hbv).le, hv0⟩
  have hr0 := ne_of_gt (h.r_pos hxp (hx.2.trans hbv))
  have hn0 := ne_of_lt (h.nu_neg hxp)
  have hg0 := ne_of_gt (sub_pos.mpr (h.mu_bounds hxp).2)
  have hphi := scalar_derivative_of_product (hrx hx) (hpx hx) hr0
  change HasDerivAt (fun u => S.phi u v) (S.duphi x v) x at hphi
  refine ⟨hrx hx, (hlx hx).congr_deriv (S.radiusCoeff_eq x v),
    (hmx hx).congr_deriv (S.massU_eq hr0 hn0 hg0), hphi, ?_⟩
  exact mixed_scalar_derivative (hrx hx) (hlx hx) (hdx hx) hphi hr0

/-- The outgoing reduced equations and scalar derivative hold a.e. on every
compact off-axis cone segment. Paper `e1a0fd5`, lines 1062–1069. -/
theorem outgoing_reduced_ae {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b →
      HasDerivAt (S.r u) (S.lam u x) x ∧
      HasDerivAt (S.nu u) (S.kappa u x * S.varkappa u x * S.nu u x) x ∧
      HasDerivAt (S.m u) (S.r u x ^ 2 / (2 * S.kappa u x) * S.dvphi u x ^ 2) x ∧
      HasDerivAt (S.phi u) (S.dvphi u x) x ∧
      HasDerivAt (S.duphi u)
        (-(S.nu u x / S.r u x) * S.dvphi u x -
          (S.lam u x / S.r u x) * S.duphi u x) x := by
  have ht (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb0)
  have ho (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0)
  have hr := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.radius_out u a x hx.1 (ht x hx))
  have hp := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.psi_out u a x hx.1 (ht x hx))
  have hm := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.mass_out u a x hx.1 (ht x hx))
  have hn := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.nu_out u a x hx.1 (ho x hx))
  have hd := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.dupsi_out u a x hx.1 (ho x hx))
  filter_upwards [hr, hp, hm, hn, hd] with x hrx hpx hmx hnx hdx
  intro hx
  have hxp : (u, x) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans hx.1).le, hx.2.le.trans hb0⟩
  have hr0 := ne_of_gt (h.r_pos hxp (hua.trans hx.1))
  have hl0 := ne_of_gt (h.lam_pos hxp)
  have hg0 := ne_of_gt (sub_pos.mpr (h.mu_bounds hxp).2)
  have hphi := scalar_derivative_of_product (hrx hx) (hpx hx) hr0
  change HasDerivAt (S.phi u) (S.dvphi u x) x at hphi
  refine ⟨hrx hx, (hnx hx).congr_deriv (S.radiusCoeff_eq u x),
    (hmx hx).congr_deriv (S.massV_eq hr0 hl0 hg0), hphi, ?_⟩
  convert mixed_scalar_derivative (hrx hx) (hnx hx) (hdx hx) hphi hr0 using 1
  · rfl
  · dsimp [SSFields.duphi, SSFields.zeta]
    ring

/-- Outgoing scalar amplitude expressed through the normalized datum off axis.
Paper `e1a0fd5`, `eq:normalized-scalar-derivatives`, lines 94–99 and 1006. -/
theorem outgoing_amplitude_eq {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    S.r u v / S.lam u v * S.dvphi u v = S.outgoingDatum u v - S.phi u v := by
  unfold SSFields.dvphi SSFields.theta SSFields.outgoingDatum
  field_simp [ne_of_gt (h.r_pos hp huv), ne_of_gt (h.lam_pos hp)]

/-- Incoming scalar amplitude expressed through its normalized datum off axis.
Paper `e1a0fd5`, `eq:normalized-scalar-derivatives`, lines 94–99 and 1071. -/
theorem incoming_amplitude_eq {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    S.r u v / S.nu u v * S.duphi u v = S.dupsi u v / S.nu u v - S.phi u v := by
  unfold SSFields.duphi SSFields.zeta
  field_simp [ne_of_gt (h.r_pos hp huv), ne_of_lt (h.nu_neg hp)]

end StandingFull

end AcExtensionPrinciple

end
