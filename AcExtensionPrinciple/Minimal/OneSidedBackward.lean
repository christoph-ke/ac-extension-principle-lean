module

public import AcExtensionPrinciple.Minimal.OneSidedDamping
public import AcExtensionPrinciple.Minimal.OneSidedAxisControl

/-!
# Backward incoming damping of the outgoing normalized datum

Paper `e1a0fd5`, `equations.tex` lines 99–105, 247–261,
`eq:normalized-scalar-transport`, `eq:regular-axis-scalar-traces`.
The transport has the damping sign when followed backward from the axis.
Thus joint φ continuity suffices without λ continuity or a blueshift-tail estimate.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- An AC function with nonnegative derivative above a barrier cannot exceed
the barrier before a terminal value below it. Paper `e1a0fd5`, lines 99–105,
backward form of `eq:normalized-scalar-transport`. -/
theorem oneSided_reverse_upper_barrier {Q : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hQ : AbsolutelyContinuousOnInterval Q a b) (hb : Q b ≤ M)
    (hd : ∀ᵐ x, x ∈ Ioo a b → M < Q x → 0 ≤ deriv Q x) : Q a ≤ M := by
  let F := fun x => max (Q x - M) 0
  have hsub := hQ.sub ((LipschitzWith.const M).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hF : AbsolutelyContinuousOnInterval F a b :=
    (LipschitzWith.id.max_const 0).comp_absolutelyContinuousOnInterval hsub
  have hdF : ∀ᵐ x, x ∈ Ioo a b → 0 ≤ deriv F x := by
    filter_upwards [hd] with x hx hxI
    have hcont : ContinuousAt Q x := hQ.continuousOn.continuousAt
      (by simpa [uIcc_of_le hab] using Icc_mem_nhds hxI.1 hxI.2)
    rcases lt_trichotomy (Q x) M with hlt | heq | hgt
    · have hevent : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with y hy
        exact max_eq_right (by linarith : Q y - M ≤ 0)
      rw [hevent.deriv_eq]
      simp
    · have hmin : IsLocalMin F x := by
        apply Eventually.of_forall
        intro y
        dsimp [F]
        rw [heq, sub_self, max_self]
        exact le_max_right _ _
      rw [hmin.deriv_eq_zero]
    · have hevent : F =ᶠ[𝓝 x] fun y => Q y - M := by
        filter_upwards [hcont.eventually (lt_mem_nhds hgt)] with y hy
        exact max_eq_left (by linarith : 0 ≤ Q y - M)
      rw [hevent.deriv_eq, deriv_sub_const]
      exact hx hxI hgt
  have hint : 0 ≤ ∫ x in a..b, deriv F x := by
    have hle : (∫ _x in a..b, (0 : ℝ)) ≤ ∫ x in a..b, deriv F x := by
      apply intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const
        hF.intervalIntegrable_deriv
      rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
        ae_restrict_iff' measurableSet_Ioo]
      exact hdF
    simpa using hle
  rw [hF.integral_deriv_eq_sub] at hint
  have hFb : F b = 0 := max_eq_right (by linarith : Q b - M ≤ 0)
  have hFa : Q a - M ≤ F a := le_max_left _ _
  linarith

/-- Positive-sign transport confines the datum backward from its terminal value.
Paper `e1a0fd5`, lines 99–105, `eq:normalized-scalar-transport`. -/
theorem oneSided_reverse_comparison {Q phi k : ℝ → ℝ} {a b L M : ℝ}
    (hab : a ≤ b) (hQ : AbsolutelyContinuousOnInterval Q a b)
    (hb : |Q b - L| ≤ M) (hphi : ∀ x ∈ Icc a b, |phi x - L| ≤ M)
    (hk : ∀ᵐ x, x ∈ Ioo a b → 0 ≤ k x)
    (hode : ∀ᵐ x, x ∈ Ioo a b → deriv Q x = k x * (Q x - phi x)) :
    |Q a - L| ≤ M := by
  have hup : Q a ≤ L + M := by
    apply oneSided_reverse_upper_barrier hab hQ (by linarith [(abs_le.mp hb).2])
    filter_upwards [hk, hode] with x hxk hxd hxI hxQ
    rw [hxd hxI]
    exact mul_nonneg (hxk hxI) (by linarith [(abs_le.mp (hphi x (Ioo_subset_Icc_self hxI))).2])
  have hlo : -Q a ≤ -L + M := by
    apply oneSided_reverse_upper_barrier hab hQ.neg (by
      change -Q b ≤ -L + M
      linarith [(abs_le.mp hb).1])
    filter_upwards [hk, hode] with x hxk hxd hxI hxQ
    change -L + M < -Q x at hxQ
    rw [deriv.neg, hxd hxI]
    have hprod := mul_nonneg (hxk hxI) (show 0 ≤ phi x - Q x by
      linarith [(abs_le.mp (hphi x (Ioo_subset_Icc_self hxI))).1])
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The outgoing normalized datum is AC on compact incoming segments from
the dvψ and λ primitives. Paper `e1a0fd5`, lines 99–105, 220–222. -/
theorem StandingAssumptions.oneSided_datum_ac_in {ui v a b : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => S.dvpsi u v / S.lam u v) a b := by
  have hs (x : ℝ) (hx : x ∈ Icc a b) :=
    inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0
  have hd := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.dvpsi_in v a x hx.1 (hs x hx))
  have hl := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.lam_in v a x hx.1 (hs x hx))
  have hi := positive_ac_inv hl (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact h.lam_pos (p := (x, v)) ⟨ha.trans hx.1, hx.2.trans_lt hb0,
      (hx.2.trans_lt hbv).le, hv0⟩)
  simpa only [div_eq_mul_inv] using hd.fun_mul hi

/-- Incoming transport has the positive sign in the u direction, hence damping
backward from the axis. Paper `e1a0fd5`, lines 99–105, `eq:normalized-scalar-transport`. -/
theorem StandingAssumptions.oneSided_datum_deriv_in {ui v a b : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → deriv (fun u => S.dvpsi u v / S.lam u v) x =
      -(S.gamma x v * S.varkappa x v) * (S.dvpsi x v / S.lam x v - S.phi x v) := by
  have hs (x : ℝ) (hx : x ∈ Icc a b) :=
    inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0
  have hd := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.dvpsi_in v a x hx.1 (hs x hx))
  have hl := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.lam_in v a x hx.1 (hs x hx))
  filter_upwards [hd, hl] with x hdx hlx hx
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hx.1.le, hx.2.trans hb0, (hx.2.trans hbv).le, hv0⟩
  have hl0 := (h.lam_pos hp).ne'
  have hc : S.radiusCoeff x v = S.lam x v * (S.gamma x v * S.varkappa x v) := by
    rw [S.radiusCoeff_eq]
    exact radius_coefficient_eq _ _ _ _
  rw [((hdx hx).fun_div (hlx hx) hl0).deriv, hc]
  field_simp [hl0]
  ring

/-- Closed incoming comparison starts from the incoming one-sided axis trace.
Paper `e1a0fd5`, lines 99–105, 247–261, `eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.oneSided_datum_comparison {ui u v L M : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hp : (u, v) ∈ pastTriangle ui) (hv : v < 0)
    (hphi : ∀ s ∈ Icc u v, |S.phi s v - L| ≤ M) :
    |S.dvpsi u v / S.lam u v - L| ≤ M := by
  rcases hp.2.2.1.eq_or_lt with huv | huv
  · change u = v at huv
    subst v
    rw [h.regularCenter.axis_dvpsi_value u ⟨hp.1, hp.2.1, rfl⟩]
    exact hphi u ⟨le_rfl, le_rfl⟩
  · have htr := oneSided_incoming_reparam (f := fun s => S.dvpsi s v / S.lam s v)
      (hp.1.trans_lt huv) (h.regularCenter.axis_dvpsi_in v ⟨hp.1.trans huv.le, hv, rfl⟩)
    have hlim := (htr.sub_const L).abs.max (tendsto_const_nhds (x := M))
    have hb : ∀ᶠ b in 𝓝[<] v,
        |S.dvpsi u v / S.lam u v - L| ≤ max (|S.dvpsi b v / S.lam b v - L|) M := by
      filter_upwards [Ioo_mem_nhdsLT huv] with b hbu
      apply oneSided_reverse_comparison
        (k := fun s => -(S.gamma s v * S.varkappa s v)) hbu.1.le
        (h.oneSided_datum_ac_in hbu.1.le hp.1 (hbu.2.trans hv) hbu.2 hv.le)
        (le_max_left _ _) (fun s hs => (hphi s ⟨hs.1, hs.2.trans hbu.2.le⟩).trans
          (le_max_right _ _))
      · apply ae_of_all
        intro s hs
        have hsp : (s, v) ∈ pastTriangle ui :=
          ⟨hp.1.trans hs.1.le, hs.2.trans (hbu.2.trans hv), hs.2.le.trans hbu.2.le, hv.le⟩
        unfold SSFields.gamma gammaOf SSFields.varkappa varkappaOf
        exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg (h.nu_neg hsp).le
            (sub_pos.mpr (h.mu_bounds hsp).2).le)
          (div_nonneg (h.mu_bounds hsp).1 (h.r_pos hsp (hs.2.trans hbu.2)).le))
      · exact h.oneSided_datum_deriv_in hbu.1.le hp.1 (hbu.2.trans hv) hbu.2 hv.le
    have hh := ge_of_tendsto hlim hb
    rw [max_eq_right (hphi v ⟨huv.le, le_rfl⟩)] at hh
    exact hh

end AcExtensionPrinciple

end
