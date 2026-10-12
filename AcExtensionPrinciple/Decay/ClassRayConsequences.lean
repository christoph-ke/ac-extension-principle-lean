module

public import AcExtensionPrinciple.Decay.ClassScalarStatements
public import AcExtensionPrinciple.GeometricBounds.Kappa
public import AcExtensionPrinciple.GeometricBounds.TerminalBlueshift

/-!
# Characteristic consequences used by the decay chain

Paper `e1a0fd5`, `equations.tex` lines 537–543 and 847–989.
All geometric and algebraic premises here are discharged from the standing
class, including the corrected axis-value equalities.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Nonnegative mass, including the axis. Paper `e1a0fd5`, lines 851–867. -/
theorem decay_mass_nonneg {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) : 0 ≤ S.m u v := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · change u = v at he
    subst v
    rw [(h.regularCenter.localBV.axis_values u hp).2]
  · have hm := (h.mu_bounds hp).1
    change 0 ≤ 2 * S.m u v / S.r u v at hm
    have hh := (le_div_iff₀ (h.r_pos hp he)).mp hm
    nlinarith

/-- Outward mass monotonicity on each cone. Paper `e1a0fd5`, lines 851–867, 918–924. -/
theorem decay_mass_out_le {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u ≤ a) (hb0 : b ≤ 0) : S.m u a ≤ S.m u b := by
  have hi := h.regularCenter.localBV.mass_out u a b hab
    (outSeg_subset_triangle hu hu0 hua hb0)
  have hn : 0 ≤ ∫ v in a..b, S.massV u v := by
    apply intervalIntegral.integral_nonneg hab
    intro v hv
    have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hua.trans hv.1, hv.2.trans hb0⟩
    exact div_nonneg (mul_nonneg (sub_pos.mpr (h.mu_bounds hp).2).le (sq_nonneg _))
      (mul_nonneg (by norm_num) (h.lam_pos hp).le)
  linarith [hi.2]

/-- Mass is nonincreasing in outgoing time. Paper `e1a0fd5`, lines 851–867. -/
theorem decay_mass_in_le {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b ≤ v) (hv0 : v ≤ 0) : S.m b v ≤ S.m a v := by
  have hi := h.regularCenter.localBV.mass_in v a b hab
    (inSeg_subset_triangle ha hb0 hbv hv0)
  have hn : (∫ u in a..b, S.massU u v) ≤ 0 := by
    calc
      _ ≤ ∫ _u in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hab hi.1 intervalIntegrable_const
        intro u hu
        have hp : (u, v) ∈ pastTriangle ui :=
          ⟨ha.trans hu.1, hu.2.trans_lt hb0, hu.2.trans hbv, hv0⟩
        exact div_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (sub_pos.mpr (h.mu_bounds hp).2).le (sq_nonneg _))
          (by nlinarith [h.nu_neg hp] : 2 * S.nu u v ≤ 0)
      _ = 0 := by simp
  linarith [hi.2]

/-- Radius is strictly increasing in the incoming label. Paper `e1a0fd5`,
`eq:radius-from-axis`, lines 664–674 and 918–924. -/
theorem decay_radius_out_strict {u a b : ℝ} (hab : a < b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u ≤ a) (hb0 : b ≤ 0) : S.r u a < S.r u b := by
  have hi := h.regularCenter.localBV.radius_out u a b hab.le
    (outSeg_subset_triangle hu hu0 hua hb0)
  have hl : Real.exp (-Bstar ui S) * (b - a) ≤ ∫ v in a..b, S.lam u v := by
    calc
      _ = ∫ _v in a..b, Real.exp (-Bstar ui S) := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hi.1
        (fun v hv => (h.lam_bounds (p := (u, v))
          ⟨hu, hu0, hua.trans hv.1, hv.2.trans hb0⟩).1)
  have hp := mul_pos (Real.exp_pos (-Bstar ui S)) (sub_pos.mpr hab)
  linarith [hi.2]

/-- Continuous mass ratio away from the axis. Paper `e1a0fd5`, line 869. -/
theorem decay_continuous_mu :
    ContinuousOn (fun p => S.mu p.1 p.2) {p ∈ pastTriangle ui | p.1 < p.2} := by
  have hs : {p ∈ pastTriangle ui | p.1 < p.2} ⊆ pastTriangle ui := fun _ hp => hp.1
  exact (continuousOn_const.mul (h.regularCenter.continuous_m.mono hs)).div
    (h.regularCenter.continuous_r.mono hs) (fun p hp => ne_of_gt (h.r_pos hp.1 hp.2))

/-- The outgoing normalized amplitude identity extends to the regular axis.
Paper `e1a0fd5`, `eq:normalized-scalar-derivatives`, lines 247–260 and 952–989. -/
theorem decay_outgoing_amplitude {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) :
    S.r u v / S.lam u v * S.dvphi u v = S.dvpsi u v / S.lam u v - S.phi u v := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · change u = v at he
    subst v
    rw [h.regularCenter.axis_dvpsi_value u ⟨hp.1, hp.2.1, rfl⟩]
    simp [SSFields.dvphi, (h.regularCenter.localBV.axis_values u hp).1]
  · have hr := ne_of_gt (h.r_pos hp he)
    have hl := ne_of_gt (h.lam_pos hp)
    unfold SSFields.dvphi SSFields.theta
    field_simp

/-- The incoming normalized amplitude identity extends to the regular axis.
Paper `e1a0fd5`, `eq:normalized-scalar-derivatives`, lines 247–260 and 987–989. -/
theorem decay_incoming_amplitude {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) :
    S.r u v / S.nu u v * S.duphi u v = S.dupsi u v / S.nu u v - S.phi u v := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · change u = v at he
    subst v
    rw [h.regularCenter.axis_dupsi_value u ⟨hp.1, hp.2.1, rfl⟩]
    simp [SSFields.duphi, (h.regularCenter.localBV.axis_values u hp).1]
  · have hr := ne_of_gt (h.r_pos hp he)
    have hn := ne_of_lt (h.nu_neg hp)
    unfold SSFields.duphi SSFields.zeta
    field_simp

omit h in
/-- Nonnegative initial AC tail on a proper late cone.
Paper `e1a0fd5`, `eq:initial-ac-tail`, lines 537–543. -/
theorem decay_tail_nonneg {u : ℝ} (hu : u ≤ 0) : 0 ≤ initialACTail ui S u := by
  exact intervalIntegral.integral_nonneg_of_forall hu (fun _ => abs_nonneg _)

/-- Initial AC makes its variation tail tend to zero.
Paper `e1a0fd5`, `eq:initial-ac-tail`, lines 537–543. -/
theorem decay_tail_tendsto : Tendsto (initialACTail ui S) (𝓝[<] 0) (𝓝 0) :=
  h.initialACTail_tendsto_zero

end AcExtensionPrinciple.StandingFull

end
