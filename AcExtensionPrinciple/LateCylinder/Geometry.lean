module

public import AcExtensionPrinciple.LateCylinder.Remainder

/-!
# Common geometric constant for late cylinders

Paper `e1a0fd5`, equations.tex lines 742–749 and 814–815.
This predicate duplicates the existing K interface under a distinct name:
Cylinder.Geometry cannot currently be imported with ACDatum because their
radius derivative declarations collide. No solution hypotheses are added.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Uniform bounds needed for radius growth and cylinder variation.
Paper `e1a0fd5`, geometric K facts, lines 742–749. -/
@[expose] def LateCylinderGeometry (ui : ℝ) (S : SSFields) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ p ∈ pastTriangle ui,
    K⁻¹ ≤ S.lam p.1 p.2 ∧ K⁻¹ ≤ 1 - S.mu p.1 p.2 ∧ K⁻¹ ≤ -S.nu p.1 p.2

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Select one geometric K for every subsequent cylinder and small parameter.
Paper `e1a0fd5`, equations.tex lines 742–749. -/
theorem exists_late_cylinder_geometry : ∃ K : ℝ, LateCylinderGeometry ui S K := by
  let L := Real.exp (-Bstar ui S)
  let g := initialGap ui S * L
  have hL : 0 < L := Real.exp_pos _
  have hg : 0 < g := mul_pos h.initialGap_pos hL
  let K := 1 + L⁻¹ + g⁻¹
  have hK1 : 1 ≤ K := by
    dsimp [K]
    linarith [inv_nonneg.mpr hL.le, inv_nonneg.mpr hg.le]
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hKL : L⁻¹ ≤ K := by dsimp [K]; linarith [inv_nonneg.mpr hg.le]
  have hKg : g⁻¹ ≤ K := by dsimp [K]; linarith [inv_nonneg.mpr hL.le]
  have hLi : K⁻¹ ≤ L := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hL) hKL
  have hgi : K⁻¹ ≤ g := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hg) hKg
  exact ⟨K, hK1, fun p hp => ⟨hLi.trans (h.lam_bounds hp).1,
    hgi.trans (h.mass_gap_lower hp), hLi.trans (h.neg_nu_lower hp)⟩⟩

/-- Waiting by Kb/ε bounds the old inverse radius by ε/b.
Paper `e1a0fd5`, equations.tex lines 814–815. -/
theorem late_old_inverse_radius_le {K b eps u0 u v : ℝ}
    (hK : LateCylinderGeometry ui S K) (hb : 0 < b) (heps : 0 < eps)
    (hu0 : ui ≤ u0) (hu : u0 ≤ u) (hu1 : u < 0) (huv : u < v) (hv : v ≤ 0)
    (hr : b ≤ S.r u v) (hwait : K * b / eps ≤ u - u0) :
    1 / S.r u0 v ≤ eps / b := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK.1
  have hg := h.late_incoming_radius_growth (fun _p hp => (hK.2 _ hp).2.2)
    hu0 hu hu1 huv hv
  have hw := mul_le_mul_of_nonneg_left hwait (inv_nonneg.mpr hK0.le)
  have heq : K⁻¹ * (K * b / eps) = b / eps := by field_simp
  rw [heq] at hw
  have hr0 := h.r_pos (u := u0) (v := v)
    ⟨hu0, hu.trans_lt hu1, (hu.trans_lt huv).le, hv⟩ (hu.trans_lt huv)
  apply (div_le_div_iff₀ hr0 hb).mpr
  have hmult := (div_le_iff₀ heps).mp (show b / eps ≤ S.r u0 v by linarith)
  simpa only [one_mul, mul_one, mul_comm] using hmult

/-- Pointwise remainder estimate after the waiting time. The small-source
premise is discharged by Lemma 2.3 on every past incoming exterior segment;
D is supplied by Lemma 2.2. Paper `e1a0fd5`, lines 808–815. -/
theorem late_remainder_le_of_bounds {K B D b eps u0 u v : ℝ}
    (hK : LateCylinderGeometry ui S K) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : 0 < b) (heps : 0 < eps) (hu0 : ui ≤ u0) (hu : u0 ≤ u)
    (hu1 : u < 0) (huv : u < v) (hv : v ≤ 0) (hr : b ≤ S.r u v)
    (hwait : K * b / eps ≤ u - u0)
    (hrem : |radialDatumRemainderIntegral ui S u0 v| ≤ D / S.r u0 v)
    (hs : ∀ s ∈ Icc u0 u,
      |outgoingAmplitude S s v * (outgoingAmplitude S s v ^ 2 - 3 * S.mu s v)| ≤ B * eps) :
    |radialDatumRemainderIntegral ui S u v| ≤
      (D / (K⁻¹) ^ 2 + B / (K⁻¹ * (K⁻¹) ^ 2)) * eps / b := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK.1
  have hiK : 0 < K⁻¹ := inv_pos.mpr hK0
  have hh := h.remainder_dilution_of_bounds hB hD hiK hiK heps.le
    (fun _p hp => (hK.2 _ hp).1) (fun _p hp => (hK.2 _ hp).2.1)
    hrem hs hu0 hu hu1 huv hv
  have h_old := h.late_old_inverse_radius_le hK hb heps hu0 hu hu1 huv hv hr hwait
  have hr0 := h.r_pos (u := u) (v := v) ⟨hu0.trans hu, hu1, huv.le, hv⟩ huv
  have hnew : eps / S.r u v ≤ eps / b := div_le_div_of_nonneg_left heps.le hb hr
  have ho := mul_le_mul_of_nonneg_left h_old
    (show 0 ≤ D / (K⁻¹) ^ 2 by positivity)
  have hn := mul_le_mul_of_nonneg_left hnew
    (show 0 ≤ B / (K⁻¹ * (K⁻¹) ^ 2) by positivity)
  have heq0 : (D / (K⁻¹) ^ 2) / S.r u0 v = (D / (K⁻¹) ^ 2) * (1 / S.r u0 v) := by ring
  have heq1 : B / (K⁻¹ * (K⁻¹) ^ 2) * eps / S.r u v =
      (B / (K⁻¹ * (K⁻¹) ^ 2)) * (eps / S.r u v) := by ring
  rw [heq0, heq1] at hh
  exact hh.trans ((add_le_add ho hn).trans_eq (by ring))

end StandingFull

end AcExtensionPrinciple

end
