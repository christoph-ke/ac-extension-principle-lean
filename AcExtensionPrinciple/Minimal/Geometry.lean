module

public import AcExtensionPrinciple.Minimal.Core
public import AcExtensionPrinciple.Solution.Geometry
public import AcExtensionPrinciple.Cylinder.ScalarRegion

/-!
# Geometric consequences without the additional fields of the full working class
Paper commit `e1a0fd5`, `equations.tex` lines 114–132 and 220–275,
`eq:regular-axis`, `eq:radius-from-axis`. These proofs use only the copied core.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Compact expansion bounds give positive λ, including on the axis. Paper `e1a0fd5`, line 222,
Luk–Oh Definition 2.1(1). -/
theorem StandingAssumptions.lam_pos {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 < S.lam p.1 p.2 := by
  obtain ⟨c, hc, hb⟩ := h.regularCenter.localBV.expansion_bounds {p}
    isCompact_singleton (singleton_subset_iff.mpr hp)
  exact hc.trans_le (hb p (mem_singleton p)).1

/-- The incoming expansion is negative, including on the axis. Paper `e1a0fd5`, line 120 and
`eq:regular-axis`. -/
theorem StandingAssumptions.nu_neg {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : S.nu p.1 p.2 < 0 := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    rw [← he, h.regularCenter.axis_expansions _ ha]
    exact neg_neg_of_pos (h.lam_pos (axis_subset_pastTriangle ui ha))
  · exact (h.signs p hp he).2.1

/-- Radius positivity needs no additional continuity assumption. Paper `e1a0fd5`,
`eq:radius-from-axis`, line 66. -/
theorem StandingAssumptions.r_pos {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) : 0 < S.r u v := by
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2
  obtain ⟨c, hc, hb⟩ := h.regularCenter.localBV.expansion_bounds (outSeg u u v)
    (isCompact_singleton.prod isCompact_Icc) hs
  have hi := h.regularCenter.localBV.radius_out u u v huv.le hs
  have he := hi.2
  rw [(h.regularCenter.localBV.axis_values u
    ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).1, sub_zero] at he
  have hbound : c * (v - u) ≤ S.r u v := by
    rw [he]
    calc
      c * (v - u) = ∫ s in u..v, c := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on huv.le intervalIntegrable_const hi.1
        (fun s hs' => (hb (u, s) ⟨by simp, hs'⟩).1)
  exact (mul_pos hc (sub_pos.mpr huv)).trans_le hbound

/-- Retained field continuities imply continuous off-axis transport forcing; positivity and the
untrapped signs discharge both nonzero denominators. Paper `e1a0fd5`, `eq:radius`, `eq:wave-psi`,
lines 66–84 and 222. -/
theorem minimal_forcing_continuous {ui : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    (hr : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui))
    (hm : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui))
    (hl : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui))
    (hn : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui))
    (hφ : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)) :
    ContinuousOn (fun p => S.radiusCoeff p.1 p.2 * S.phi p.1 p.2)
      (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hmu : ContinuousOn (fun p => S.mu p.1 p.2) (cylinderScalarRegion ui) :=
    (continuousOn_const.mul (hm.mono hs)).div (hr.mono hs)
      (fun p hp => (h.r_pos (hs hp) hp.2.1).ne')
  exact ((((hmu.mul (hl.mono hs)).mul (hn.mono hs)).div
    ((continuousOn_const.sub hmu).mul (hr.mono hs))
      (fun p hp => mul_ne_zero
        (sub_ne_zero.mpr (ne_of_lt (h.signs p (hs hp) hp.2.1).2.2.2).symm)
        (h.r_pos (hs hp) hp.2.1).ne')).mul (hφ.mono hs))

end AcExtensionPrinciple

end
