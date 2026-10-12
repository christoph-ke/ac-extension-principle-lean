module

public import AcExtensionPrinciple.Sanity.ClassicalCalculus

/-!
# Classical characteristic integral equations
Paper `e1a0fd5`, lines 66–84 and 220–275, `eq:radius`, `eq:mass`, `eq:wave-psi`;
Christodoulou CPAM p. 1157. AC of the primitive supplies source integrability even at the axis.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Outgoing FTC on a segment in the past triangle. All pointwise premises are discharged
by the corresponding classical equation. Paper `e1a0fd5`, lines 66–84 and 222. -/
theorem classical_primitive_out {ui : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2) (closedTriangle ui))
    (hd : ∀ u v, ui ≤ u → u < v → v < 0 → HasDerivAt (f u) (g u v) v)
    {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ pastTriangle ui) :
    IntervalPrimitive (f u) (g u) a b := by
  apply classical_primitive hab
    (classical_ac_out hf hab (hs.trans (classical_past_subset_closed ui)))
  intro x hx
  have ha := hs (a := (u, a)) ⟨mem_singleton u, le_rfl, hab⟩
  have hb := hs (a := (u, b)) ⟨mem_singleton u, hab, le_rfl⟩
  exact hd u x ha.1 (ha.2.2.1.trans_lt hx.1) (hx.2.trans_le hb.2.2.2)

/-- Incoming FTC on a segment in the past triangle. Paper `e1a0fd5`, lines 66–84 and 222. -/
theorem classical_primitive_in {ui : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2) (closedTriangle ui))
    (hd : ∀ u v, ui < u → u < v → v ≤ 0 →
      HasDerivAt (fun s => f s v) (g u v) u)
    {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui) :
    IntervalPrimitive (fun u => f u v) (fun u => g u v) a b := by
  apply classical_primitive hab
    (classical_ac_in hf hab (hs.trans (classical_past_subset_closed ui)))
  intro x hx
  have ha := hs (a := (a, v)) ⟨⟨le_rfl, hab⟩, mem_singleton v⟩
  have hb := hs (a := (b, v)) ⟨⟨hab, le_rfl⟩, mem_singleton v⟩
  exact hd x v (ha.1.trans_lt hx.1) (hx.2.trans_le hb.2.2.1) hb.2.2.2

namespace ClassicalTriangleSolution

variable {ui : ℝ} {S : SSFields} (h : ClassicalTriangleSolution ui S)
include h

/-- The outgoing radius equation includes segments starting at the axis.
Paper `e1a0fd5`, `eq:radius`, lines 222–243. -/
theorem radius_out {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ pastTriangle ui) :
    IntervalPrimitive (S.r u) (S.lam u) a b :=
  classical_primitive_out h.c1_r h.r_v hab hs

/-- Incoming radius FTC. Paper `e1a0fd5`, `eq:radius`, lines 222–243. -/
theorem radius_in {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui) :
    IntervalPrimitive (fun u => S.r u v) (fun u => S.nu u v) a b :=
  classical_primitive_in h.c1_r h.r_u hab hs

/-- Outgoing scalar primitive, including its axis endpoint.
Paper `e1a0fd5`, `eq:wave-psi`, lines 222–243. -/
theorem psi_out {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ pastTriangle ui) :
    IntervalPrimitive (fun v => S.r u v * S.phi u v) (S.dvpsi u) a b :=
  classical_primitive_out (h.c1_r.mul h.c1_phi) h.psi_v hab hs

/-- Incoming scalar FTC. Paper `e1a0fd5`, `eq:wave-psi`, lines 222–243. -/
theorem psi_in {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui) :
    IntervalPrimitive (fun u => S.r u v * S.phi u v) (fun u => S.dupsi u v) a b :=
  classical_primitive_in (h.c1_r.mul h.c1_phi) h.psi_u hab hs

/-- Outgoing mass FTC; AC proves integrability without dividing by the axis radius.
Paper `e1a0fd5`, `eq:mass`, lines 222–243. -/
theorem mass_out {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ pastTriangle ui) :
    IntervalPrimitive (S.m u) (S.massV u) a b :=
  classical_primitive_out h.c1_m h.m_v hab hs

/-- Incoming mass FTC. Paper `e1a0fd5`, `eq:mass`, lines 222–243. -/
theorem mass_in {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui) :
    IntervalPrimitive (fun u => S.m u v) (fun u => S.massU u v) a b :=
  classical_primitive_in h.c1_m h.m_u hab hs

/-- Incoming expansion FTC, even through the axis endpoint.
Paper `e1a0fd5`, `eq:radius`, line 222. -/
theorem lam_in {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui) :
    IntervalPrimitive (fun u => S.lam u v) (fun u => S.radiusCoeff u v) a b :=
  classical_primitive_in h.c1_lam h.lam_u hab hs

/-- Outgoing expansion FTC, even through the axis endpoint.
Paper `e1a0fd5`, `eq:radius`, line 222. -/
theorem nu_out {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ pastTriangle ui) :
    IntervalPrimitive (S.nu u) (S.radiusCoeff u) a b :=
  classical_primitive_out h.c1_nu h.nu_v hab hs

/-- Incoming outgoing-scalar-derivative FTC. Paper `e1a0fd5`, `eq:wave-psi`, line 222. -/
theorem dvpsi_in {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui) :
    IntervalPrimitive (fun u => S.dvpsi u v) (fun u => S.radiusCoeff u v * S.phi u v) a b :=
  classical_primitive_in h.c1_dvpsi h.dvpsi_u hab hs

/-- Outgoing incoming-scalar-derivative FTC. Paper `e1a0fd5`, `eq:wave-psi`, line 222. -/
theorem dupsi_out {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ pastTriangle ui) :
    IntervalPrimitive (S.dupsi u) (fun v => S.radiusCoeff u v * S.phi u v) a b :=
  classical_primitive_out h.c1_dupsi h.dupsi_v hab hs

/-- Incoming ν is AC on every incoming segment of the past triangle. Paper `e1a0fd5`, lines 220–275;
Christodoulou CPAM p. 1157. -/
theorem nu_ac_in {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui) :
    AbsolutelyContinuousOnInterval (fun u => S.nu u v) a b := by
  exact classical_ac_in (f := fun p : ℝ × ℝ => S.nu p.1 p.2) h.c1_nu hab
    (hs.trans (classical_past_subset_closed ui))

end ClassicalTriangleSolution

end AcExtensionPrinciple

end
