module

public import AcExtensionPrinciple.Cylinder.Geometry
public import AcExtensionPrinciple.Cylinder.TraceCalculus
public import AcExtensionPrinciple.BoundaryEnergy.Stability

/-!
# Boundary energy on a regular solution cylinder

Paper `e1a0fd5`, `equations.tex` lines 674–738,
`lem:boundary-energy-identity`. Comparison uses the solution class directly;
the AC balance helpers expose the remaining trace regularity/chain rules.
The trace calculus and balance are supplied by `StandingFull.lemma24` in
`Integration/CylinderStatements.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Normalized outgoing ψ trace. Paper `e1a0fd5`, lines 690–706, 731–737. -/
@[expose] noncomputable def cylinderP (S : SSFields) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  S.dvpsi u (v u) / S.lam u (v u)

/-- Boundary energy of the actual cylinder fields. Paper `e1a0fd5`,
`eq:boundary-energy`, lines 674–679. -/
@[expose] noncomputable def cylinderEnergy (S : SSFields) (b : ℝ)
    (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  boundaryEnergy b (S.m u (v u)) (cylinderP S v u - S.phi u (v u))

/-- The normalized outgoing amplitude has both expressions used in the paper.
Paper `e1a0fd5`, lines 726–729, `eq:boundary-energy`. -/
theorem cylinder_amplitude_eq {S : SSFields} {b u w : ℝ} (hb : b ≠ 0)
    (hl : S.lam u w ≠ 0) (hr : S.r u w = b) :
    S.dvpsi u w / S.lam u w - S.phi u w = (b / S.lam u w) * S.dvphi u w := by
  simp only [SSFields.dvphi, SSFields.theta, hr]
  field_simp

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The cylinder energy controls enclosed mass and the outgoing scalar square.
Paper `e1a0fd5`, `eq:boundary-energy-comparison`, lines 684–688. -/
theorem cylinder_energy_comparison {v : ℝ → ℝ} {b u : ℝ} (hb : 0 < b)
    (hp : (u, v u) ∈ pastTriangle ui) (hr : S.r u (v u) = b) :
    S.m u (v u) ≤ cylinderEnergy S b v u ∧
      (b / 2) * ((b / S.lam u (v u)) * S.dvphi u (v u)) ^ 2 ≤
        cylinderEnergy S b v u := by
  have hmu : S.mu u (v u) = massRatio b (S.m u (v u)) := by rw [SSFields.mu, hr]
  have hm := h.mu_bounds hp
  rw [hmu] at hm
  constructor
  · exact mass_le_boundaryEnergy hb hm.2
  · unfold cylinderEnergy cylinderP
    rw [cylinder_amplitude_eq hb.ne' (h.lam_pos hp).ne' hr]
    exact scalar_square_le_boundaryEnergy hb hm.1 hm.2

/-- Nonnegative actual cylinder energy. Paper `e1a0fd5`,
`eq:boundary-energy-comparison`, lines 684–688. -/
theorem cylinder_energy_nonneg {v : ℝ → ℝ} {b u : ℝ} (hb : 0 < b)
    (hp : (u, v u) ∈ pastTriangle ui) (hr : S.r u (v u) = b) :
    0 ≤ cylinderEnergy S b v u :=
  (mul_nonneg (by positivity) (sq_nonneg _)).trans
    (h.cylinder_energy_comparison hb hp hr).2

omit h in
/-- Uniform E_b≤Cb from the geometric gap and Lemma 2.1's amplitude bound.
Both premises are uniform before b,u,v, as required by the paper's ≲ notation.
Paper `e1a0fd5`, `eq:boundary-energy-comparison`, lines 684–688, 707. -/
theorem cylinder_energy_upper_of_geometric_scalar {g M : ℝ} (hg : 0 < g) (hM : 0 ≤ M)
    (hgap : ∀ p ∈ pastTriangle ui, g ≤ 1 - S.mu p.1 p.2)
    (hscalar : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      |S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → ∀ v : ℝ → ℝ, ∀ u : ℝ,
      (u, v u) ∈ pastTriangle ui → u < v u → S.r u (v u) = b →
      cylinderEnergy S b v u ≤ C * b := by
  let C := (M ^ 2 + |Real.log g| + 1) / 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro b hb v u hp huv hr
  have ha := hscalar (u, v u) hp huv
  have hs : (cylinderP S v u - S.phi u (v u)) ^ 2 ≤ M ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg _) hM).mpr ha
    simpa only [sq_abs, cylinderP] using hs
  have hmu : massRatio b (S.m u (v u)) = S.mu u (v u) := by rw [SSFields.mu, hr]
  have hlog : -|Real.log g| ≤ Real.log (1 - massRatio b (S.m u (v u))) := by
    rw [hmu]
    exact (neg_abs_le _).trans (Real.log_le_log hg (hgap (u, v u) hp))
  unfold cylinderEnergy boundaryEnergy
  dsimp [C]
  nlinarith

end StandingFull

/-- AC of m_b, φ_b and P_b implies AC of their energy.
Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 729–737. -/
theorem cylinder_energy_ac_of_traces {a0 a1 b : ℝ} {mB phiB PB : ℝ → ℝ}
    (hm : AbsolutelyContinuousOnInterval mB a0 a1)
    (hphi : AbsolutelyContinuousOnInterval phiB a0 a1)
    (hP : AbsolutelyContinuousOnInterval PB a0 a1)
    (hmu : ∀ u ∈ uIcc a0 a1, massRatio b (mB u) < 1) :
    AbsolutelyContinuousOnInterval (fun u => boundaryEnergy b (mB u) (PB u - phiB u))
      a0 a1 := by
  have hA := hP.fun_sub hphi
  have hq := hA.fun_mul hA
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a0 a1 :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hratio : AbsolutelyContinuousOnInterval (fun u => massRatio b (mB u)) a0 a1 := by
    simpa [massRatio, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hm.const_mul (2 / b)
  have hlog := positive_ac_log (hconst.fun_sub hratio) (fun u hu => sub_pos.mpr (hmu u hu))
  simpa only [boundaryEnergy, pow_two] using (hq.fun_sub hlog).const_mul (b / 2)

/-- Exact a.e. balance on actual cylinder fields, in both u and boundary time.
The premises are the mass/scalar chain rules and AC of P_b, not the balance.
Paper `e1a0fd5`, `eq:boundary-energy-balance`, lines 690–697, 709–737. -/
theorem cylinder_balance_of_trace_derivatives {ui b a0 a1 : ℝ} {S : SSFields}
    (h : StandingFull ui S) {v : ℝ → ℝ} (ha : a0 ≤ a1) (hb : 0 < b)
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hr : ∀ u ∈ Icc a0 a1, S.r u (v u) = b)
    (hP : AbsolutelyContinuousOnInterval (cylinderP S v) a0 a1)
    (hm : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.m s (v s))
      (cylinderMassDerivative b (S.lam u (v u)) (S.nu u (v u)) (S.m u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u)
    (hphi : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.phi s (v s))
      (cylinderScalarDerivative (S.lam u (v u)) (S.nu u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u) :
    ∀ᵐ u, u ∈ Ioo a0 a1 →
      deriv (cylinderEnergy S b v) u +
          (b ^ 2 / 2) * (deriv (fun s => S.phi s (v s)) u) ^ 2 / (-S.nu u (v u)) =
        b * (cylinderP S v u - S.phi u (v u)) * deriv (cylinderP S v) u ∧
      deriv (cylinderEnergy S b v) u / (-S.nu u (v u)) +
          (b ^ 2 / 2) * (deriv (fun s => S.phi s (v s)) u / (-S.nu u (v u))) ^ 2 =
        b * (cylinderP S v u - S.phi u (v u)) *
          (deriv (cylinderP S v) u / (-S.nu u (v u))) := by
  filter_upwards [hm, hphi, hP.ae_differentiableAt] with u hmu hphiu hPu
  intro hu
  have huC := Ioo_subset_Icc_self hu
  have huU : u ∈ uIcc a0 a1 := by rwa [uIcc_of_le ha]
  have hlam := h.lam_pos (hp u huC)
  have hnu := h.nu_neg (hp u huC)
  have hmu0 : massRatio b (S.m u (v u)) < 1 := by
    simpa only [SSFields.mu, hr u huC] using (h.mu_bounds (hp u huC)).2
  have hA : cylinderP S v u - S.phi u (v u) =
      (b / S.lam u (v u)) * S.dvphi u (v u) :=
    cylinder_amplitude_eq hb.ne' hlam.ne' (hr u huC)
  have hd := hasDerivAt_boundaryEnergy (u := u)
    (mB := fun s => S.m s (v s)) (phiB := fun s => S.phi s (v s))
    (PB := cylinderP S v) hb hlam hnu hmu0 hA
    (hmu hu) (hphiu hu) (hPu huU).hasDerivAt
  have hbalance : deriv (cylinderEnergy S b v) u +
      (b ^ 2 / 2) * (deriv (fun s => S.phi s (v s)) u) ^ 2 / (-S.nu u (v u)) =
      b * (cylinderP S v u - S.phi u (v u)) * deriv (cylinderP S v) u := by
    rw [(hphiu hu).deriv, show deriv (cylinderEnergy S b v) u = _ from hd.deriv, hA]
    ring
  refine ⟨hbalance, ?_⟩
  have hn : -S.nu u (v u) ≠ 0 := neg_ne_zero.mpr hnu.ne
  calc
    _ = (deriv (cylinderEnergy S b v) u +
        (b ^ 2 / 2) * (deriv (fun s => S.phi s (v s)) u) ^ 2 / (-S.nu u (v u))) /
        (-S.nu u (v u)) := by field_simp [hnu.ne]; ring
    _ = _ := by rw [hbalance]; ring

end AcExtensionPrinciple

end
