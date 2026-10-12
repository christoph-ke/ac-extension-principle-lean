module

public import AcExtensionPrinciple.Cylinder.Energy
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Cylinder chain rules from characteristic partial derivatives

Paper `e1a0fd5`, `equations.tex` lines 709–737,
`eq:cylinder-mass-balance` and `eq:cylinder-scalar-derivative`.
The partial derivative certificates are explicit helper inputs; `Cylinder/ClassPartials.lean`
discharges them from the off-axis characteristic primitives and scalar trace regularity.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Mass characteristic partials and the cylinder tangent give the actual mass chain rule.
Paper `e1a0fd5`, `eq:cylinder-mass-balance`, lines 709–716. -/
theorem cylinder_mass_hasDerivAt_of_partials {S : SSFields} {b u : ℝ} {v : ℝ → ℝ}
    (hb : 0 < b) (hl : 0 < S.lam u (v u)) (hn : S.nu u (v u) < 0)
    (hmu : S.mu u (v u) < 1) (hr : S.r u (v u) = b)
    (hv : HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u)
    (hm : HasFDerivAt (fun p => S.m p.1 p.2)
      ((cylinderLinear (S.massU u (v u))).coprod (cylinderLinear (S.massV u (v u))))
      (u, v u)) :
    HasDerivAt (fun s => S.m s (v s))
      (cylinderMassDerivative b (S.lam u (v u)) (S.nu u (v u)) (S.m u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u := by
  have hd := hm.comp_hasDerivAt u ((hasDerivAt_id u).prodMk hv)
  have hz : S.zeta u (v u) = b * S.duphi u (v u) := by
    rw [SSFields.duphi, hr]
    field_simp
  have ht : S.theta u (v u) = b * S.dvphi u (v u) := by
    rw [SSFields.dvphi, hr]
    field_simp
  have hmuE : S.mu u (v u) = massRatio b (S.m u (v u)) := by rw [SSFields.mu, hr]
  have hg : 1 - massRatio b (S.m u (v u)) ≠ 0 := by
    rw [← hmuE]
    exact (sub_pos.mpr hmu).ne'
  convert hd using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply, cylinderLinear,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    unfold cylinderMassDerivative gammaOf kappaOf SSFields.massU SSFields.massV
    rw [hz, ht, hmuE]
    field_simp [hb.ne', hl.ne', hn.ne, hg]
    ring

/-- Scalar characteristic partials and the cylinder tangent give the scalar chain rule.
Paper `e1a0fd5`, `eq:cylinder-scalar-derivative`, lines 716–719. -/
theorem cylinder_scalar_hasDerivAt_of_partials {S : SSFields} {u : ℝ} {v : ℝ → ℝ}
    (hv : HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u)
    (hphi : HasFDerivAt (fun p => S.phi p.1 p.2)
      ((cylinderLinear (S.duphi u (v u))).coprod (cylinderLinear (S.dvphi u (v u))))
      (u, v u)) :
    HasDerivAt (fun s => S.phi s (v s))
      (cylinderScalarDerivative (S.lam u (v u)) (S.nu u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u := by
  convert hphi.comp_hasDerivAt u ((hasDerivAt_id u).prodMk hv) using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply, cylinderLinear,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, cylinderScalarDerivative]
    ring

/-- Recover AC of m_b and φ_b from continuous off-axis differential coefficients.
No AC of these boundary traces is assumed. The helper's partials come from the
characteristic primitives; continuity of the scalar derivatives is the remaining
class regularity input. Paper `e1a0fd5`, lines 709–737. -/
theorem cylinder_mass_scalar_ac_of_partials {ui b a0 a1 : ℝ} {S : SSFields}
    (h : StandingFull ui S) {v : ℝ → ℝ} (ha : a0 ≤ a1) (hb : 0 < b)
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hr : ∀ u ∈ Icc a0 a1, S.r u (v u) = b)
    (ht : ∀ u ∈ Ioo a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u)
    (hU : ContinuousOn (fun u => S.duphi u (v u)) (Icc a0 a1))
    (hV : ContinuousOn (fun u => S.dvphi u (v u)) (Icc a0 a1))
    (hm : ∀ u ∈ Ioo a0 a1, HasFDerivAt (fun p => S.m p.1 p.2)
      ((cylinderLinear (S.massU u (v u))).coprod (cylinderLinear (S.massV u (v u))))
      (u, v u))
    (hphi : ∀ u ∈ Ioo a0 a1, HasFDerivAt (fun p => S.phi p.1 p.2)
      ((cylinderLinear (S.duphi u (v u))).coprod (cylinderLinear (S.dvphi u (v u))))
      (u, v u)) :
    AbsolutelyContinuousOnInterval (fun u => S.m u (v u)) a0 a1 ∧
      AbsolutelyContinuousOnInterval (fun u => S.phi u (v u)) a0 a1 := by
  have hc := continuousOn_id.prodMk hv
  have hcM := h.regularCenter.continuous_m.comp hc hp
  have hcPhi := h.regularCenter.continuous_phi.comp hc hp
  have hcL := h.regularCenter.continuous_lam.comp hc hp
  have hcN := h.regularCenter.continuous_nu.comp hc hp
  have hcMu : ContinuousOn (fun u => massRatio b (S.m u (v u))) (Icc a0 a1) := by
    exact (continuousOn_const.mul hcM).div_const b
  have hcG : ContinuousOn (fun u => gammaOf (S.nu u (v u))
      (massRatio b (S.m u (v u)))) (Icc a0 a1) := by
    apply hcN.div (continuousOn_const.sub hcMu)
    intro u hu
    have he : massRatio b (S.m u (v u)) = S.mu u (v u) := by rw [SSFields.mu, hr u hu]
    change 1 - massRatio b (S.m u (v u)) ≠ 0
    rw [he]
    exact (sub_pos.mpr (h.mu_bounds (hp u hu)).2).ne'
  have hcK : ContinuousOn (fun u => kappaOf (S.lam u (v u))
      (massRatio b (S.m u (v u)))) (Icc a0 a1) := by
    apply hcL.div (continuousOn_const.sub hcMu)
    intro u hu
    have he : massRatio b (S.m u (v u)) = S.mu u (v u) := by rw [SSFields.mu, hr u hu]
    change 1 - massRatio b (S.m u (v u)) ≠ 0
    rw [he]
    exact (sub_pos.mpr (h.mu_bounds (hp u hu)).2).ne'
  have hcMD : ContinuousOn (fun u => cylinderMassDerivative b (S.lam u (v u))
      (S.nu u (v u)) (S.m u (v u)) (S.duphi u (v u)) (S.dvphi u (v u)))
      (Icc a0 a1) := by
    unfold cylinderMassDerivative
    apply ContinuousOn.sub
    · apply ContinuousOn.mul _ (hU.pow 2)
      apply continuousOn_const.div (continuousOn_const.mul hcG)
      intro u hu
      have he : massRatio b (S.m u (v u)) = S.mu u (v u) := by rw [SSFields.mu, hr u hu]
      change 2 * gammaOf (S.nu u (v u)) (massRatio b (S.m u (v u))) ≠ 0
      rw [gammaOf, he]
      exact mul_ne_zero (by norm_num) (div_ne_zero (h.nu_neg (hp u hu)).ne
        (sub_pos.mpr (h.mu_bounds (hp u hu)).2).ne')
    · apply ContinuousOn.mul _ (hV.pow 2)
      apply ContinuousOn.mul (hcN.div hcL (fun u hu => (h.lam_pos (hp u hu)).ne'))
      apply continuousOn_const.div (continuousOn_const.mul hcK)
      intro u hu
      have he : massRatio b (S.m u (v u)) = S.mu u (v u) := by rw [SSFields.mu, hr u hu]
      change 2 * kappaOf (S.lam u (v u)) (massRatio b (S.m u (v u))) ≠ 0
      rw [kappaOf, he]
      exact mul_ne_zero (by norm_num) (div_ne_zero (h.lam_pos (hp u hu)).ne'
        (sub_pos.mpr (h.mu_bounds (hp u hu)).2).ne')
  have hcPD : ContinuousOn (fun u => cylinderScalarDerivative (S.lam u (v u))
      (S.nu u (v u)) (S.duphi u (v u)) (S.dvphi u (v u))) (Icc a0 a1) :=
    hU.sub ((hcN.div hcL (fun u hu => (h.lam_pos (hp u hu)).ne')).mul hV)
  constructor
  · apply cylinder_ac_of_continuous_derivative ha hcM hcMD
    intro u hu
    have huC := Ioo_subset_Icc_self hu
    exact cylinder_mass_hasDerivAt_of_partials hb (h.lam_pos (hp u huC))
      (h.nu_neg (hp u huC)) (h.mu_bounds (hp u huC)).2 (hr u huC) (ht u hu) (hm u hu)
  · exact cylinder_ac_of_continuous_derivative ha hcPhi hcPD
      (fun u hu => cylinder_scalar_hasDerivAt_of_partials (ht u hu) (hphi u hu))

end AcExtensionPrinciple

end
