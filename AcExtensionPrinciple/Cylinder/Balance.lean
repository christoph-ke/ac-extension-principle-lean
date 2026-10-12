module

public import AcExtensionPrinciple.Cylinder.Differential

/-!
# Integral boundary energy balance and stability on solution cylinders

Paper `e1a0fd5`, `equations.tex` lines 690–737,
`eq:boundary-energy-balance` and `eq:boundary-energy-stability`.
The imported calculus theorems are instantiated with the actual solution fields.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- AC traces and their characteristic chain rules imply the paper's √E stability,
including zeros of E. Trace AC is discharged by the transport and partials helpers.
Paper `e1a0fd5`, `eq:boundary-energy-stability`, lines 700–706, 729–737. -/
theorem cylinder_stability_of_traces {ui b a0 a1 : ℝ} {S : SSFields}
    (h : StandingFull ui S) {v : ℝ → ℝ} (ha : a0 ≤ a1) (hb : 0 < b)
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hr : ∀ u ∈ Icc a0 a1, S.r u (v u) = b)
    (hmAC : AbsolutelyContinuousOnInterval (fun u => S.m u (v u)) a0 a1)
    (hphiAC : AbsolutelyContinuousOnInterval (fun u => S.phi u (v u)) a0 a1)
    (hP : AbsolutelyContinuousOnInterval (cylinderP S v) a0 a1)
    (hm : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.m s (v s))
      (cylinderMassDerivative b (S.lam u (v u)) (S.nu u (v u)) (S.m u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u)
    (hphi : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.phi s (v s))
      (cylinderScalarDerivative (S.lam u (v u)) (S.nu u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u) :
    Real.sqrt (cylinderEnergy S b v a1) ≤ Real.sqrt (cylinderEnergy S b v a0) +
      Real.sqrt (b / 2) * (eVariationOn (cylinderP S v) (Icc a0 a1)).toReal := by
  have hmu : ∀ u ∈ uIcc a0 a1, massRatio b (S.m u (v u)) < 1 := by
    intro u hu
    rw [uIcc_of_le ha] at hu
    simpa only [SSFields.mu, hr u hu] using (h.mu_bounds (hp u hu)).2
  have hE := cylinder_energy_ac_of_traces hmAC hphiAC hP hmu
  apply boundary_energy_stability ha hb hE hP
  · exact fun u hu => h.cylinder_energy_nonneg hb (hp u hu) (hr u hu)
  · intro u hu
    exact scalar_square_le_boundaryEnergy hb
      (by simpa only [SSFields.mu, hr u hu] using (h.mu_bounds (hp u hu)).1)
      (hmu u (by simpa [uIcc_of_le ha] using hu))
  · filter_upwards [cylinder_balance_of_trace_derivatives h ha hb hp hr hP hm hphi] with u hu
    intro huI
    change deriv (cylinderEnergy S b v) u ≤ _
    have hD : 0 ≤ (b ^ 2 / 2) * (deriv (fun s => S.phi s (v s)) u) ^ 2 /
        (-S.nu u (v u)) := by
      exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
        (neg_nonneg.mpr (h.nu_neg (hp u (Ioo_subset_Icc_self huI))).le)
    linarith [(hu huI).1]

/-- An a.e. scalar chain rule and integrable squared continuous coefficient give
integrable actual dissipation. Paper `e1a0fd5`, lines 709–737,
`eq:cylinder-scalar-derivative`, `eq:boundary-energy-balance`. -/
theorem cylinder_dissipation_integrable_of_coefficient {b a0 a1 : ℝ} {phiB nuB q : ℝ → ℝ}
    (ha : a0 ≤ a1)
    (hi : IntervalIntegrable (fun u => (b ^ 2 / 2) * (q u) ^ 2 / (-nuB u)) volume a0 a1)
    (hd : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt phiB (q u) u) :
    IntervalIntegrable (fun u => (b ^ 2 / 2) * (deriv phiB u) ^ 2 / (-nuB u)) volume a0 a1 := by
  apply hi.congr_ae
  change ∀ᵐ u ∂volume.restrict (uIoc a0 a1),
    (b ^ 2 / 2) * (q u) ^ 2 / (-nuB u) =
      (b ^ 2 / 2) * (deriv phiB u) ^ 2 / (-nuB u)
  rw [uIoc_of_le ha, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hd, show ∀ᵐ u : ℝ, u ≠ a1 by simp [ae_iff]] with u hu hune
  intro huI
  rw [(hu ⟨huI.1, lt_of_le_of_ne huI.2 hune⟩).deriv]

/-- The exact integral identity of Lemma 2.4 for actual AC solution traces.
The dissipation's integrability follows from the continuous scalar coefficient
and its chain rule; it is explicit here to keep this helper reusable.
Paper `e1a0fd5`, `eq:boundary-energy-balance`, lines 690–697, 729–737. -/
theorem cylinder_integral_balance_of_traces {ui b a0 a1 : ℝ} {S : SSFields}
    (h : StandingFull ui S) {v : ℝ → ℝ} (ha : a0 ≤ a1) (hb : 0 < b)
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hr : ∀ u ∈ Icc a0 a1, S.r u (v u) = b)
    (hmAC : AbsolutelyContinuousOnInterval (fun u => S.m u (v u)) a0 a1)
    (hphiAC : AbsolutelyContinuousOnInterval (fun u => S.phi u (v u)) a0 a1)
    (hP : AbsolutelyContinuousOnInterval (cylinderP S v) a0 a1)
    (hD : IntervalIntegrable (fun u => (b ^ 2 / 2) *
      (deriv (fun s => S.phi s (v s)) u) ^ 2 / (-S.nu u (v u))) volume a0 a1)
    (hm : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.m s (v s))
      (cylinderMassDerivative b (S.lam u (v u)) (S.nu u (v u)) (S.m u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u)
    (hphi : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.phi s (v s))
      (cylinderScalarDerivative (S.lam u (v u)) (S.nu u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u) :
    cylinderEnergy S b v a1 - cylinderEnergy S b v a0 +
        (∫ u in a0..a1, (b ^ 2 / 2) * (deriv (fun s => S.phi s (v s)) u) ^ 2 /
          (-S.nu u (v u))) =
      ∫ u in a0..a1, b * (cylinderP S v u - S.phi u (v u)) * deriv (cylinderP S v) u := by
  have hmu : ∀ u ∈ uIcc a0 a1, massRatio b (S.m u (v u)) < 1 := by
    intro u hu
    rw [uIcc_of_le ha] at hu
    simpa only [SSFields.mu, hr u hu] using (h.mu_bounds (hp u hu)).2
  apply boundary_energy_integral_balance (cylinder_energy_ac_of_traces hmAC hphiAC hP hmu) hD
  filter_upwards [cylinder_balance_of_trace_derivatives h ha hb hp hr hP hm hphi,
    show ∀ᵐ u : ℝ, u ≠ a1 by simp [ae_iff]] with u hu hune
  intro huI
  rw [uIoc_of_le ha] at huI
  exact (hu ⟨huI.1, lt_of_le_of_ne huI.2 hune⟩).1

/-- The zero-length regular interval obeys both integral balance and stability.
Paper `e1a0fd5`, `eq:boundary-energy-balance`, `eq:boundary-energy-stability`, lines 690–706. -/
theorem cylinder_balance_stability_refl (S : SSFields) (b a : ℝ) (v : ℝ → ℝ) :
    (cylinderEnergy S b v a - cylinderEnergy S b v a +
      (∫ u in a..a, (b ^ 2 / 2) * (deriv (fun s => S.phi s (v s)) u) ^ 2 /
        (-S.nu u (v u))) =
      ∫ u in a..a, b * (cylinderP S v u - S.phi u (v u)) * deriv (cylinderP S v) u) ∧
    Real.sqrt (cylinderEnergy S b v a) ≤ Real.sqrt (cylinderEnergy S b v a) +
      Real.sqrt (b / 2) * (eVariationOn (cylinderP S v) (Icc a a)).toReal := by
  simp

end AcExtensionPrinciple

end
