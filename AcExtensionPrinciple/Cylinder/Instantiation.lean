module

public import AcExtensionPrinciple.Cylinder.CompactCurve
public import AcExtensionPrinciple.Cylinder.Balance

/-!
# Lemma 2.4 instantiated on the canonical solution cylinder

Paper `e1a0fd5`, `lem:boundary-energy-identity`,
`equations.tex` lines 661–738. The explicit inputs are the off-axis partial
certificates, continuous scalar differential coefficients, and the linear
transport remainder. These are helper premises, not additional standing
assumptions or a revised paper statement.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Assemble AC, integral balance, and √E stability on the canonical class cylinder.
Partial certificates and continuous scalar coefficients are discharged by the
characteristic primitives and scalar trace continuity. The Lipschitz expansion
and remainder come from the off-axis linear transport representation (or Lemma 2.2).
Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 709–737. -/
theorem cylinder_balance_stability_of_partials_transport
    {ui b a0 a1 : ℝ} {S : SSFields} (h : StandingFull ui S)
    (hb : 0 < b) (ha : a0 < a1) (hI : Icc a0 a1 ⊆ cylinderDomain ui b S)
    {R : ℝ → ℝ} {KL KR : ℝ≥0}
    (hL : LipschitzOnWith KL (fun u => S.lam u (cylinderV h b u)) (Icc a0 a1))
    (hR : LipschitzOnWith KR R (Icc a0 a1))
    (htransport : ∀ u ∈ Icc a0 a1,
      cylinderP S (cylinderV h b) u =
        S.dvpsi ui (cylinderV h b u) / S.lam u (cylinderV h b u) + R u)
    (hU : ContinuousOn (fun u => S.duphi u (cylinderV h b u)) (Icc a0 a1))
    (hV : ContinuousOn (fun u => S.dvphi u (cylinderV h b u)) (Icc a0 a1))
    (hm : ∀ u ∈ Ioo a0 a1, HasFDerivAt (fun p => S.m p.1 p.2)
      ((cylinderLinear (S.massU u (cylinderV h b u))).coprod
        (cylinderLinear (S.massV u (cylinderV h b u)))) (u, cylinderV h b u))
    (hphi : ∀ u ∈ Ioo a0 a1, HasFDerivAt (fun p => S.phi p.1 p.2)
      ((cylinderLinear (S.duphi u (cylinderV h b u))).coprod
        (cylinderLinear (S.dvphi u (cylinderV h b u)))) (u, cylinderV h b u)) :
    AbsolutelyContinuousOnInterval (fun u => S.m u (cylinderV h b u)) a0 a1 ∧
    AbsolutelyContinuousOnInterval (fun u => S.phi u (cylinderV h b u)) a0 a1 ∧
    AbsolutelyContinuousOnInterval (cylinderP S (cylinderV h b)) a0 a1 ∧
    (cylinderEnergy S b (cylinderV h b) a1 - cylinderEnergy S b (cylinderV h b) a0 +
      (∫ u in a0..a1, (b ^ 2 / 2) *
        (deriv (fun s => S.phi s (cylinderV h b s)) u) ^ 2 / (-S.nu u (cylinderV h b u))) =
      ∫ u in a0..a1, b * (cylinderP S (cylinderV h b) u - S.phi u (cylinderV h b u)) *
        deriv (cylinderP S (cylinderV h b)) u) ∧
    Real.sqrt (cylinderEnergy S b (cylinderV h b) a1) ≤
      Real.sqrt (cylinderEnergy S b (cylinderV h b) a0) + Real.sqrt (b / 2) *
        (eVariationOn (cylinderP S (cylinderV h b)) (Icc a0 a1)).toReal := by
  let v := cylinderV h b
  have hp (u : ℝ) (hu : u ∈ Icc a0 a1) := h.cylinder_mem hb (hI hu)
  have hr (u : ℝ) (hu : u ∈ Icc a0 a1) := (h.cylinderV_spec hb (hI hu)).2
  have hv := h.cylinderV_continuousOn_closed hb ha.le hI
  have ht (u : ℝ) (hu : u ∈ Ioo a0 a1) :=
    h.cylinderV_hasDerivAt hb (hI (Ioo_subset_Icc_self hu))
      ((hI (left_mem_Icc.mpr ha.le)).1.trans_lt hu.1)
  obtain ⟨Kv, hvL⟩ := h.cylinderV_lipschitz_closed hb ha hI
  have hvM := (h.cylinderV_strictMonoOn_closed hb ha.le hI).monotoneOn
  have hvD : MapsTo v (uIcc a0 a1) (uIcc ui 0) := by
    intro u hu
    rw [uIcc_of_le ha.le] at hu
    rw [uIcc_of_le h.initial_negative.le]
    have huD := hI hu
    have hvs := (h.cylinderV_spec hb huD).1
    exact ⟨huD.1.trans hvs.1.le, hvs.2.le⟩
  have hPAC : AbsolutelyContinuousOnInterval (cylinderP S v) a0 a1 := by
    apply cylinder_P_ac_of_transport h.initial_ac_data
      (by simpa only [uIcc_of_le ha.le] using hvM)
      (by simpa only [uIcc_of_le ha.le] using hvL) hvD
      (by simpa only [uIcc_of_le ha.le] using hL)
      (fun u hu => h.lam_pos (hp u (by simpa only [uIcc_of_le ha.le] using hu)))
      (by simpa only [uIcc_of_le ha.le] using hR)
    intro u hu
    exact htransport u (by simpa only [uIcc_of_le ha.le] using hu)
  obtain ⟨hmAC, hphiAC⟩ := cylinder_mass_scalar_ac_of_partials h ha.le hb hv hp hr ht hU hV hm hphi
  have hmD : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.m s (v s))
      (cylinderMassDerivative b (S.lam u (v u)) (S.nu u (v u)) (S.m u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u := by
    filter_upwards with u hu
    have huC := Ioo_subset_Icc_self hu
    exact cylinder_mass_hasDerivAt_of_partials hb (h.lam_pos (hp u huC))
      (h.nu_neg (hp u huC)) (h.mu_bounds (hp u huC)).2 (hr u huC) (ht u hu) (hm u hu)
  have hphiD : ∀ᵐ u, u ∈ Ioo a0 a1 → HasDerivAt (fun s => S.phi s (v s))
      (cylinderScalarDerivative (S.lam u (v u)) (S.nu u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) u := by
    filter_upwards with u hu
    exact cylinder_scalar_hasDerivAt_of_partials (ht u hu) (hphi u hu)
  have hc := continuousOn_id.prodMk hv
  have hcN := h.regularCenter.continuous_nu.comp hc hp
  have hcL := h.regularCenter.continuous_lam.comp hc hp
  have hcQ : ContinuousOn (fun u => cylinderScalarDerivative (S.lam u (v u))
      (S.nu u (v u)) (S.duphi u (v u)) (S.dvphi u (v u))) (Icc a0 a1) :=
    hU.sub ((hcN.div hcL (fun u hu => (h.lam_pos (hp u hu)).ne')).mul hV)
  have hcD : ContinuousOn (fun u => (b ^ 2 / 2) *
      (cylinderScalarDerivative (S.lam u (v u)) (S.nu u (v u))
        (S.duphi u (v u)) (S.dvphi u (v u))) ^ 2 / (-S.nu u (v u))) (Icc a0 a1) :=
    (continuousOn_const.mul (hcQ.pow 2)).div hcN.neg
      (fun u hu => neg_ne_zero.mpr (h.nu_neg (hp u hu)).ne)
  have hD := cylinder_dissipation_integrable_of_coefficient ha.le
    (hcD.intervalIntegrable_of_Icc (μ := volume) ha.le) hphiD
  exact ⟨hmAC, hphiAC, hPAC,
    cylinder_integral_balance_of_traces h ha.le hb hp hr hmAC hphiAC hPAC hD hmD hphiD,
    cylinder_stability_of_traces h ha.le hb hp hr hmAC hphiAC hPAC hmD hphiD⟩

end AcExtensionPrinciple

end
