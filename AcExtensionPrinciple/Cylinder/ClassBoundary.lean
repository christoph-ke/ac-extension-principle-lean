module

public import AcExtensionPrinciple.Cylinder.TransportRemainder
public import AcExtensionPrinciple.Cylinder.Balance

/-!
# Lemma 2.4 from the standing class on every regular regular cylinder interval

Paper statements. Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 661–738. All trace
regularity and characteristic chain rules are discharged; only the uniform upper energy comparison
has a Lemma 2.1 amplitude premise.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology NNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The class gives both characteristic cylinder chain rules at every interior parameter.
Paper `e1a0fd5`, `eq:cylinder-mass-balance`, `eq:cylinder-scalar-derivative`, lines 709–719. -/
theorem cylinder_mass_scalar_derivatives_regular {b a0 a1 u : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (hu : u ∈ Ioo a0 a1) :
    HasDerivAt (fun s => S.m s (cylinderV h b s))
      (cylinderMassDerivative b (S.lam u (cylinderV h b u)) (S.nu u (cylinderV h b u))
        (S.m u (cylinderV h b u)) (S.duphi u (cylinderV h b u))
        (S.dvphi u (cylinderV h b u))) u ∧
    HasDerivAt (fun s => S.phi s (cylinderV h b s))
      (cylinderScalarDerivative (S.lam u (cylinderV h b u)) (S.nu u (cylinderV h b u))
        (S.duphi u (cylinderV h b u)) (S.dvphi u (cylinderV h b u))) u := by
  have hD := h.cylinder_regular_interior hI ⟨hu.1.le, hu.2⟩
  have hvs := (h.cylinderV_spec hb hD).1
  have hpi : (u, cylinderV h b u) ∈ cylinderInterior ui := ⟨hI.2.1.trans_lt hu.1, hvs⟩
  have hp := cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI
    (Ioo_subset_Icc_self hu))
  have ht := h.cylinderV_hasDerivAt_regular hb hI hu
  have hmf : HasFDerivAt (fun p => S.m p.1 p.2)
      ((cylinderLinear (S.massU u (cylinderV h b u))).coprod
        (cylinderLinear (S.massV u (cylinderV h b u)))) (u, cylinderV h b u) := by
    convert h.cylinder_mass_hasFDerivAt hpi using 1
  have hphif : HasFDerivAt (fun p => S.phi p.1 p.2)
      ((cylinderLinear (S.duphi u (cylinderV h b u))).coprod
        (cylinderLinear (S.dvphi u (cylinderV h b u)))) (u, cylinderV h b u) := by
    convert h.cylinder_phi_hasFDerivAt hpi using 1
  have hm := cylinder_mass_hasDerivAt_of_partials (S := S) (u := u) (v := cylinderV h b)
      hb (h.lam_pos hp) (h.nu_neg hp)
      (h.mu_bounds hp).2 (h.cylinderV_spec_regular hb hI (Ioo_subset_Icc_self hu)).2 ht
      hmf
  have hphi := cylinder_scalar_hasDerivAt_of_partials (S := S) (u := u) (v := cylinderV h b)
      ht hphif
  exact ⟨hm, hphi⟩

/-- All boundary traces, including the energy, are AC from the standing assumptions alone.
Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 729–737. -/
theorem cylinder_traces_ac_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    AbsolutelyContinuousOnInterval (fun u => S.m u (cylinderV h b u)) a0 a1 ∧
    AbsolutelyContinuousOnInterval (fun u => S.phi u (cylinderV h b u)) a0 a1 ∧
    AbsolutelyContinuousOnInterval (cylinderP S (cylinderV h b)) a0 a1 ∧
    AbsolutelyContinuousOnInterval (cylinderEnergy S b (cylinderV h b)) a0 a1 := by
  rcases hI.1.eq_or_lt with he | ha
  · subst a1
    exact ⟨.rfl, .rfl, .rfl, .rfl⟩
  · let v := cylinderV h b
    have hv := h.cylinderV_continuousOn_regular hb hI
    have hc := continuousOn_id.prodMk hv
    have hp : MapsTo (fun u => (u, v u)) (Icc a0 a1) (cylinderScalarRegion ui) :=
      fun _ hu => h.cylinderV_mem_regular hb hI hu
    have hpt (u : ℝ) (hu : u ∈ Icc a0 a1) := cylinderScalarRegion_subset ui (hp hu)
    have hr (u : ℝ) (hu : u ∈ Icc a0 a1) := (h.cylinderV_spec_regular hb hI hu).2
    obtain ⟨Kv, hvL⟩ := h.cylinderV_lipschitz_regular hb hI ha
    obtain ⟨KL, hL⟩ := h.cylinder_lambda_lipschitz_regular hb hI ha
    obtain ⟨KR, hR⟩ := h.cylinder_remainder_lipschitz_regular hb hI ha
    have hvM := (h.cylinderV_strictMonoOn_regular hb hI).monotoneOn
    have hvD : MapsTo v (uIcc a0 a1) (uIcc ui 0) := by
      intro u hu
      rw [uIcc_of_le hI.1] at hu
      rw [uIcc_of_le h.initial_negative.le]
      exact ⟨(hp hu).1.trans (hp hu).2.1.le, (hp hu).2.2⟩
    have hPAC : AbsolutelyContinuousOnInterval (cylinderP S v) a0 a1 := by
      apply cylinder_P_ac_of_transport (R := fun u => cylinderRemainder S ui u (v u))
        h.initial_ac_data (by simpa only [uIcc_of_le hI.1] using hvM)
        (by simpa only [uIcc_of_le hI.1] using hvL) hvD
        (by simpa only [uIcc_of_le hI.1] using hL)
        (fun u hu => h.lam_pos (hpt u (by simpa only [uIcc_of_le hI.1] using hu)))
        (by simpa only [uIcc_of_le hI.1] using hR)
      intro u hu
      exact h.cylinder_P_representation (hp (by simpa only [uIcc_of_le hI.1] using hu))
    have hU := h.cylinder_duphi_continuous.comp hc hp
    have hV := h.cylinder_dvphi_continuous.comp hc hp
    have hmass : ∀ u ∈ Ioo a0 a1, HasFDerivAt (fun p => S.m p.1 p.2)
        ((cylinderLinear (S.massU u (v u))).coprod (cylinderLinear (S.massV u (v u))))
        (u, v u) := by
      intro u hu
      have hs := (h.cylinderV_spec hb (h.cylinder_regular_interior hI ⟨hu.1.le, hu.2⟩)).1
      convert h.cylinder_mass_hasFDerivAt (p := (u, v u))
        ⟨hI.2.1.trans_lt hu.1, hs⟩ using 1
    have hphi : ∀ u ∈ Ioo a0 a1, HasFDerivAt (fun p => S.phi p.1 p.2)
        ((cylinderLinear (S.duphi u (v u))).coprod (cylinderLinear (S.dvphi u (v u))))
        (u, v u) := by
      intro u hu
      have hs := (h.cylinderV_spec hb (h.cylinder_regular_interior hI ⟨hu.1.le, hu.2⟩)).1
      convert h.cylinder_phi_hasFDerivAt (p := (u, v u))
        ⟨hI.2.1.trans_lt hu.1, hs⟩ using 1
    obtain ⟨hmAC, hphiAC⟩ := cylinder_mass_scalar_ac_of_partials h hI.1 hb hv hpt hr
      (fun _ hu => h.cylinderV_hasDerivAt_regular hb hI hu) hU hV hmass hphi
    refine ⟨hmAC, hphiAC, hPAC, cylinder_energy_ac_of_traces hmAC hphiAC hPAC ?_⟩
    intro u hu
    rw [uIcc_of_le hI.1] at hu
    simpa only [v, SSFields.mu, hr u hu] using (h.mu_bounds (hpt u hu)).2

/-- The actual energy controls enclosed mass and the outgoing scalar square on regular cylinders.
Paper `e1a0fd5`, `eq:boundary-energy-comparison`, lines 684–688. -/
theorem cylinder_energy_comparison_regular {b a0 a1 u : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (hu : u ∈ Icc a0 a1) :
    S.m u (cylinderV h b u) ≤ cylinderEnergy S b (cylinderV h b) u ∧
      (b / 2) * ((b / S.lam u (cylinderV h b u)) * S.dvphi u (cylinderV h b u)) ^ 2 ≤
        cylinderEnergy S b (cylinderV h b) u :=
  h.cylinder_energy_comparison hb
    (cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI hu))
    (h.cylinderV_spec_regular hb hI hu).2

/-- Exact a.e. balance in both characteristic parameter and boundary time from the standing class.
Paper `e1a0fd5`, `eq:boundary-energy-balance`, lines 690–697, 709–737. -/
theorem cylinder_boundary_balance_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    ∀ᵐ u, u ∈ Ioo a0 a1 →
      deriv (cylinderEnergy S b (cylinderV h b)) u + (b ^ 2 / 2) *
          (deriv (fun s => S.phi s (cylinderV h b s)) u) ^ 2 / (-S.nu u (cylinderV h b u)) =
        b * (cylinderP S (cylinderV h b) u - S.phi u (cylinderV h b u)) *
          deriv (cylinderP S (cylinderV h b)) u ∧
      deriv (cylinderEnergy S b (cylinderV h b)) u / (-S.nu u (cylinderV h b u)) +
          (b ^ 2 / 2) * (deriv (fun s => S.phi s (cylinderV h b s)) u /
            (-S.nu u (cylinderV h b u))) ^ 2 =
        b * (cylinderP S (cylinderV h b) u - S.phi u (cylinderV h b u)) *
          (deriv (cylinderP S (cylinderV h b)) u / (-S.nu u (cylinderV h b u))) := by
  have ht := h.cylinder_traces_ac_regular hb hI
  apply cylinder_balance_of_trace_derivatives h hI.1 hb
    (fun _ hu => cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI hu))
    (fun _ hu => (h.cylinderV_spec_regular hb hI hu).2) ht.2.2.1
  · filter_upwards with u hu
    exact (h.cylinder_mass_scalar_derivatives_regular hb hI hu).1
  · filter_upwards with u hu
    exact (h.cylinder_mass_scalar_derivatives_regular hb hI hu).2

/-- Actual squared scalar dissipation is integrable on every regular interval.
Paper `e1a0fd5`, `eq:boundary-energy-balance`, lines 709–737. -/
theorem cylinder_dissipation_integrable_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    IntervalIntegrable (fun u => (b ^ 2 / 2) *
      (deriv (fun s => S.phi s (cylinderV h b s)) u) ^ 2 / (-S.nu u (cylinderV h b u)))
      volume a0 a1 := by
  have hc := continuousOn_id.prodMk (h.cylinderV_continuousOn_regular hb hI)
  have hp : MapsTo (fun u => (u, cylinderV h b u)) (Icc a0 a1) (cylinderScalarRegion ui) :=
    fun _ hu => h.cylinderV_mem_regular hb hI hu
  have hpt (u : ℝ) (hu : u ∈ Icc a0 a1) := cylinderScalarRegion_subset ui (hp hu)
  have hcU := h.cylinder_duphi_continuous.comp hc hp
  have hcV := h.cylinder_dvphi_continuous.comp hc hp
  have hcN := h.regularCenter.continuous_nu.comp hc hpt
  have hcL := h.regularCenter.continuous_lam.comp hc hpt
  have hcQ : ContinuousOn (fun u => cylinderScalarDerivative (S.lam u (cylinderV h b u))
      (S.nu u (cylinderV h b u)) (S.duphi u (cylinderV h b u)) (S.dvphi u (cylinderV h b u)))
      (Icc a0 a1) :=
    hcU.sub ((hcN.div hcL (fun _ hu => (h.lam_pos (hpt _ hu)).ne')).mul hcV)
  have hcD : ContinuousOn (fun u => (b ^ 2 / 2) *
      (cylinderScalarDerivative (S.lam u (cylinderV h b u))
        (S.nu u (cylinderV h b u)) (S.duphi u (cylinderV h b u))
        (S.dvphi u (cylinderV h b u))) ^ 2 / (-S.nu u (cylinderV h b u)))
      (Icc a0 a1) :=
    (continuousOn_const.mul (hcQ.pow 2)).div hcN.neg
      (fun _ hu => neg_ne_zero.mpr (h.nu_neg (hpt _ hu)).ne)
  apply cylinder_dissipation_integrable_of_coefficient hI.1
    (hcD.intervalIntegrable_of_Icc (μ := volume) hI.1)
  filter_upwards with u hu
  exact (h.cylinder_mass_scalar_derivatives_regular hb hI hu).2

/-- The exact integral identity of Lemma 2.4, with every regularity premise discharged.
Paper `e1a0fd5`, `eq:boundary-energy-balance`, lines 690–697, 729–737. -/
theorem cylinder_boundary_integral_balance_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    cylinderEnergy S b (cylinderV h b) a1 - cylinderEnergy S b (cylinderV h b) a0 +
        (∫ u in a0..a1, (b ^ 2 / 2) *
          (deriv (fun s => S.phi s (cylinderV h b s)) u) ^ 2 / (-S.nu u (cylinderV h b u))) =
      ∫ u in a0..a1, b * (cylinderP S (cylinderV h b) u - S.phi u (cylinderV h b u)) *
        deriv (cylinderP S (cylinderV h b)) u := by
  have ht := h.cylinder_traces_ac_regular hb hI
  apply cylinder_integral_balance_of_traces h hI.1 hb
    (fun _ hu => cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI hu))
    (fun _ hu => (h.cylinderV_spec_regular hb hI hu).2) ht.1 ht.2.1 ht.2.2.1
    (h.cylinder_dissipation_integrable_regular hb hI)
  · filter_upwards with u hu
    exact (h.cylinder_mass_scalar_derivatives_regular hb hI hu).1
  · filter_upwards with u hu
    exact (h.cylinder_mass_scalar_derivatives_regular hb hI hu).2

/-- √E stability on every regular regular cylinder interval, including zeros and zero-length
intervals. Paper `e1a0fd5`, `eq:boundary-energy-stability`, lines 700–706, 729–737. -/
theorem cylinder_boundary_stability_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    Real.sqrt (cylinderEnergy S b (cylinderV h b) a1) ≤
      Real.sqrt (cylinderEnergy S b (cylinderV h b) a0) + Real.sqrt (b / 2) *
        (eVariationOn (cylinderP S (cylinderV h b)) (Icc a0 a1)).toReal := by
  have ht := h.cylinder_traces_ac_regular hb hI
  apply cylinder_stability_of_traces h hI.1 hb
    (fun _ hu => cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI hu))
    (fun _ hu => (h.cylinderV_spec_regular hb hI hu).2) ht.1 ht.2.1 ht.2.2.1
  · filter_upwards with u hu
    exact (h.cylinder_mass_scalar_derivatives_regular hb hI hu).1
  · filter_upwards with u hu
    exact (h.cylinder_mass_scalar_derivatives_regular hb hI hu).2

/-- Uniform upper boundary energy comparison, with only the permitted Lemma 2.1 amplitude premise.
Paper `e1a0fd5`, `eq:boundary-energy-comparison`, lines 684–688, 707. -/
theorem cylinder_energy_upper_of_scalar_bound {M : ℝ} (hM : 0 ≤ M)
    (hscalar : ∀ p ∈ cylinderScalarRegion ui,
      |S.dvpsi p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ b a0 a1 : ℝ, 0 < b →
      RegularCylinderInterval ui S b a0 a1 → ∀ u ∈ Icc a0 a1,
        cylinderEnergy S b (cylinderV h b) u ≤ C * b := by
  obtain ⟨C, hC, hbound⟩ := cylinder_energy_upper_of_geometric_scalar
    (ui := ui) (S := S) (mul_pos h.initialGap_pos (Real.exp_pos _)) hM
    (fun _ hp => h.mass_gap_lower hp)
    (fun p hp huv => hscalar p ⟨hp.1, huv, hp.2.2.2⟩)
  refine ⟨C, hC, ?_⟩
  intro b a0 a1 hb hI u hu
  have hp := h.cylinderV_mem_regular hb hI hu
  exact hbound b hb (cylinderV h b) u (cylinderScalarRegion_subset ui hp) hp.2.1
    (h.cylinderV_spec_regular hb hI hu).2

end AcExtensionPrinciple.StandingFull

end
