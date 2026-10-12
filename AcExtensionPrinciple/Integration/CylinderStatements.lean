module

public import AcExtensionPrinciple.Integration.DecayChain
public import AcExtensionPrinciple.Cylinder.ClassEnergy
public import AcExtensionPrinciple.Interpolation.Uniform
public import AcExtensionPrinciple.LateCylinder.Closed

/-!
# Exact decay-chain interfaces for the cylinder lemmas

Paper `e1a0fd5`, `lem:ac-interpolation`, `lem:boundary-energy-identity`,
and `lem:late-cylinder-variation`, equations.tex lines 608–833.
The abstract cylinder agrees with the canonical one on its closed interval.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Local equality on a closed interval preserves interior derivatives.
Paper `e1a0fd5`, `eq:boundary-energy-balance`, lines 690–697. -/
theorem integration_deriv_eq_of_eqOn {f g : ℝ → ℝ} {a b x : ℝ}
    (hfg : EqOn f g (Icc a b)) (hx : x ∈ Ioo a b) : deriv f x = deriv g x :=
  (Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Ioo a b, isOpen_Ioo.mem_nhds hx, fun _ hy => hfg (Ioo_subset_Icc_self hy)⟩).deriv_eq

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Lemma 2.3 in the pointwise interface `Lemma23Statement`.
Paper `e1a0fd5`, `lem:ac-interpolation`, lines 608–659. -/
theorem lemma23 : Lemma23Statement ui S := by
  obtain ⟨C, hC, hb⟩ := h.ac_interpolation
  refine ⟨C, hC, ?_⟩
  intro u v hp hr
  have hA : S.r u v / S.lam u v * S.dvphi u v = outgoingAmplitude S u v := by
    dsimp [SSFields.dvphi, outgoingAmplitude]
    field_simp [hr.ne', (h.lam_pos hp).ne']
  rw [hA]
  exact hb (u, v) hp hr

/-- An abstract regular cylinder supplies the canonical regular interval. Paper `e1a0fd5`, lines
661–670, 682–707. -/
theorem decayCylinder_regular {b a d : ℝ} (c : DecayCylinder ui S b a d) :
    RegularCylinderInterval ui S b a d := by
  refine ⟨c.ordered, c.initial_le, c.terminal_negative, ?_⟩
  intro u hu
  have hp := c.points u hu
  rw [← hp.2.2]
  exact (h.radius_strictMono (c.initial_le.trans hu.1)
    (hu.2.trans_lt c.terminal_negative)).monotoneOn ⟨hp.1.le, hp.2.1⟩
      ⟨(hu.2.trans_lt c.terminal_negative).le, le_rfl⟩ hp.2.1

/-- Uniqueness of the radius intersection identifies both curves, including v=0.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem decayCylinder_v_eq {b a d : ℝ} (c : DecayCylinder ui S b a d) :
    EqOn c.v (cylinderV h b) (Icc a d) := by
  intro u hu
  have hp := c.points u hu
  have hv := h.cylinderV_spec_regular c.radius_pos (h.decayCylinder_regular c) hu
  apply (h.radius_strictMono (c.initial_le.trans hu.1)
    (hu.2.trans_lt c.terminal_negative)).injOn
    ⟨hp.1.le, hp.2.1⟩ ⟨hv.1.1.le, hv.1.2⟩
  exact hp.2.2.trans hv.2.symm

/-- Lemma 2.4 discharges `Lemma24Statement` on every abstract regular cylinder. Paper `e1a0fd5`,
`lem:boundary-energy-identity`, lines 682–737. -/
theorem lemma24 : Lemma24Statement ui S := by
  obtain ⟨C, hC, hupper⟩ := h.cylinder_energy_upper_regular
  refine ⟨C, hC, ?_⟩
  intro b a d c
  have hI := h.decayCylinder_regular c
  have hv := h.decayCylinder_v_eq c
  have hm : EqOn (fun u => S.m u (c.v u))
      (fun u => S.m u (cylinderV h b u)) (Icc a d) := fun u hu => by
    dsimp only; rw [hv hu]
  have hphi : EqOn (cylinderPhi S c)
      (fun u => S.phi u (cylinderV h b u)) (Icc a d) := fun u hu => by
    simp only [cylinderPhi, hv hu]
  have hP : EqOn (cylinderDatum S c) (cylinderP S (cylinderV h b)) (Icc a d) :=
    fun u hu => by simp only [cylinderDatum, cylinderP, hv hu]
  have hE : EqOn (decayCylinderEnergy S c)
      (cylinderEnergy S b (cylinderV h b)) (Icc a d) := fun u hu => by
    simp only [decayCylinderEnergy, cylinderEnergy, cylinderDatum, cylinderPhi, cylinderP, hv hu]
  have ht := h.cylinder_traces_ac_regular c.radius_pos hI
  refine ⟨?_, ht.1.congr ?_, ht.2.1.congr ?_, ht.2.2.1.congr ?_,
    ht.2.2.2.congr ?_, ?_, ?_⟩
  · intro u hu
    have hc := h.cylinder_energy_comparison_regular c.radius_pos hI hu
    have hp : (u, c.v u) ∈ pastTriangle ui :=
      ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative,
        (c.points u hu).1.le, (c.points u hu).2.1⟩
    have hA := cylinder_amplitude_eq c.radius_pos.ne' (h.lam_pos hp).ne'
      (c.points u hu).2.2
    refine ⟨?_, ?_, ?_⟩
    · rw [hv hu, hE hu]; exact hc.1
    · change b / 2 * (S.dvpsi u (c.v u) / S.lam u (c.v u) - S.phi u (c.v u)) ^ 2 ≤ _
      rw [hA, hv hu, hE hu]; exact hc.2
    · rw [hE hu]; exact hupper b a d c.radius_pos hI u hu
  · simpa only [uIcc_of_le c.ordered] using hm.symm
  · simpa only [uIcc_of_le c.ordered] using hphi.symm
  · simpa only [uIcc_of_le c.ordered] using hP.symm
  · simpa only [uIcc_of_le c.ordered] using hE.symm
  · filter_upwards [h.cylinder_boundary_balance_regular c.radius_pos hI] with u hu hmem
    rw [integration_deriv_eq_of_eqOn hE hmem, integration_deriv_eq_of_eqOn hphi hmem,
      integration_deriv_eq_of_eqOn hP hmem, hv (Ioo_subset_Icc_self hmem),
      hP (Ioo_subset_Icc_self hmem), hphi (Ioo_subset_Icc_self hmem)]
    exact (hu hmem).1
  · intro x y hax hxy hyd
    have hsub : Icc x y ⊆ Icc a d := Icc_subset_Icc hax hyd
    have hJ : RegularCylinderInterval ui S b x y :=
      ⟨hxy, c.initial_le.trans hax, hyd.trans_lt c.terminal_negative,
        fun u hu => hI.2.2.2 u (hsub hu)⟩
    have hs := h.cylinder_boundary_stability_regular c.radius_pos hJ
    rw [hE (hsub (right_mem_Icc.mpr hxy)), hE (hsub (left_mem_Icc.mpr hxy))]
    unfold cylinderVariation
    rw [eVariationOn.congr (hP.mono hsub)]
    exact hs

/-- The geometric constant of the decay proof also supplies the late-cylinder bounds.
Paper `e1a0fd5`, `eq:boundary-travel-time`, lines 742–749, 814–815. -/
theorem integrationCylinderK_late_bounds : LateCylinderGeometry ui S h.integrationCylinderK :=
  ⟨h.integrationCylinderK_bounds.1, fun p hp =>
    let hb := h.integrationCylinderK_bounds.2 p hp
    ⟨hb.1, hb.2.2.1, hb.2.2.2⟩⟩

/-- Lemma 2.6 in the closed-cylinder interface `Lemma26Statement`, using the same geometric K.
H is the positive observability constant of Lemma 2.5.
Paper `e1a0fd5`, `lem:late-cylinder-variation`, lines 791–833. -/
theorem lemma26 {H : ℝ} (hH : 0 < H) : Lemma26Statement ui S h.integrationCylinderK H := by
  obtain ⟨D, hD, hb⟩ :=
    h.late_cylinder_variation_closed_of_geometric h.integrationCylinderK_late_bounds hH
  refine ⟨D, hD, ?_⟩
  intro eps b u0 a d c heps heps1 hui hua hsmall htail hwait htime
  have hI := h.decayCylinder_regular c
  have hv := h.decayCylinder_v_eq c
  have htime_eq : lateCylinderTime S (cylinderV h b) a d = c.tau d - c.tau a := by
    unfold lateCylinderTime
    calc
      _ = ∫ u in a..d, -S.nu u (c.v u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le c.ordered] at hu
        simp only [hv hu]
      _ = _ := (c.clock a d le_rfl c.ordered le_rfl).2.symm
  have hbound := hb eps b u0 a d heps heps1 c.radius_pos hui c.ordered
    (fun u hu => ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative,
      hI.2.2.2 u hu⟩)
    (fun p hp h0 ha hr => hsmall p.1 p.2 hp h0 ha hr) htail hwait
    (by rwa [htime_eq])
  have heq : EqOn (cylinderDatum S c) (lateCylinderDatum S (cylinderV h b)) (Icc a d) :=
    fun u hu => by simp only [cylinderDatum, lateCylinderDatum, hv hu]
  rwa [← eVariationOn.congr heq] at hbound

end StandingFull

end AcExtensionPrinciple

end
