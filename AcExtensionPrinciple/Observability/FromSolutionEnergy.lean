module

public import AcExtensionPrinciple.Observability.FromSolution
public import AcExtensionPrinciple.Cylinder.ClassEnergy

/-!
# Lemma 2.4 for the cylinder interface used by Lemma 2.5

Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 681–737.
Uniqueness of the radius-b intersection identifies an arbitrary regular
cylinder with the canonical curve. No trace regularity premise is added.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace DecayCylinder

/-- Every cylinder in the decay interface satisfies the regular cylinder condition. Paper `e1a0fd5`,
lines 664–675 and 681–737. -/
theorem regularInterval {ui b a₀ a₁ : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S) :
    RegularCylinderInterval ui S b a₀ a₁ := by
  refine ⟨c.ordered, c.initial_le, c.terminal_negative, ?_⟩
  intro u hu
  have hp := c.points u hu
  rw [← hp.2.2]
  exact (h.radius_strictMono (c.initial_le.trans hu.1)
    (hu.2.trans_lt c.terminal_negative)).monotoneOn
      ⟨hp.1.le, hp.2.1⟩ ⟨hp.1.le.trans hp.2.1, le_rfl⟩ hp.2.1

/-- The source cylinder equals the canonical radius-b curve throughout
its interval. Paper `e1a0fd5`, lines 664–675 and 681–737. -/
theorem v_eq_canonical {ui b a₀ a₁ u : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hu : u ∈ Icc a₀ a₁) : c.v u = cylinderV h b u := by
  have hp := c.points u hu
  have hv := h.cylinderV_spec_regular c.radius_pos (c.regularInterval h) hu
  exact (h.radius_strictMono (c.initial_le.trans hu.1)
    (hu.2.trans_lt c.terminal_negative)).injOn
      ⟨hp.1.le, hp.2.1⟩ ⟨hv.1.1.le, hv.1.2⟩ (hp.2.2.trans hv.2.symm)

end DecayCylinder

namespace StandingFull

/-- The class-level Lemma 2.4 discharges exactly the statement
consumed by the decay chain, including arbitrary cylinder graphs and
all subintervals. Paper `e1a0fd5`, `lem:boundary-energy-identity`,
lines 681–737. -/
theorem lemma24_statement {ui : ℝ} {S : SSFields} (h : StandingFull ui S) :
    Lemma24Statement ui S := by
  obtain ⟨C, hC, hupper⟩ := h.cylinder_energy_upper_regular
  refine ⟨C, hC, ?_⟩
  intro b a₀ a₁ c
  have hI := c.regularInterval h
  have hv := fun u hu => c.v_eq_canonical h (u := u) hu
  have hP : EqOn (cylinderP S (cylinderV h b)) (cylinderDatum S c) (Icc a₀ a₁) := by
    intro u hu
    simp only [cylinderP, cylinderDatum, hv u hu]
  have hphi : EqOn (fun u => S.phi u (cylinderV h b u)) (cylinderPhi S c)
      (Icc a₀ a₁) := by
    intro u hu
    simp only [cylinderPhi, hv u hu]
  have hE : EqOn (cylinderEnergy S b (cylinderV h b)) (decayCylinderEnergy S c)
      (Icc a₀ a₁) := by
    intro u hu
    simp only [cylinderEnergy, decayCylinderEnergy, cylinderP, cylinderDatum,
      cylinderPhi, hv u hu]
  have ht := h.cylinder_traces_ac_regular c.radius_pos hI
  refine ⟨?_, ht.1.congr ?_, ht.2.1.congr ?_, ht.2.2.1.congr ?_,
    ht.2.2.2.congr ?_, ?_, ?_⟩
  · intro u hu
    have hp : (u, c.v u) ∈ pastTriangle ui :=
      ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative,
        (c.points u hu).1.le, (c.points u hu).2.1⟩
    have hr := (c.points u hu).2.2
    have hc := h.cylinder_energy_comparison (v := c.v) c.radius_pos hp hr
    rw [← cylinder_amplitude_eq c.radius_pos.ne' (h.lam_pos hp).ne' hr] at hc
    exact ⟨hc.1, hc.2, by
      rw [← hE hu]
      exact hupper b a₀ a₁ c.radius_pos hI u hu⟩
  · intro u hu
    rw [uIcc_of_le c.ordered] at hu
    simp only [hv u hu]
  · simpa only [uIcc_of_le c.ordered] using hphi
  · simpa only [uIcc_of_le c.ordered] using hP
  · simpa only [uIcc_of_le c.ordered] using hE
  · filter_upwards [h.cylinder_boundary_balance_regular c.radius_pos hI] with u hu
    intro huI
    have hEq : ∀ᶠ z in 𝓝 u, c.v z = cylinderV h b z := by
      filter_upwards [Icc_mem_nhds huI.1 huI.2] with z hz
      exact hv z hz
    have hDP : deriv (cylinderDatum S c) u = deriv (cylinderP S (cylinderV h b)) u :=
      Filter.EventuallyEq.deriv_eq (hEq.mono (fun z hz => by
        simp only [cylinderDatum, cylinderP, hz]))
    have hDphi : deriv (cylinderPhi S c) u =
        deriv (fun z => S.phi z (cylinderV h b z)) u :=
      Filter.EventuallyEq.deriv_eq (hEq.mono (fun z hz => by simp only [cylinderPhi, hz]))
    have hDE : deriv (decayCylinderEnergy S c) u =
        deriv (cylinderEnergy S b (cylinderV h b)) u :=
      Filter.EventuallyEq.deriv_eq (hEq.mono (fun z hz => by
        simp only [decayCylinderEnergy, cylinderEnergy, cylinderDatum, cylinderP,
          cylinderPhi, hz]))
    simpa only [hDP, hDphi, hDE, cylinderDatum, cylinderP, cylinderPhi,
      hv u (Ioo_subset_Icc_self huI)] using (hu huI).1
  · intro a d ha had hd
    have hsub : Icc a d ⊆ Icc a₀ a₁ := Icc_subset_Icc ha hd
    have hJ : RegularCylinderInterval ui S b a d :=
      ⟨had, c.initial_le.trans ha, hd.trans_lt c.terminal_negative,
        fun u hu => hI.2.2.2 u (hsub hu)⟩
    rw [← hE (hsub (right_mem_Icc.mpr had)),
      ← hE (hsub (left_mem_Icc.mpr had)), cylinderVariation,
      ← eVariationOn.congr (hP.mono hsub)]
    exact h.cylinder_boundary_stability_regular c.radius_pos hJ

end StandingFull

end AcExtensionPrinciple

end
