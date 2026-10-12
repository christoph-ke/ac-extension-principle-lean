module

public import AcExtensionPrinciple.Decay.ClassCylinderStatements
public import AcExtensionPrinciple.Cylinder.CompactCurve
public import AcExtensionPrinciple.GeometricBounds.IncomingFlux

/-!
# Constructing the cylinders needed by the decay proof

Paper `e1a0fd5`, lines 664–675, 742–749 and 884–891. Main's canonical cylinders provide the assembly
interface whenever b < r(u,0). Proposition 2.7 proves r(u,0) ≥ 2b, so this helper's strict margin is
discharged there. The exact regular cylinder geometry statement remains recorded in
`ClassCylinderStatements`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Construct the regular cylinder with a terminal radial margin, as supplied by Proposition 2.7's
cylinder-inside-domain estimate. Paper `e1a0fd5`, `eq:cylinder-tangent`, `eq:cylinder-time`, lines
664–675 and 884–891. -/
theorem decay_cylinder_of_strict_terminal_radius {b a₀ a₁ : ℝ}
    (hb : 0 < b) (hai : ui ≤ a₀) (haa : a₀ ≤ a₁) (ha₁0 : a₁ < 0)
    (hR : ∀ u ∈ Icc a₀ a₁, b < S.r u 0) :
    Nonempty (DecayCylinder ui S b a₀ a₁) := by
  have hI : Icc a₀ a₁ ⊆ cylinderDomain ui b S := by
    intro u hu
    exact ⟨hai.trans hu.1, hu.2.trans_lt ha₁0, hR u hu⟩
  let v := cylinderV h b
  have hv := h.cylinderV_continuousOn_closed hb haa hI
  have hp (u : ℝ) (hu : u ∈ Icc a₀ a₁) := h.cylinder_mem hb (hI hu)
  have hn := (h.regularCenter.continuous_nu.comp (continuousOn_id.prodMk hv) hp).neg
  have hi : IntervalIntegrable (fun u => -S.nu u (v u)) volume a₀ a₁ :=
    hn.intervalIntegrable_of_Icc haa
  refine ⟨{
    v := v
    tau := cylinderTime S v a₀
    radius_pos := hb
    initial_le := hai
    ordered := haa
    terminal_negative := ha₁0
    points := fun u hu => ⟨(h.cylinderV_spec hb (hI hu)).1.1,
      (h.cylinderV_spec hb (hI hu)).1.2.le, (h.cylinderV_spec hb (hI hu)).2⟩
    smooth_v := ?_
    tangent := fun u hu => h.cylinderV_hasDerivAt hb (hI (Ioo_subset_Icc_self hu))
      (hai.trans_lt hu.1)
    continuous_tau := ?_
    clock := ?_ }⟩
  · rcases haa.eq_or_lt with he | he
    · subst a₁
      rw [Icc_self]
      intro x hx
      rw [mem_singleton_iff] at hx
      subst x
      exact contDiffWithinAt_singleton
    · exact h.cylinderV_contDiffOn_closed hb he hI
  · simpa only [uIcc_of_le haa] using (h.cylinder_time_ac haa hv hp).continuousOn
  · intro a d ha had hd
    have hia : IntervalIntegrable (fun u => -S.nu u (v u)) volume a₀ a :=
      hi.mono_set (by
        rw [uIcc_of_le haa, uIcc_of_le ha]
        exact Icc_subset_Icc le_rfl (had.trans hd))
    have hid : IntervalIntegrable (fun u => -S.nu u (v u)) volume a₀ d :=
      hi.mono_set (by
        rw [uIcc_of_le haa, uIcc_of_le (ha.trans had)]
        exact Icc_subset_Icc le_rfl hd)
    refine ⟨hi.mono_set (by
      rw [uIcc_of_le haa, uIcc_of_le had]
      exact Icc_subset_Icc ha hd), ?_⟩
    exact intervalIntegral.integral_interval_sub_left hid hia

/-- Choose the uniform cylinder constant from Lemma 1.1, with no remaining
geometric premise. Paper `e1a0fd5`, lines 742–749. -/
theorem exists_decay_cylinder_K : ∃ K : ℝ, CylinderKBounds ui S K :=
  h.exists_cylinder_K_of_geometric h.initialGap_pos (fun _ hp => h.mass_gap_lower hp)

end AcExtensionPrinciple.StandingFull

end
