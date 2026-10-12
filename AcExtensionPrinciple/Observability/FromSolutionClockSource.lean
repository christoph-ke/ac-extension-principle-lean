module

public import AcExtensionPrinciple.Observability.FromSolutionClock

/-!
# The inverse clock of a standing solution on a regular cylinder

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and 1923–1929.
This instantiates the extended clock with -ν_b and the uniform K lower
bound, without assuming an inverse chart as an extra source premise.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace DecayCylinder

/-- The physical cylinder lies in the standing source domain. Paper
`e1a0fd5`, lines 664–675 and 1460–1473. -/
theorem source_mem {ui b a₀ a₁ u : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (hu : u ∈ Icc a₀ a₁) :
    (u, c.v u) ∈ pastTriangle ui :=
  ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative,
    (c.points u hu).1.le, (c.points u hu).2.1⟩

/-- The boundary clock density is continuous on its entire regular
interval. Paper `e1a0fd5`, `eq:cylinder-time`, lines 671–673 and 1460. -/
theorem clock_density_continuous {ui b a₀ a₁ : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S) :
    ContinuousOn (fun u => -S.nu u (c.v u)) (Icc a₀ a₁) :=
  (h.regularCenter.continuous_nu.comp
    (continuousOn_id.prodMk c.smooth_v.continuousOn) (fun _ hu => c.source_mem hu)).neg

/-- The K lower bound holds for the actual clock density. Paper
`e1a0fd5`, lines 742–749 and 1460. -/
theorem clock_density_lower {ui b a₀ a₁ K : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (hK : CylinderKBounds ui S K) :
    ∀ u ∈ Icc a₀ a₁, K⁻¹ ≤ -S.nu u (c.v u) :=
  fun _ hu => (hK.2 _ (c.source_mem hu)).2.2.2

/-- The globally extended clock agrees with s=τ_b-τ_b(a) on the
physical subinterval. Paper `e1a0fd5`, line 1460 and 1926–1927. -/
theorem regularChartClock_eq {ui b a₀ a₁ a d u : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (ha : a₀ ≤ a) (hd : d ≤ a₁)
    (hu : u ∈ Icc a d) :
    regularChartClock (fun u => -S.nu u (c.v u)) a d u = normalizedCylinderClock c a u := by
  calc
    _ = ∫ x in a..u, -S.nu x (c.v x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hu.1] at hx
      exact chartClockDensity_eq ⟨hx.1, hx.2.trans hu.2⟩
    _ = normalizedCylinderClock c a u - normalizedCylinderClock c a a :=
      (normalizedCylinderClock_primitive c ha hu.1 (hu.2.trans hd)).2.symm
    _ = _ := by simp [normalizedCylinderClock]

/-- A normalized source clock, with globally defined regular inverse.
Paper `e1a0fd5`, line 1460, `eq:cylinder-time`, and lines 1926–1927. -/
@[expose] noncomputable def normalizedClockIso {ui b a₀ a₁ a d K : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) : ℝ ≃o ℝ :=
  regularChartClockIso (fun u => -S.nu u (c.v u)) had
    ((c.clock_density_continuous h).mono (Icc_subset_Icc ha hd))
    (inv_pos.mpr (zero_lt_one.trans_le hK.1))
    (fun _ hu => c.clock_density_lower hK _ (Icc_subset_Icc ha hd hu))

/-- Forward clock identification for the concrete source isomorphism.
Paper `e1a0fd5`, lines 1460 and 1926–1927. -/
theorem normalizedClockIso_apply {ui b a₀ a₁ a d K u : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁)
    (hu : u ∈ Icc a d) :
    c.normalizedClockIso h hK ha had hd u = normalizedCylinderClock c a u :=
  c.regularChartClock_eq ha hd hu

/-- The normalized initial label is zero. Paper `e1a0fd5`, line 1460. -/
theorem normalizedClockIso_initial {ui b a₀ a₁ a d K : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) :
    c.normalizedClockIso h hK ha had hd a = 0 := by
  rw [c.normalizedClockIso_apply h hK ha had hd (left_mem_Icc.mpr had)]
  simp [normalizedCylinderClock]

/-- The normalized final label is the boundary duration. Paper
`e1a0fd5`, line 1460. -/
theorem normalizedClockIso_terminal {ui b a₀ a₁ a d K : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) :
    c.normalizedClockIso h hK ha had hd d = c.tau d - c.tau a :=
  c.normalizedClockIso_apply h hK ha had hd (right_mem_Icc.mpr had)

/-- Every normalized time has its inverse in the physical cylinder
interval. Paper `e1a0fd5`, lines 1460–1473. -/
theorem normalizedClockIso_inverse_mem {ui b a₀ a₁ a d K s : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁)
    (hs : s ∈ Icc 0 (c.tau d - c.tau a)) :
    (c.normalizedClockIso h hK ha had hd).symm s ∈ Icc a d := by
  let e := c.normalizedClockIso h hK ha had hd
  have he0 : e a = 0 := c.normalizedClockIso_initial h hK ha had hd
  have heT : e d = c.tau d - c.tau a := c.normalizedClockIso_terminal h hK ha had hd
  constructor
  · simpa only [← he0, e.symm_apply_apply] using e.symm.monotone hs.1
  · simpa only [← heT, e.symm_apply_apply] using e.symm.monotone hs.2

/-- The inverse derivative is the required reciprocal expansion, even
at both physical endpoints. Paper `e1a0fd5`, lines 1460 and 1926–1927. -/
theorem normalizedClockIso_inverse_hasDerivAt {ui b a₀ a₁ a d K s : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁)
    (hs : s ∈ Icc 0 (c.tau d - c.tau a)) :
    HasDerivAt (c.normalizedClockIso h hK ha had hd).symm
      (-S.nu ((c.normalizedClockIso h hK ha had hd).symm s)
        (c.v ((c.normalizedClockIso h hK ha had hd).symm s)))⁻¹ s := by
  have hh := regularChartClockIso_inverse_hasDerivAt had
    ((c.clock_density_continuous h).mono (Icc_subset_Icc ha hd))
    (inv_pos.mpr (zero_lt_one.trans_le hK.1))
    (fun _ hu => c.clock_density_lower hK _ (Icc_subset_Icc ha hd hu)) s
  change HasDerivAt (c.normalizedClockIso h hK ha had hd).symm
    (chartClockDensity (fun u => -S.nu u (c.v u)) a d
      ((c.normalizedClockIso h hK ha had hd).symm s))⁻¹ s at hh
  rw [chartClockDensity_eq (c.normalizedClockIso_inverse_mem h hK ha had hd hs)] at hh
  exact hh

end DecayCylinder

end AcExtensionPrinciple

end
