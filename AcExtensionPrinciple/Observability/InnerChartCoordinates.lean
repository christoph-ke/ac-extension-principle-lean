module

public import AcExtensionPrinciple.Observability.InnerChartGeometry
public import AcExtensionPrinciple.Observability.FromSolutionJacobian

/-!
# Regular inverse coordinates for an inner cylinder

Paper `e1a0fd5`, `equations.tex` lines 1877–1907 and 1460–1473.
The outgoing coordinate inverts the inner clock. The incoming coordinate
integrates the reciprocal expansion and has a matching affine extension.
BV of the two boundary expansions is an explicit internal calculus premise.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Inverse coordinates for an inner radius-a cylinder, with an affine
earlier-label extension and finite-variation Jacobians. Paper `e1a0fd5`,
lines 1460–1473 and 1877–1907. -/
structure InnerBoundaryCoordinates {b T K a s₀ s₁ : ℝ} {S : SSFields}
    {h : NormalizedChartData b T K S} (c : InnerCylinder h a s₀ s₁) (T' : ℝ) where
  U : ℝ ≃o ℝ
  V : ℝ ≃o ℝ
  dU : ℝ → ℝ
  dV : ℝ → ℝ
  duration : c.clock s₁ = T'
  T_nonneg : 0 ≤ T'
  U_initial : U 0 = s₀
  U_terminal : U T' = s₁
  clock : ∀ s ∈ Icc s₀ s₁, U.symm s = c.clock s
  U_derivative : ∀ x, HasDerivAt U (dU x) x
  V_derivative : ∀ x, HasDerivAt V (dV x) x
  dU_continuous : Continuous dU
  dV_continuous : Continuous dV
  dU_positive : ∀ x, 0 < dU x
  dV_positive : ∀ x, 0 < dV x
  boundary : ∀ x ∈ Icc 0 T', V x = c.v (U x)
  U_jacobian : ∀ x ∈ Icc 0 T', dU x = (-S.nu (U x) (c.v (U x)))⁻¹
  V_jacobian : ∀ x ∈ Icc 0 T', dV x = (S.lam (U x) (c.v (U x)))⁻¹
  earlier : ∀ x ≤ 0, V x = c.v s₀ + (S.lam s₀ (c.v s₀))⁻¹ * x
  dU_variation : BoundedVariationOn dU (Icc 0 T')
  dV_variation : ∀ x y, BoundedVariationOn dV (Icc x y)

namespace InnerCylinder

variable {b T K a s₀ s₁ : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable (c : InnerCylinder h a s₀ s₁)

/-- The constantly extended clock agrees with the actual inner clock
on the physical interval. Paper `e1a0fd5`, lines 1877–1887. -/
theorem regularClock_eq {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    regularChartClock (fun z => -S.nu z (c.v z)) s₀ s₁ s = c.clock s := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hs.1] at hz
  exact chartClockDensity_eq ⟨hz.1, hz.2.trans hs.2⟩

/-- Construct both inverse coordinates and the regular earlier-label
extension. The expansion BV premises concern only coordinate regularity;
the clock lower bound is the paper's late annular bound. Paper `e1a0fd5`,
lines 1877–1907 and 1460–1473. -/
theorem exists_coordinates_of_boundary_variation
    (hhalf : ∀ s ∈ Icc s₀ s₁, 1 / 2 ≤ -S.nu s (c.v s))
    (hnuBV : BoundedVariationOn (fun s => -S.nu s (c.v s)) (Icc s₀ s₁))
    (hlamBV : BoundedVariationOn (fun s => S.lam s (c.v s)) (Icc s₀ s₁)) :
    Nonempty (InnerBoundaryCoordinates c (c.clock s₁)) := by
  let w := fun s => -S.nu s (c.v s)
  have hw := c.density_continuous_positive.1
  let e := regularChartClockIso w c.ordered hw (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  let U := e.symm
  let dU := fun x => (chartClockDensity w s₀ s₁ (U x))⁻¹
  let T' := c.clock s₁
  have heq (s : ℝ) (hs : s ∈ Icc s₀ s₁) : e s = c.clock s :=
    c.regularClock_eq hs
  have he0 : e s₀ = 0 := by
    change regularChartClock w s₀ s₁ s₀ = 0
    simp [regularChartClock]
  have he1 : e s₁ = T' := heq s₁ ⟨c.ordered, le_rfl⟩
  have hT : 0 ≤ T' := by
    rw [← he1, ← he0]
    exact e.monotone c.ordered
  have hU0 : U 0 = s₀ := by rw [← he0]; exact e.symm_apply_apply s₀
  have hU1 : U T' = s₁ := by rw [← he1]; exact e.symm_apply_apply s₁
  have hmap : MapsTo U (Icc 0 T') (Icc s₀ s₁) := by
    intro x hx
    constructor
    · simpa only [hU0] using U.monotone hx.1
    · simpa only [hU1] using U.monotone hx.2
  have hUd : ∀ x, HasDerivAt U (dU x) x :=
    regularChartClockIso_inverse_hasDerivAt c.ordered hw (by norm_num) hhalf
  have hUC : Continuous dU :=
    ((chartClockDensity_continuous c.ordered hw).comp U.continuous).inv₀
      (fun x => (show 0 < chartClockDensity w s₀ s₁ (U x) from
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
          (chartClockDensity_lower c.ordered hhalf _)).ne')
  have hUP (x : ℝ) : 0 < dU x := inv_pos.mpr
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (chartClockDensity_lower c.ordered hhalf _))
  have hUJ (x : ℝ) (hx : x ∈ Icc 0 T') : dU x = (w (U x))⁻¹ := by
    dsimp only [dU]
    rw [chartClockDensity_eq (hmap hx)]
  have hUBV : BoundedVariationOn dU (Icc 0 T') := by
    have hwBV : BoundedVariationOn (fun x => w (U x)) (Icc 0 T') :=
      ne_top_of_le_ne_top hnuBV
        (eVariationOn.comp_le_of_monotoneOn w U (U.monotone.monotoneOn _) hmap)
    have hi := boundedVariation_chart_reciprocal (by norm_num : (0 : ℝ) < 1 / 2)
      hwBV (fun x hx => hhalf _ (hmap hx))
    change eVariationOn dU (Icc 0 T') ≠ ⊤
    rw [eVariationOn.congr (fun x hx => hUJ x hx)]
    exact hi
  let j := fun x => (S.lam (U x) (c.v (U x)))⁻¹
  have hc := continuousOn_id.prodMk c.continuous_v
  have hLC := h.continuous_lam.comp hc (fun _ hs => (c.source_mem hs).1)
  have hjC : ContinuousOn j (Icc 0 T') :=
    (hLC.comp U.continuous.continuousOn hmap).inv₀
      (fun x hx => (h.signs _ _ (c.source_mem (hmap hx)).1).1.ne')
  have htlabel (s : ℝ) (hs : s ∈ Icc s₀ s₁) : 0 ≤ c.v s :=
    (PropA4.axis_label_nonneg h ⟨(c.source_mem hs).1.1, (c.source_mem hs).1.2.1⟩
      (c.late.trans hs.1)).trans (c.points s hs).1.le
  have hjlo : ∀ x ∈ Icc 0 T', (1 : ℝ) ≤ j x := by
    intro x hx
    exact one_le_inv_iff₀.mpr
      ⟨(h.signs _ _ (c.source_mem (hmap hx)).1).1,
        (h.lam_bounds (htlabel _ (hmap hx)) (c.source_mem (hmap hx))).2⟩
  let ej := regularChartClockIso j hT hjC zero_lt_one hjlo
  let V := ej.trans (OrderIso.addRight (c.v s₀))
  let dV := chartClockDensity j 0 T'
  have hVD : ∀ x, HasDerivAt V (dV x) x := by
    intro x
    convert (regularChartClock_hasDerivAt hT hjC x).add_const (c.v s₀) using 1
    ext z
    rfl
  have hvC : ContinuousOn (fun x => c.v (U x)) (Icc 0 T') :=
    c.continuous_v.comp U.continuous.continuousOn hmap
  have hvD : ∀ x ∈ Ioo 0 T', HasDerivAt (fun x => c.v (U x)) (j x) x := by
    intro x hx
    have hxC := Ioo_subset_Icc_self hx
    have hxU : U x ∈ Ioo s₀ s₁ := by
      constructor
      · simpa only [hU0] using U.strictMono hx.1
      · simpa only [hU1] using U.strictMono hx.2
    have hd := (c.tangent (U x) hxU).comp x (hUd x)
    rw [hUJ x hxC] at hd
    apply hd.congr_deriv
    dsimp only [j, w]
    have hn := (h.signs _ _ (c.source_mem (hmap hxC)).1).2.1.ne
    have hl := (h.signs _ _ (c.source_mem (hmap hxC)).1).1.ne'
    field_simp [hn, hl]
  have hB : ∀ x ∈ Icc 0 T', V x = c.v (U x) := by
    intro x hx
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hvC.mono (Icc_subset_Icc le_rfl hx.2))
      (fun z hz => hvD z ⟨hz.1, hz.2.trans_le hx.2⟩)
      ((hjC.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc
        (μ := volume) hx.1)
    have hj : regularChartClock j 0 T' x = ∫ z in 0..x, j z := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le hx.1] at hz
      exact chartClockDensity_eq ⟨hz.1, hz.2.trans hx.2⟩
    change regularChartClock j 0 T' x + c.v s₀ = c.v (U x)
    rw [hj, hi, hU0]
    ring
  have hK : 0 < K := zero_lt_one.trans_le h.K_ge_one
  have hjBV : BoundedVariationOn j (Icc 0 T') := by
    have hlBV : BoundedVariationOn (fun x => S.lam (U x) (c.v (U x))) (Icc 0 T') :=
      ne_top_of_le_ne_top hlamBV
        (eVariationOn.comp_le_of_monotoneOn (fun s => S.lam s (c.v s)) U
          (U.monotone.monotoneOn _) hmap)
    exact boundedVariation_chart_reciprocal (inv_pos.mpr hK) hlBV
      (fun x hx => (h.lam_bounds (htlabel _ (hmap hx)) (c.source_mem (hmap hx))).1)
  refine ⟨{
    U := U, V := V, dU := dU, dV := dV
    duration := rfl, T_nonneg := hT
    U_initial := hU0, U_terminal := hU1
    clock := heq
    U_derivative := hUd, V_derivative := hVD
    dU_continuous := hUC
    dV_continuous := chartClockDensity_continuous hT hjC
    dU_positive := hUP
    dV_positive := fun x => zero_lt_one.trans_le (chartClockDensity_lower hT hjlo x)
    boundary := hB
    U_jacobian := hUJ
    V_jacobian := fun _ hx => chartClockDensity_eq hx
    earlier := ?_
    dU_variation := hUBV
    dV_variation := fun x y => boundedVariation_chartClockDensity hT hjBV }⟩
  intro x hx
  have hj : regularChartClock j 0 T' x = j 0 * x := by
    unfold regularChartClock
    have he : (∫ z in 0..x, chartClockDensity j 0 T' z) = ∫ _z in 0..x, j 0 := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_ge hx] at hz
      simp only [chartClockDensity, min_eq_left (hz.2.trans hT), max_eq_left hz.2]
    rw [he]
    simp [mul_comm]
  change regularChartClock j 0 T' x + c.v s₀ = c.v s₀ + _
  rw [hj]
  dsimp only [j]
  rw [hU0]
  ring

end InnerCylinder

end AcExtensionPrinciple

end
