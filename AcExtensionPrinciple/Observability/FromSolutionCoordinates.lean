module

public import AcExtensionPrinciple.Observability.FromSolutionIncomingSource
public import AcExtensionPrinciple.Observability.FromSolutionNuTrace

/-!
# The two normalized coordinates of a regular source cylinder

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and 1923–1929.
Both inverse coordinates are constructed, regular and increasing.
The extension below the first entering label has the matching slope.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Constructed boundary coordinates, before transporting the interior
equations. This is coordinate data, not an added source assumption.
Paper `e1a0fd5`, lines 1441–1443, 1460–1473 and 1923–1929. -/
structure NormalizedBoundaryCoordinates {ui b a₀ a₁ : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (a d T : ℝ) where
  U : ℝ ≃o ℝ
  V : ℝ ≃o ℝ
  dU : ℝ → ℝ
  dV : ℝ → ℝ
  duration : c.tau d - c.tau a = T
  T_nonneg : 0 ≤ T
  U_initial : U 0 = a
  U_terminal : U T = d
  clock : ∀ u ∈ Icc a d, U.symm u = normalizedCylinderClock c a u
  U_derivative : ∀ s, HasDerivAt U (dU s) s
  V_derivative : ∀ s, HasDerivAt V (dV s) s
  dU_continuous : Continuous dU
  dV_continuous : Continuous dV
  dU_positive : ∀ s, 0 < dU s
  dV_positive : ∀ s, 0 < dV s
  boundary : ∀ s ∈ Icc 0 T, V s = c.v (U s)
  U_jacobian : ∀ s ∈ Icc 0 T, dU s = (-S.nu (U s) (c.v (U s)))⁻¹
  V_jacobian : ∀ s ∈ Icc 0 T, dV s = (S.lam (U s) (c.v (U s)))⁻¹
  earlier : ∀ s ≤ 0, V s = c.v a + (S.lam a (c.v a))⁻¹ * s
  dU_variation : BoundedVariationOn dU (Icc 0 T)
  dV_variation : ∀ x y, BoundedVariationOn dV (Icc x y)

/-- Every regular source cylinder has regular normalized coordinates with the prescribed clock,
entry labels and affine earlier-label extension. All Jacobian BV premises are discharged from the
standing class. Paper `e1a0fd5`, lines 1460–1473, regular extension as in line 1422. -/
theorem exists_normalizedBoundaryCoordinates {ui b a₀ a₁ a d K : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) :
    Nonempty (NormalizedBoundaryCoordinates c a d (c.tau d - c.tau a)) := by
  let T := c.tau d - c.tau a
  let w := fun u => -S.nu u (c.v u)
  let e := c.normalizedClockIso h hK ha had hd
  let U := e.symm
  let dU := fun s => (chartClockDensity w a d (U s))⁻¹
  have he0 : e a = 0 := c.normalizedClockIso_initial h hK ha had hd
  have heT : e d = T := c.normalizedClockIso_terminal h hK ha had hd
  have hT : 0 ≤ T := by simpa only [he0, heT] using e.monotone had
  have hU0 : U 0 = a := by
    change e.symm 0 = a
    rw [← he0, e.symm_apply_apply]
  have hUT : U T = d := by
    change e.symm T = d
    rw [← heT, e.symm_apply_apply]
  have hmap : MapsTo U (Icc 0 T) (Icc a₀ a₁) :=
    fun s hs => Icc_subset_Icc ha hd (c.normalizedClockIso_inverse_mem h hK ha had hd hs)
  have hUd : ∀ s ∈ Icc 0 T, HasDerivAt U (-S.nu (U s) (c.v (U s)))⁻¹ s :=
    fun s hs => c.normalizedClockIso_inverse_hasDerivAt h hK ha had hd hs
  obtain ⟨i⟩ := exists_regularIncomingCoordinate c h hK hT U hmap hUd
  have hwC := (c.clock_density_continuous h).mono (Icc_subset_Icc ha hd)
  have hwlo : ∀ u ∈ Icc a d, K⁻¹ ≤ w u :=
    fun u hu => c.clock_density_lower hK u (Icc_subset_Icc ha hd hu)
  have hKpos : 0 < K⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hK.1)
  have hDJ : ∀ s ∈ Icc 0 T, dU s = (-S.nu (U s) (c.v (U s)))⁻¹ := by
    intro s hs
    dsimp only [dU]
    rw [chartClockDensity_eq (c.normalizedClockIso_inverse_mem h hK ha had hd hs)]
  have hUBV : BoundedVariationOn dU (Icc 0 T) := by
    change eVariationOn dU (Icc 0 T) ≠ ⊤
    rw [eVariationOn.congr hDJ]
    exact c.outgoing_jacobian_boundedVariation h hK U (U.monotone.monotoneOn _) hmap
  refine ⟨{
    U := U
    V := i.V
    dU := dU
    dV := i.dV
    duration := rfl
    T_nonneg := hT
    U_initial := hU0
    U_terminal := hUT
    clock := fun u hu => c.normalizedClockIso_apply h hK ha had hd hu
    U_derivative := fun s => regularChartClockIso_inverse_hasDerivAt had hwC hKpos hwlo s
    V_derivative := i.derivative
    dU_continuous := ((chartClockDensity_continuous had hwC).comp U.continuous).inv₀
      (fun s => (hKpos.trans_le (chartClockDensity_lower had hwlo (U s))).ne')
    dV_continuous := i.continuous_jacobian
    dU_positive := fun s => inv_pos.mpr
      (hKpos.trans_le (chartClockDensity_lower had hwlo (U s)))
    dV_positive := i.positive_jacobian
    boundary := i.boundary
    U_jacobian := hDJ
    V_jacobian := i.boundary_jacobian
    earlier := ?_
    dU_variation := hUBV
    dV_variation := i.jacobian_variation }⟩
  intro s hs
  simpa only [hU0] using i.earlier s hs

end AcExtensionPrinciple

end
