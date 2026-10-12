module

public import AcExtensionPrinciple.Observability.FromSolutionRealization
public import AcExtensionPrinciple.Continuation.ProperBounds
public import AcExtensionPrinciple.Integration.CylinderStatements
public import AcExtensionPrinciple.Integration.Observability

/-!
# Constant scalar translation in a normalized chart

Paper `e1a0fd5`, equations.tex lines 1475–1480 and 1923–1929.
The primitive equations are invariant. Uniform expansion BV is an internal
premise for the translated scalar-derivative BV bounds; it is discharged
for the constructed source chart in `SourceChartVariation`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Translate the scalar while retaining the geometry and mass.
Paper `e1a0fd5`, lines 1475–1480 and 1923–1929. -/
@[expose] noncomputable def SSFields.integrationScalarShift (S : SSFields) (c : ℝ) : SSFields where
  r := S.r
  m := S.m
  lam := S.lam
  nu := S.nu
  phi s t := S.phi s t - c
  dvpsi s t := S.dvpsi s t - c * S.lam s t
  dupsi s t := S.dupsi s t - c * S.nu s t

/-- Translation preserves both physical scalar amplitudes, all mass densities,
and the mixed radius coefficient. Paper `e1a0fd5`, lines 1475–1492. -/
theorem integrationScalarShift_invariants (S : SSFields) (c s t : ℝ) :
    (S.integrationScalarShift c).theta s t = S.theta s t ∧
    (S.integrationScalarShift c).zeta s t = S.zeta s t ∧
    (S.integrationScalarShift c).massV s t = S.massV s t ∧
    (S.integrationScalarShift c).massU s t = S.massU s t ∧
    (S.integrationScalarShift c).radiusCoeff s t = S.radiusCoeff s t := by
  have ht : (S.integrationScalarShift c).theta s t = S.theta s t := by
    simp only [SSFields.theta, SSFields.integrationScalarShift]; ring
  have hz : (S.integrationScalarShift c).zeta s t = S.zeta s t := by
    simp only [SSFields.zeta, SSFields.integrationScalarShift]; ring
  refine ⟨ht, hz, ?_, ?_, rfl⟩
  · simp only [SSFields.massV, ht]; rfl
  · simp only [SSFields.massU, hz]; rfl

/-- Subtraction and constant scaling preserve interval primitives.
Paper `e1a0fd5`, lines 1475–1492, translation component. -/
theorem integration_primitive_sub_mul {f g F G : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalPrimitive f F a b) (hg : IntervalPrimitive g G a b) (c : ℝ) :
    IntervalPrimitive (fun x => f x - c * g x) (fun x => F x - c * G x) a b := by
  refine ⟨hf.1.sub (hg.1.const_mul c), ?_⟩
  rw [intervalIntegral.integral_sub hf.1 (hg.1.const_mul c),
    intervalIntegral.integral_const_mul, ← hf.2, ← hg.2]
  ring

/-- All ten chart equations survive constant scalar translation.
Paper `e1a0fd5`, lines 1475–1492 and 1923–1929. -/
theorem ChartIntegralEquations.integrationScalarShift {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChartIntegralEquations D S) (c : ℝ) :
    ChartIntegralEquations D (S.integrationScalarShift c) where
  radius_t := h.radius_t
  radius_s := h.radius_s
  psi_t := by
    intro s a b hab hseg
    apply (integration_primitive_sub_mul (h.psi_t s a b hab hseg)
      (h.radius_t s a b hab hseg) c).congr
    · intro x _; dsimp [SSFields.integrationScalarShift]; ring
    · intro x _; rfl
  psi_s := by
    intro t a b hab hseg
    apply (integration_primitive_sub_mul (h.psi_s t a b hab hseg)
      (h.radius_s t a b hab hseg) c).congr
    · intro x _; dsimp [SSFields.integrationScalarShift]; ring
    · intro x _; rfl
  mass_t := by
    intro s a b hab hseg
    exact (h.mass_t s a b hab hseg).congr (fun _ _ => rfl)
      (fun x _ => (integrationScalarShift_invariants S c s x).2.2.1.symm)
  mass_s := by
    intro t a b hab hseg
    exact (h.mass_s t a b hab hseg).congr (fun _ _ => rfl)
      (fun x _ => (integrationScalarShift_invariants S c x t).2.2.2.1.symm)
  lam_s := h.lam_s
  nu_t := h.nu_t
  dvpsi_s := by
    intro t a b hab hseg
    apply (integration_primitive_sub_mul (h.dvpsi_s t a b hab hseg)
      (h.lam_s t a b hab hseg) c).congr
    · intro x _; rfl
    · intro x _; dsimp [SSFields.integrationScalarShift, SSFields.radiusCoeff, SSFields.mu]; ring
  dupsi_t := by
    intro s a b hab hseg
    apply (integration_primitive_sub_mul (h.dupsi_t s a b hab hseg)
      (h.nu_t s a b hab hseg) c).congr
    · intro x _; rfl
    · intro x _; dsimp [SSFields.integrationScalarShift, SSFields.radiusCoeff, SSFields.mu]; ring

/-- Constant multiplication scales real variation by at most |c|.
Paper `e1a0fd5`, lines 1441–1443 and 1475–1480, BV translation component. -/
theorem integration_variation_const_mul (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun x => c * f x) s ≤ ENNReal.ofReal |c| * eVariationOn f s := by
  apply iSup_le
  rintro ⟨n, u, hm, hs⟩
  have he : ∀ x y : ℝ, edist (c * x) (c * y) = ENNReal.ofReal |c| * edist x y := by
    intro x y
    simp only [edist_dist, Real.dist_eq, ← mul_sub, abs_mul,
      ENNReal.ofReal_mul (abs_nonneg c)]
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_right (eVariationOn.sum_le hm hs) _

/-- Translation preserves the chart when expansion BV on compact sets is
available. That helper premise comes from the source class and chart Jacobians.
Paper `e1a0fd5`, lines 1441–1443, 1475–1480 and 1923–1929. -/
@[expose] noncomputable def NormalizedChartData.integrationScalarShift {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (c : ℝ)
    (hl : ∀ C, IsCompact C → C ⊆ chartCylinder h.g T → ∃ A : ℝ,
      ∀ s a d, a ≤ d → outSeg s a d ⊆ C →
        eVariationOn (S.lam s) (Icc a d) ≤ ENNReal.ofReal A)
    (hn : ∀ C, IsCompact C → C ⊆ chartCylinder h.g T → ∃ A : ℝ,
      ∀ t a d, a ≤ d → inSeg t a d ⊆ C →
        eVariationOn (fun s => S.nu s t) (Icc a d) ≤ ENNReal.ofReal A) :
    NormalizedChartData b T K (S.integrationScalarShift c) where
  g := h.g
  b_pos := h.b_pos
  T_nonneg := h.T_nonneg
  K_ge_one := h.K_ge_one
  continuous_g := h.continuous_g
  monotone_g := h.monotone_g
  axis_before_boundary := h.axis_before_boundary
  equations := h.equations.integrationScalarShift c
  continuous_r := h.continuous_r
  continuous_m := h.continuous_m
  continuous_phi := h.continuous_phi.sub continuousOn_const
  continuous_lam := h.continuous_lam
  continuous_nu := h.continuous_nu
  signs := h.signs
  gap := h.gap
  axis_values := h.axis_values
  boundary_gauge := h.boundary_gauge
  incoming_ratio := h.incoming_ratio
  axis_reached := h.axis_reached
  psi_t_variation := by
    intro C hC hsub
    obtain ⟨A, hA⟩ := h.psi_t_variation C hC hsub
    obtain ⟨B, hB⟩ := hl C hC hsub
    refine ⟨(ENNReal.ofReal A + ENNReal.ofReal |c| * ENNReal.ofReal B).toReal, ?_⟩
    intro s a d had hseg
    rw [ENNReal.ofReal_toReal (by finiteness)]
    exact (variation_sub_le _ _ _).trans (add_le_add (hA s a d had hseg)
      ((integration_variation_const_mul _ _ _).trans
        (mul_le_mul_right (hB s a d had hseg) _)))
  psi_s_variation := by
    intro C hC hsub
    obtain ⟨A, hA⟩ := h.psi_s_variation C hC hsub
    obtain ⟨B, hB⟩ := hn C hC hsub
    refine ⟨(ENNReal.ofReal A + ENNReal.ofReal |c| * ENNReal.ofReal B).toReal, ?_⟩
    intro t a d had hseg
    rw [ENNReal.ofReal_toReal (by finiteness)]
    exact (variation_sub_le _ _ _).trans (add_le_add (hA t a d had hseg)
      ((integration_variation_const_mul _ _ _).trans
        (mul_le_mul_right (hB t a d had hseg) _)))

/-- The initial shifted energy has precisely the displayed translated form.
Paper `e1a0fd5`, lines 1928–1929. -/
theorem NormalizedChartData.integrationScalarShift_initial {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (c : ℝ) :
    chartShiftedEnergy b (S.integrationScalarShift c) 0 =
      b / 2 * ((S.phi 0 0 - c) ^ 2 - Real.log (1 - S.mu 0 0)) := by
  have hr := (h.boundary_gauge 0 ⟨le_rfl, h.T_nonneg⟩).1
  simp only [chartShiftedEnergy, boundaryEnergy, chartPsi, SSFields.integrationScalarShift,
    hr, mul_div_cancel_left₀ _ h.b_pos.ne', SSFields.mu]

/-- Constant scalar translation changes the radial observation by c and leaves
its boundary trace derivative unchanged a.e. Paper `e1a0fd5`, lines 1923–1929. -/
theorem NormalizedChartData.integrationScalarShift_energy {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (c : ℝ) :
    chartScalarEnergy (S.integrationScalarShift c) T = PropA4.translatedScalarEnergy S T c := by
  have he : EqOn (fun s => chartPsi (S.integrationScalarShift c) s s)
      (fun s => chartPsi S s s - b * c) (Icc 0 T) := by
    intro s hs
    dsimp [chartPsi, SSFields.integrationScalarShift]
    rw [(h.boundary_gauge s hs).1]
    ring
  unfold chartScalarEnergy PropA4.translatedScalarEnergy
  apply intervalIntegral.integral_congr_ae
  filter_upwards [show ∀ᵐ s : ℝ, s ≠ T by simp [ae_iff]] with s hs
  intro hsI
  rw [uIoc_of_le h.T_nonneg] at hsI
  have hd := integration_deriv_eq_of_eqOn he
    (show s ∈ Ioo 0 T from ⟨hsI.1, lt_of_le_of_ne hsI.2 hs⟩)
  rw [hd, deriv_sub_const]
  have hb := (h.boundary_gauge s ⟨hsI.1.le, hsI.2⟩).2.2
  dsimp only [SSFields.integrationScalarShift]
  rw [hb, mul_one]

end AcExtensionPrinciple

end
