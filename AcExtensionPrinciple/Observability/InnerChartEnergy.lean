module

public import AcExtensionPrinciple.Observability.InnerChart

/-!
# Exact boundary measure transport for the inner chart

Paper `e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1877–1887.
The a.e. chain rule comes from the inherited normalized chart, rather than
being assumed for the old-coordinate cylinder trace.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace InnerCylinder

variable {b T K a s₀ s₁ : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable (c : InnerCylinder h a s₀ s₁)

/-- The inner clock is the primitive of its continuous positive density.
Paper `e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1877–1887. -/
theorem clock_primitive {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    IntervalPrimitive c.clock (fun z => -S.nu z (c.v z)) s₀ s := by
  have hc := c.density_continuous_positive.1.mono (Icc_subset_Icc le_rfl hs.2)
  refine ⟨hc.intervalIntegrable_of_Icc (μ := volume) hs.1, ?_⟩
  simp [clock]

/-- The inner clock supplies substitution even at a closed-interval
endpoint. Paper `e1a0fd5`, lines 1877–1887. -/
theorem clock_gauge : GaugeSegment c.clock (fun s => -S.nu s (c.v s)) s₀ s₁ := by
  apply GaugeSegment.of_hasDerivWithinAt
  · intro s hs
    rw [uIcc_of_le c.ordered] at hs ⊢
    exact hasDerivWithinAt_of_intervalPrimitives (fun x hx => c.clock_primitive hx)
      c.density_continuous_positive.1 hs
  · intro s hs
    rw [uIcc_of_le c.ordered] at hs
    exact (c.density_continuous_positive.2 s hs).le

/-- The old interval is at most twice as long as its inner boundary
duration under the printed late annular bound. Paper `e1a0fd5`,
lines 1905–1907. -/
theorem outer_duration_le_twice_clock
    (hhalf : ∀ s ∈ Icc s₀ s₁, 1 / 2 ≤ -S.nu s (c.v s)) :
    s₁ - s₀ ≤ 2 * c.clock s₁ := by
  have hc := c.density_continuous_positive.1
  have he := intervalIntegral.integral_mono_on c.ordered intervalIntegrable_const
    (hc.intervalIntegrable_of_Icc (μ := volume) c.ordered) hhalf
  simp only [intervalIntegral.integral_const, smul_eq_mul] at he
  dsimp only [clock]
  linarith

end InnerCylinder

namespace InnerBoundaryCoordinates

variable {b T K a s₀ s₁ T' : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable {c : InnerCylinder h a s₀ s₁} (q : InnerBoundaryCoordinates c T')

include q

/-- The forward inner clock maps precisely into the new boundary-time
interval. Paper `e1a0fd5`, lines 1877–1887. -/
theorem clock_mem {s : ℝ} (hs : s ∈ Icc s₀ s₁) : c.clock s ∈ Icc 0 T' := by
  rw [← q.clock s hs]
  constructor
  · simpa only [← q.U_initial, q.U.symm_apply_apply] using q.U.symm.monotone hs.1
  · simpa only [← q.U_terminal, q.U.symm_apply_apply] using q.U.symm.monotone hs.2

/-- Inverting the forward clock returns the old cylinder parameter.
Paper `e1a0fd5`, lines 1877–1887. -/
theorem inverse_clock {s : ℝ} (hs : s ∈ Icc s₀ s₁) : q.U (c.clock s) = s := by
  rw [← q.clock s hs, q.U.apply_symm_apply]

/-- Pointwise boundary density transport, before integration. Paper
`e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1877–1887. -/
theorem weighted_density_at_clock {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    (q.fields.dvpsi (c.clock s) (c.clock s) ^ 2 +
      (q.fields.dupsi (c.clock s) (c.clock s) + q.fields.dvpsi (c.clock s) (c.clock s)) ^ 2) *
      (-S.nu s (c.v s)) = PropA4.innerBoundaryDensity S s (c.v s) := by
  have ht := q.clock_mem hs
  have hUi := q.inverse_clock hs
  have hVi : q.V (c.clock s) = c.v s := by rw [q.boundary _ ht, hUi]
  have hg := PropA4.separatePullback_energy_density S q.U q.V q.dU q.dV
    (x := c.clock s)
    (by simpa only [hUi, hVi] using (h.signs _ _ (c.source_mem hs).1).2.1)
    (by simpa only [hUi, hVi] using (h.signs _ _ (c.source_mem hs).1).1)
    (by simpa only [q.boundary _ ht] using q.U_jacobian _ ht)
    (by simpa only [q.boundary _ ht] using q.V_jacobian _ ht)
  simpa only [fields, hUi, hVi, mul_comm] using hg

/-- The old-time observation density is integrable, including its BV
scalar representatives. Positive clock substitution transports the
proved inner-chart boundary square integrability. Paper `e1a0fd5`,
`eq:observability-inner-boundary-measure`, lines 1877–1887. -/
theorem observation_integrable :
    IntervalIntegrable (fun s => PropA4.innerBoundaryDensity S s (c.v s)) volume s₀ s₁ := by
  have hsum : IntervalIntegrable
      (fun x => (q.fields.dupsi x x + q.fields.dvpsi x x) ^ 2) volume 0 T' := by
    apply q.chart_data.boundary_psi_deriv_square_integrable.congr_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [q.chart_data.boundary_psi_ae_hasDerivAt] with x hx hxI
    rw [uIoc_of_le q.T_nonneg] at hxI
    rw [(hx ⟨hxI.1.le, hxI.2⟩).deriv]
  have hi := q.chart_data.boundary_scalar_square_integrable.2.add hsum
  have hzero : c.clock s₀ = 0 := by simp [InnerCylinder.clock]
  have hclock := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (g := fun x => q.fields.dvpsi x x ^ 2 + (q.fields.dupsi x x + q.fields.dvpsi x x) ^ 2)
    c.clock_gauge.continuous c.clock_gauge.hasDeriv c.clock_gauge.nonneg
  have hsource := hclock.mpr (by simpa only [hzero, q.duration] using hi)
  apply hsource.congr
  intro s hs
  rw [uIoc_of_le c.ordered] at hs
  exact q.weighted_density_at_clock ⟨hs.1.le, hs.2⟩

/-- The normalized inner observation is exactly the printed old-time
radial density, with Jacobian dτₐ/ds=-r_s. The trace derivative in the
first integral is replaced using the proved a.e. boundary chain rule.
Paper `e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1877–1887. -/
theorem observation_integral_eq :
    chartScalarEnergy q.fields T' =
      ∫ s in s₀..s₁, PropA4.innerBoundaryDensity S s (c.v s) := by
  have he : chartScalarEnergy q.fields T' =
      ∫ x in 0..T', q.fields.dvpsi x x ^ 2 +
        (q.fields.dupsi x x + q.fields.dvpsi x x) ^ 2 := by
    unfold chartScalarEnergy
    apply intervalIntegral.integral_congr_ae
    filter_upwards [q.chart_data.boundary_psi_ae_hasDerivAt] with x hx hxI
    rw [uIoc_of_le q.T_nonneg] at hxI
    rw [(hx ⟨hxI.1.le, hxI.2⟩).deriv]
  rw [he]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun x => q.fields.dvpsi x x ^ 2 +
      (q.fields.dupsi x x + q.fields.dvpsi x x) ^ 2)
    c.clock_gauge.continuous c.clock_gauge.hasDeriv c.clock_gauge.nonneg
  have hzero : c.clock s₀ = 0 := by simp [InnerCylinder.clock]
  simp only [hzero, q.duration, Function.comp_apply] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le c.ordered] at hs
  exact q.weighted_density_at_clock hs

/-- The initial scalar and mass ratio agree with the actual old inner
boundary values. Paper `e1a0fd5`, lines 1877–1879 and 1901–1904. -/
theorem initial_values : q.fields.phi 0 0 = S.phi s₀ (c.v s₀) ∧
    q.fields.mu 0 0 = S.mu s₀ (c.v s₀) := by
  have hz : (0 : ℝ) ∈ Icc 0 T' := ⟨le_rfl, q.T_nonneg⟩
  simp [fields, PropA4.separatePullback, SSFields.mu, massRatio,
    q.boundary 0 hz, q.U_initial]

/-- Apply A.3 directly to the old-coordinate inner boundary observation.
The energy equality is the exact bridge required in A.4. Paper `e1a0fd5`,
`eq:observability-inner-boundary-lower-bound`, lines 1900–1907. -/
theorem inner_observation {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hT : T' = PropA4.positiveMassDuration K ε * a) (hmu : ε ≤ S.mu s₀ (c.v s₀)) :
    ∃ C : ℝ, 0 < C ∧ C * ε ^ 3 * a / (1 + |Real.log ε|) ^ 2 ≤
      ∫ s in s₀..s₁, PropA4.innerBoundaryDensity S s (c.v s) := by
  obtain ⟨C, hC, hobs⟩ := PropA4.inner_observation_of_chart h.K_ge_one
  refine ⟨C, hC, ?_⟩
  have hh := hobs a ε q.fields hε hε1 (hT ▸ q.chart_data)
    (by simpa only [q.initial_values.2] using hmu)
  rw [← hT, q.observation_integral_eq] at hh
  exact hh

end InnerBoundaryCoordinates

end AcExtensionPrinciple

end
