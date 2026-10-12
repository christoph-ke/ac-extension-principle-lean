module

public import AcExtensionPrinciple.Observability.LemmaA2

/-!
# Statements and interfaces for uniform mass observation

Statements from paper `e1a0fd5`, `equations.tex` lines 1533–1663
and 1665–1913. The positive-mass lemma is an explicit premise `LemmaA3Statement`.
No theorem in this file asserts Proposition A.4.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Duration in Lemma A.3, with `δ₀ = 1/(8K)`. Paper `e1a0fd5`,
`eq:observability-positive-mass-duration`, lines 1636–1639. -/
@[expose] noncomputable def positiveMassDuration (K ε : ℝ) : ℝ :=
  max (K + 1) (1 + Real.log (2 / (ε * (1 / (8 * K)))))

/-- The observation after translating `φ` by `c`. The boundary value of
`r` is constant, so its scalar trace derivative is unchanged. Paper `e1a0fd5`,
`eq:observability-energy-integral`, lines 1477–1480 and 1922–1930. -/
@[expose] noncomputable def translatedScalarEnergy (S : SSFields) (T c : ℝ) : ℝ :=
  ∫ s in 0..T, (S.dvpsi s s - c) ^ 2 + deriv (fun s => chartPsi S s s) s ^ 2

/-- Zero translation recovers the stored observation. Paper `e1a0fd5`,
`eq:observability-energy-integral`, lines 1477–1480. -/
theorem translatedScalarEnergy_zero (S : SSFields) (T : ℝ) :
    translatedScalarEnergy S T 0 = chartScalarEnergy S T := by
  simp [translatedScalarEnergy, chartScalarEnergy]

/-- Positive-mass premise, uniform in radius, chart, threshold,
and scalar translation, with its observation constant chosen first. Paper
`e1a0fd5`, `lem:observability-positive-mass`, lines 1533–1663. -/
@[expose] def LemmaA3Statement (K : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ε b : ℝ) (S : SSFields),
    0 < ε → ε < 1 →
    NormalizedChartData b (positiveMassDuration K ε * b) K S →
    ε ≤ S.mu 0 0 → ∀ shift : ℝ,
      c * ε ^ 3 * b / (1 + |Real.log ε|) ^ 2 ≤
        translatedScalarEnergy S (positiveMassDuration K ε * b) shift

/-- Uniform mass observation, with both constants chosen before the radius
and solution. Paper `e1a0fd5`, `prop:boundary-mass-observability`,
`eq:uniform-boundary-mass-observability`, lines 1665–1673. -/
@[expose] def Statement (K : ℝ) : Prop :=
  ∃ H c : ℝ, K + 4 ≤ H ∧ 0 < c ∧
    ∀ (b : ℝ) (S : SSFields), NormalizedChartData b (H * b) K S →
      c * S.m 0 0 ≤ chartScalarEnergy S (H * b)

/-- A normalized chart may be restricted to a shorter boundary interval.
Paper `e1a0fd5`, lines 1910–1911 and `eq:observability-boundary-gauge`. -/
@[expose] def restrict {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)
    {U : ℝ} (hU : 0 ≤ U) (hUT : U ≤ T) : NormalizedChartData b U K S where
  g := h.g
  b_pos := h.b_pos
  T_nonneg := hU
  K_ge_one := h.K_ge_one
  continuous_g := h.continuous_g
  monotone_g := h.monotone_g.mono (Icc_subset_Icc le_rfl hUT)
  axis_before_boundary := fun s hs => h.axis_before_boundary s ⟨hs.1, hs.2.trans hUT⟩
  equations := {
    radius_t := fun s a c hac hseg => h.equations.radius_t s a c hac
      (fun _ hq => let hh := hseg hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
    radius_s := fun t a c hac hseg => h.equations.radius_s t a c hac
      (fun _ hq => let hh := hseg hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
    psi_t := fun s a c hac hseg => h.equations.psi_t s a c hac
      (fun _ hq => let hh := hseg hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
    psi_s := fun t a c hac hseg => h.equations.psi_s t a c hac
      (fun _ hq => let hh := hseg hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
    mass_t := fun s a c hac hseg => h.equations.mass_t s a c hac
      (fun _ hq => let hh := hseg hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
    mass_s := fun t a c hac hseg => h.equations.mass_s t a c hac
      (fun _ hq => let hh := hseg hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
    lam_s := fun t a c hac hseg => h.equations.lam_s t a c hac
      (fun _ hq => let hh := hseg hq; ⟨⟨hh.1.1, hh.1.2.1.trans hUT, hh.1.2.2⟩, hh.2⟩)
    nu_t := fun s a c hac hseg => h.equations.nu_t s a c hac
      (fun _ hq => let hh := hseg hq; ⟨⟨hh.1.1, hh.1.2.1.trans hUT, hh.1.2.2⟩, hh.2⟩)
    dvpsi_s := fun t a c hac hseg => h.equations.dvpsi_s t a c hac
      (fun _ hq => let hh := hseg hq; ⟨⟨hh.1.1, hh.1.2.1.trans hUT, hh.1.2.2⟩, hh.2⟩)
    dupsi_t := fun s a c hac hseg => h.equations.dupsi_t s a c hac
      (fun _ hq => let hh := hseg hq; ⟨⟨hh.1.1, hh.1.2.1.trans hUT, hh.1.2.2⟩, hh.2⟩) }
  continuous_r := h.continuous_r.mono
    (fun _ hh => ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
  continuous_m := h.continuous_m.mono
    (fun _ hh => ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
  continuous_phi := h.continuous_phi.mono
    (fun _ hh => ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
  continuous_lam := h.continuous_lam.mono
    (fun _ hh => ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
  continuous_nu := h.continuous_nu.mono
    (fun _ hh => ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
  signs := fun s t hh => h.signs s t ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩
  gap := fun s t hh => h.gap s t ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩
  axis_values := fun s hs => h.axis_values s ⟨hs.1, hs.2.trans hUT⟩
  boundary_gauge := fun s hs => h.boundary_gauge s ⟨hs.1, hs.2.trans hUT⟩
  incoming_ratio := fun s t ht hts hs hh => h.incoming_ratio s t ht hts (hs.trans hUT)
    ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩
  axis_reached := fun t ht hh => h.axis_reached t ⟨ht.1, ht.2.trans hUT⟩ (hh.trans hUT)
  psi_t_variation := fun C hC hsub => h.psi_t_variation C hC
    (fun _ hq => let hh := hsub hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)
  psi_s_variation := fun C hC hsub => h.psi_s_variation C hC
    (fun _ hq => let hh := hsub hq; ⟨hh.1, hh.2.1.trans hUT, hh.2.2⟩)

/-- Observation increases with duration. Integrability is derived from the
chart, including that of the actual boundary trace derivative. Paper `e1a0fd5`,
lines 1910–1911 and `eq:observability-energy-integral`. -/
theorem scalarEnergy_mono {b T K U : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hU : 0 ≤ U) (hUT : U ≤ T) :
    chartScalarEnergy S U ≤ chartScalarEnergy S T := by
  unfold chartScalarEnergy
  exact intervalIntegral.integral_mono_interval le_rfl hU hUT
    (Filter.Eventually.of_forall (fun s => by positivity))
    (h.boundary_scalar_square_integrable.2.add h.boundary_psi_deriv_square_integrable)

end PropA4
end AcExtensionPrinciple

end
