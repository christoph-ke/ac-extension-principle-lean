module

public import AcExtensionPrinciple.Observability.LemmaA3Weight

/-!
# Lemma A.3: uniform constants and logarithmic duration

Paper `e1a0fd5`, `eq:observability-positive-mass-duration`, lines 1633–1637,
and uniform small-flux constants at lines 1554–1558 and 1623–1628.
-/

public section

namespace AcExtensionPrinciple

/-- The paper's annular gap parameter. Paper `e1a0fd5`, line 1554. -/
@[expose] noncomputable def lemmaA3Delta (K : ℝ) : ℝ := 1 / (8 * K)

/-- The paper's duration factor. Paper `e1a0fd5`,
`eq:observability-positive-mass-duration`, lines 1633–1637. -/
@[expose] noncomputable def lemmaA3Duration (K ε : ℝ) : ℝ :=
  max (K + 1) (1 + Real.log (2 / (ε * lemmaA3Delta K)))

/-- A uniform upper coefficient for the outgoing flux on the annulus.
Paper `e1a0fd5`, `eq:observability-annular-gronwall`, lines 1607–1611. -/
@[expose] noncomputable def lemmaA3FluxCoefficient (δ : ℝ) : ℝ := 4 * (1 + δ) / δ

/-- Explicit positive small-flux constant independent of ε. Paper `e1a0fd5`,
`eq:observability-small-mass-flux`, lines 1554–1558, 1623–1628. -/
@[expose] noncomputable def lemmaA3SmallConstant (K : ℝ) : ℝ :=
  min (lemmaA3Delta K / 2)
    (lemmaA3Delta K ^ 3 * Real.exp (-8 / lemmaA3Delta K) /
      (8 * lemmaA3FluxCoefficient (lemmaA3Delta K)))

/-- An explicit logarithmic duration constant. Paper `e1a0fd5`,
`eq:observability-positive-mass-duration`, lines 1633–1637, 1663. -/
@[expose] noncomputable def lemmaA3DurationConstant (K : ℝ) : ℝ := K + 2 + Real.log (16 * K)

/-- The uniform parameters are strictly positive and satisfy both needed
smallness conditions. Paper `e1a0fd5`, lines 1554–1558, 1623–1628. -/
theorem lemmaA3_constants {K : ℝ} (hK : 1 ≤ K) :
    0 < lemmaA3Delta K ∧ lemmaA3Delta K ≤ 1 ∧
      1 ≤ lemmaA3FluxCoefficient (lemmaA3Delta K) ∧
      0 < lemmaA3SmallConstant K ∧
      lemmaA3SmallConstant K ≤ lemmaA3Delta K / 2 ∧
      lemmaA3SmallConstant K ≤ lemmaA3Delta K ^ 3 * Real.exp (-8 / lemmaA3Delta K) /
        (8 * lemmaA3FluxCoefficient (lemmaA3Delta K)) := by
  have hK0 : 0 < K := by linarith
  have hδ : 0 < lemmaA3Delta K := by unfold lemmaA3Delta; positivity
  have hδ1 : lemmaA3Delta K ≤ 1 := by
    unfold lemmaA3Delta
    apply (div_le_one (by positivity : 0 < 8 * K)).mpr
    linarith
  have hA : 1 ≤ lemmaA3FluxCoefficient (lemmaA3Delta K) := by
    unfold lemmaA3FluxCoefficient
    apply (le_div_iff₀ hδ).mpr
    linarith
  refine ⟨hδ, hδ1, hA, ?_, min_le_left _ _, min_le_right _ _⟩
  unfold lemmaA3SmallConstant
  apply lt_min <;> positivity

/-- The chosen duration dominates the geometric axis time and grows at most
like `1+|log ε|`. Paper `e1a0fd5`, lines 1633–1637, 1663. -/
theorem lemmaA3_duration_bounds {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) :
    K ≤ lemmaA3Duration K ε ∧
      lemmaA3Duration K ε ≤ lemmaA3DurationConstant K * (1 + |Real.log ε|) ∧
      1 ≤ lemmaA3DurationConstant K := by
  have hK0 : 0 < K := by linarith
  have hlog : 0 ≤ Real.log (16 * K) := Real.log_nonneg (by linarith)
  have hC : 1 ≤ lemmaA3DurationConstant K := by unfold lemmaA3DurationConstant; linarith
  have he : 2 / (ε * lemmaA3Delta K) = (16 * K) / ε := by
    unfold lemmaA3Delta
    field_simp [hε.ne', hK0.ne']
    ring
  have hlogeq : Real.log (2 / (ε * lemmaA3Delta K)) = Real.log (16 * K) - Real.log ε := by
    rw [he, Real.log_div (by positivity : 16 * K ≠ 0) hε.ne']
  refine ⟨(by unfold lemmaA3Duration; exact (by linarith : K ≤ K + 1).trans (le_max_left _ _)), ?_, hC⟩
  unfold lemmaA3Duration
  apply max_le
  · unfold lemmaA3DurationConstant at *
    nlinarith [abs_nonneg (Real.log ε)]
  · rw [hlogeq]
    unfold lemmaA3DurationConstant at *
    nlinarith [abs_nonneg (Real.log ε), neg_le_abs (Real.log ε)]

end AcExtensionPrinciple

end
