module

public import AcExtensionPrinciple.Weighted.ClassComparison
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Truncated domains, weighted norms, and the radial operator

Paper `e1a0fd5`, `equations.tex` lines 1146–1164.
The norms take values in ℝ≥0∞, preserving finiteness as a separate assertion.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The closed proper triangle D_U. Paper `e1a0fd5`,
`eq:weighted-truncated-domain`, line 1148. -/
@[expose] def weightedTruncatedDomain (u₀ U : ℝ) : Set (ℝ × ℝ) :=
  {p | u₀ ≤ p.1 ∧ p.1 ≤ U ∧ p.1 ≤ p.2 ∧ p.2 ≤ 0}

/-- The remainder weight. Paper `e1a0fd5`,
`eq:weighted-remainder-norm`, line 1150. -/
@[expose] noncomputable def weightedRemainderDensity (S : SSFields) (p : ℝ × ℝ) : ℝ :=
  (-S.nu p.1 p.2) / ((1 - S.mu p.1 p.2) ^ 2 * S.lam p.1 p.2)

/-- The source weight. Paper `e1a0fd5`,
`eq:weighted-source-norm`, line 1152. -/
@[expose] noncomputable def weightedSourceDensity (S : SSFields) (p : ℝ × ℝ) : ℝ :=
  (-S.nu p.1 p.2) * S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ^ 2

/-- The squared remainder norm as a lower integral on ℝ². Paper `e1a0fd5`,
`eq:weighted-remainder-norm`, line 1150. -/
@[expose] noncomputable def weightedRemainderNormSq
    (S : SSFields) (u₀ U : ℝ) (W : ℝ × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in weightedTruncatedDomain u₀ U,
    ENNReal.ofReal (weightedRemainderDensity S p * |W p| ^ 2)

/-- The squared source norm as a lower integral on ℝ². Paper `e1a0fd5`,
`eq:weighted-source-norm`, line 1152. -/
@[expose] noncomputable def weightedSourceNormSq
    (S : SSFields) (u₀ U : ℝ) (F : ℝ × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in weightedTruncatedDomain u₀ U,
    ENNReal.ofReal (weightedSourceDensity S p * |F p| ^ 2)

/-- N_U, with infinity retained. Paper `e1a0fd5`,
`eq:weighted-remainder-norm`, line 1150. -/
@[expose] noncomputable def weightedRemainderNorm
    (S : SSFields) (u₀ U : ℝ) (W : ℝ × ℝ → ℝ) : ℝ≥0∞ :=
  weightedRemainderNormSq S u₀ U W ^ (1 / 2 : ℝ)

/-- M_U, with infinity retained. Paper `e1a0fd5`,
`eq:weighted-source-norm`, line 1152. -/
@[expose] noncomputable def weightedSourceNorm
    (S : SSFields) (u₀ U : ℝ) (F : ℝ × ℝ → ℝ) : ℝ≥0∞ :=
  weightedSourceNormSq S u₀ U F ^ (1 / 2 : ℝ)

/-- Incoming normalized amplitude, retaining the actual scalar coefficient.
Paper `e1a0fd5`, `eq:weighted-radial-operator`, line 1158. -/
@[expose] noncomputable def weightedIncomingAmplitude (S : SSFields) (u v : ℝ) : ℝ :=
  (S.r u v / S.nu u v) * S.duphi u v

/-- The radial operator T in the original double-null coordinates.
Paper `e1a0fd5`, `eq:weighted-radial-operator`, lines 1157–1159. -/
@[expose] noncomputable def weightedRadialOperator
    (S : SSFields) (W : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (S.r p.1 p.2 ^ 2)⁻¹ * ∫ s in p.1..p.2,
    S.r p.1 s * (weightedIncomingAmplitude S p.1 s * W (p.1, s))

/-- The L¹ remainder quantity used for uniqueness. Paper `e1a0fd5`,
`eq:radial-l1-estimate`, lines 1179–1181. -/
@[expose] noncomputable def weightedRemainderL1
    (S : SSFields) (u₀ U : ℝ) (W : ℝ × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in weightedTruncatedDomain u₀ U,
    ENNReal.ofReal (weightedRemainderDensity S p * |W p|)

/-- The L¹ source quantity uses no λ in its weight. Paper `e1a0fd5`,
`eq:radial-l1-estimate`, lines 1179–1181. -/
@[expose] noncomputable def weightedSourceL1
    (S : SSFields) (u₀ U : ℝ) (F : ℝ × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in weightedTruncatedDomain u₀ U,
    ENNReal.ofReal ((-S.nu p.1 p.2) / (1 - S.mu p.1 p.2) ^ 2 * |F p|)

/-- The kernel G_a, with the incoming amplitude inside it. Paper `e1a0fd5`,
`lem:weighted-radial-estimates`, lines 1187–1190. -/
@[expose] noncomputable def weightedTransportKernel
    (S : SSFields) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < a ∧ a < p.2 then
    S.r p.1 a / S.r p.1 p.2 ^ 2 * weightedIncomingAmplitude S p.1 a else 0

/-- D_U is measurable. Paper `e1a0fd5`,
`eq:weighted-truncated-domain`, line 1148. -/
theorem measurableSet_weightedTruncatedDomain (u₀ U : ℝ) :
    MeasurableSet (weightedTruncatedDomain u₀ U) := by
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)))

/-- Each proper truncated domain is compact, including its axis edge.
Paper `e1a0fd5`, `eq:weighted-truncated-domain`, line 1148. -/
theorem isCompact_weightedTruncatedDomain (u₀ U : ℝ) :
    IsCompact (weightedTruncatedDomain u₀ U) := by
  have hc : IsClosed (weightedTruncatedDomain u₀ U) :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le continuous_fst continuous_snd).inter
          (isClosed_le continuous_snd continuous_const)))
  exact (isCompact_Icc.prod (isCompact_Icc (a := u₀) (b := 0))).of_isClosed_subset hc
    (fun p hp => ⟨⟨hp.1, hp.2.1⟩, ⟨hp.1.trans hp.2.2.1, hp.2.2.2⟩⟩)

/-- The proper truncation lies in the solution domain. Paper `e1a0fd5`,
`eq:weighted-truncated-domain`, lines 1146–1148. -/
theorem weightedTruncatedDomain_subset_triangle {ui u₀ U : ℝ} (hi : ui ≤ u₀)
    (hU : U < 0) : weightedTruncatedDomain u₀ U ⊆ pastTriangle ui :=
  fun _ hp => ⟨hi.trans hp.1, hp.2.1.trans_lt hU, hp.2.2.1, hp.2.2.2⟩

/-- Increasing the truncation time increases the domain. Paper `e1a0fd5`,
`eq:weighted-truncated-domain`, line 1148; monotone convergence at line 1318. -/
theorem weightedTruncatedDomain_mono {u₀ U V : ℝ} (hUV : U ≤ V) :
    weightedTruncatedDomain u₀ U ⊆ weightedTruncatedDomain u₀ V :=
  fun _ hp => ⟨hp.1, hp.2.1.trans hUV, hp.2.2⟩

/-- Source and remainder weights differ by λ². Paper `e1a0fd5`,
`eq:weighted-remainder-norm`, `eq:weighted-source-norm`, lines 1150–1152. -/
theorem weightedSourceDensity_eq (S : SSFields) {p : ℝ × ℝ}
    (hl : S.lam p.1 p.2 ≠ 0) :
    weightedSourceDensity S p = weightedRemainderDensity S p * S.lam p.1 p.2 ^ 2 := by
  unfold weightedSourceDensity weightedRemainderDensity
  field_simp

/-- Squaring the extended remainder norm recovers its lower integral.
Paper `e1a0fd5`, `eq:weighted-remainder-norm`, line 1150. -/
theorem weightedRemainderNorm_sq (S : SSFields) (u₀ U : ℝ) (W : ℝ × ℝ → ℝ) :
    weightedRemainderNorm S u₀ U W ^ 2 = weightedRemainderNormSq S u₀ U W := by
  rw [weightedRemainderNorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Squaring the extended source norm recovers its lower integral.
Paper `e1a0fd5`, `eq:weighted-source-norm`, line 1152. -/
theorem weightedSourceNorm_sq (S : SSFields) (u₀ U : ℝ) (F : ℝ × ℝ → ℝ) :
    weightedSourceNorm S u₀ U F ^ 2 = weightedSourceNormSq S u₀ U F := by
  rw [weightedSourceNorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end AcExtensionPrinciple

end
