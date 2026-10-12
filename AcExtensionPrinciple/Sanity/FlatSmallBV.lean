module

public import AcExtensionPrinciple.Sanity.FlatFields

/-!
# Constant-data satisfiability of the small-BV input

Sanity checks, paper `e1a0fd5`, `equations.tex` `lem:small-bv-existence`, lines 1364–1388. In the
gauge r = (v-u)/2, the derivative datum c requires scalar value 2c. No restriction on c is needed,
so these checks include nonzero characteristic data.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Flat space realizing derivative datum c in the half-radius gauge.
Paper `e1a0fd5`, `lem:small-bv-existence`, line 1367. -/
@[expose] noncomputable def halfFlat (c : ℝ) : SSFields := scaledFlat (1 / 2) (2 * c)

/-- The constant E1 datum is right-continuous and has zero total variation.
Paper `e1a0fd5`, `lem:small-bv-existence`, lines 1364–1388. -/
theorem constant_smallBV_data (c : ℝ) :
    (∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt (fun _ : ℝ => c) (Ici v) v) ∧
    eVariationOn (fun _ : ℝ => c) (Ioi 0) = 0 :=
  ⟨fun _ _ => continuous_const.continuousWithinAt, flat_variation_const _ _⟩

/-- Half-gauge flat space obeys all six explicit E1 geometry bounds.
Paper `e1a0fd5`, `eq:small-bv-geometry`, lines 1369–1373. -/
theorem halfFlat_geometry (c : ℝ) : SmallBVGeometry (halfFlat c) := by
  intro p _
  norm_num [halfFlat, scaledFlat, SSFields.mu, massRatio]

/-- Both E1 variation sums vanish in half-gauge flat space.
Paper `e1a0fd5`, `lem:small-bv-existence`, line 1387,
`eq:small-bv-incoming-estimate`, lines 1375–1382. -/
theorem halfFlat_variations (c u v : ℝ) :
    smallBVOutgoingTV (halfFlat c) u = 0 ∧ smallBVIncomingTV (halfFlat c) v = 0 := by
  simp [smallBVOutgoingTV, smallBVIncomingTV, halfFlat, scaledFlat]

/-- The full E1 conclusion is realized for any constant derivative  datum c and positive epsilon and
`C₀`. Paper `e1a0fd5`, `lem:small-bv-existence`, lines 1364–1388. This proves a constant-data
instance of its conclusion, not the universal external input E1. -/
theorem halfFlat_smallBV_conclusions (c ε C₀ : ℝ) (hε : 0 < ε) (hC : 0 < C₀) :
    ∃ S : SSFields, ChristodoulouBV smallBVDomain (Ici 0) S ∧
      (∀ v > 0, S.r 0 v = v / 2 ∧ S.dvpsi 0 v = c) ∧
      SmallBVGeometry S ∧
      (∀ u ≥ 0, smallBVOutgoingTV S u < ENNReal.ofReal (C₀ * ε)) ∧
      (∀ v > 0, smallBVIncomingTV S v < ENNReal.ofReal (C₀ * ε)) := by
  refine ⟨halfFlat c,
    scaledFlat_christodoulouBV (1 / 2) (2 * c) (by norm_num) _ _
      (fun _ hp => hp.2), ?_, halfFlat_geometry c, ?_, ?_⟩
  · intro v _
    constructor <;> dsimp [halfFlat, scaledFlat] <;> ring
  · intro u _
    rw [(halfFlat_variations c u 0).1]
    exact ENNReal.ofReal_pos.mpr (mul_pos hC hε)
  · intro v _
    rw [(halfFlat_variations c 0 v).2]
    exact ENNReal.ofReal_pos.mpr (mul_pos hC hε)

/-- The small-BV input with universal positive threshold and constant, restricted to constant data:
both the E1 premises and conclusions are satisfiable. Paper `e1a0fd5`, `lem:small-bv-existence`,
lines 1364–1388. -/
theorem smallBVExistence_constant_data :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ ε ∈ Ioo 0 ε₀, ∀ c : ℝ,
        (∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt (fun _ : ℝ => c) (Ici v) v) ∧
        eVariationOn (fun _ : ℝ => c) (Ioi 0) < ENNReal.ofReal ε ∧
        ∃ S : SSFields, ChristodoulouBV smallBVDomain (Ici 0) S ∧
          (∀ v > 0, S.r 0 v = v / 2 ∧ S.dvpsi 0 v = c) ∧
          SmallBVGeometry S ∧
          (∀ u ≥ 0, smallBVOutgoingTV S u < ENNReal.ofReal (C₀ * ε)) ∧
          (∀ v > 0, smallBVIncomingTV S v < ENNReal.ofReal (C₀ * ε)) := by
  refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
  intro ε hε c
  refine ⟨(constant_smallBV_data c).1, ?_,
    halfFlat_smallBV_conclusions c ε 1 hε.1 zero_lt_one⟩
  rw [(constant_smallBV_data c).2]
  exact ENNReal.ofReal_pos.mpr hε.1

end AcExtensionPrinciple

end
