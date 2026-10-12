module

public import AcExtensionPrinciple.Main.Statement
public import AcExtensionPrinciple.Solution.FullReduction

/-!
# Flat solutions for class sanity checks

Checks against paper `e1a0fd5`, `equations.tex` lines 49–106,
220–275 and `lem:small-bv-existence`. The scale q describes the two
initial radius gauges; c is the scalar value, not the derivative datum.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Minkowski fields with radius q(v-u) and constant scalar c.
Paper `e1a0fd5`, lines 49–106, `eq:initial-radius-gauge`, `lem:small-bv-existence`. -/
@[expose] noncomputable def scaledFlat (q c : ℝ) : SSFields where
  r u v := q * (v - u)
  phi _ _ := c
  m _ _ := 0
  lam _ _ := q
  nu _ _ := -q
  dvpsi _ _ := q * c
  dupsi _ _ := -q * c

/-- Constant functions have zero variation on any set, including the four
axis families. Paper `e1a0fd5`, line 222, Luk–Oh Def. 2.1(5). -/
@[simp] theorem flat_variation_const (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun _ : ℝ => c) s = 0 := by
  apply eVariationOn.constant_on
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rfl

/-- Constant scalar and expansion traces are AC. Paper `e1a0fd5`,
lines 220–275 and `eq:initial-ac-data`. -/
theorem flat_ac_const (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
  simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
  exact tendsto_const_nhds

/-- All nonlinear sources vanish in the flat family, even on the axis.
Paper `e1a0fd5`, `eq:radius`, `eq:mass`, lines 49–106. -/
@[simp] theorem scaledFlat_sources (q c u v : ℝ) :
    (scaledFlat q c).mu u v = 0 ∧ (scaledFlat q c).theta u v = 0 ∧
    (scaledFlat q c).zeta u v = 0 ∧ (scaledFlat q c).radiusCoeff u v = 0 ∧
    (scaledFlat q c).massV u v = 0 ∧ (scaledFlat q c).massU u v = 0 := by
  simp [scaledFlat, SSFields.mu, massRatio, SSFields.theta, SSFields.zeta,
    SSFields.radiusCoeff, SSFields.massV, SSFields.massU]

/-- The flat family satisfies every clause of the full local BV class on any
specified domain. Paper `e1a0fd5`, lines 66–84, 220–275, Luk–Oh Def. 2.1. -/
theorem scaledFlat_localBV_full (q c : ℝ) (hq : 0 < q) (D : Set (ℝ × ℝ)) :
    LocalBVSolutionFull D (scaledFlat q c) := by
  have hbounds : ∃ d : ℝ, 0 < d ∧ d ≤ q ∧ q ≤ 1 / d := by
    refine ⟨min q (1 / q), lt_min hq (one_div_pos.mpr hq), min_le_left _ _, ?_⟩
    apply (le_div_iff₀ (lt_min hq (one_div_pos.mpr hq))).2
    calc
      q * min q (1 / q) ≤ q * (1 / q) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hq.le
      _ = 1 := by field_simp
  constructor
  · intro u a b _ _
    refine ⟨intervalIntegrable_const, ?_⟩
    simp [scaledFlat]
    ring
  · intro v a b _ _
    refine ⟨intervalIntegrable_const, ?_⟩
    simp [scaledFlat]
    ring
  · intro u a b _ _
    refine ⟨intervalIntegrable_const, ?_⟩
    simp [scaledFlat]
    ring
  · intro v a b _ _
    refine ⟨intervalIntegrable_const, ?_⟩
    simp [scaledFlat]
    ring
  · intro u a b _ _
    change IntervalPrimitive (fun _ => (0 : ℝ))
      (fun v => (scaledFlat q c).massV u v) a b
    simp [IntervalPrimitive, scaledFlat, SSFields.massV, SSFields.mu, massRatio,
      SSFields.theta, intervalIntegrable_const]
  · intro v a b _ _
    simp [IntervalPrimitive, scaledFlat, SSFields.massU, SSFields.mu, massRatio,
      SSFields.zeta, intervalIntegrable_const]
  · intro v a b _ _
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro u a b _ _
    change IntervalPrimitive (fun _ => -q)
      (fun v => (scaledFlat q c).radiusCoeff u v) a b
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro v a b _ _
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro u a b _ _
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro K _ _
    obtain ⟨d, hd, hdq, hqd⟩ := hbounds
    exact ⟨d, hd, fun _ _ => ⟨hdq, by simpa [scaledFlat] using hqd⟩⟩
  · intro K _ _
    refine ⟨0, ?_, ?_⟩ <;> intros <;> simp [scaledFlat]
  · intro a _
    simp [scaledFlat]
  · intro K _ _
    refine ⟨0, ?_, ?_⟩ <;> intro x a b _ _ <;>
      exact ⟨flat_ac_const c a b, by simp [scaledFlat]⟩
  · intro a _
    constructor <;> simp [scaledFlat]
  · intro K _ _
    refine ⟨0, ?_, ?_⟩ <;> intros <;> simp [scaledFlat]
  · intro a _
    simp [scaledFlat]
  · intro a _
    simp [scaledFlat]
  · intro p _
    exact continuousWithinAt_const
  · intro p _
    exact continuousWithinAt_const
  · intro p _
    exact continuousWithinAt_const
  · intro p _
    exact continuousWithinAt_const

/-- The flat family satisfies Christodoulou's core, with arbitrary axis
parameters and any off-axis domain. Paper `e1a0fd5`, lines 220–275,
`lem:small-bv-existence`; Christodoulou pp. 1146–1147. -/
theorem scaledFlat_chrCore (q c : ℝ) (hq : 0 < q)
    (D : Set (ℝ × ℝ)) (A : Set ℝ) (hD : D ⊆ {p | p.1 < p.2}) :
    ChrBVCore D A (scaledFlat q c) := by
  have h := scaledFlat_localBV_full q c hq D
  refine ⟨hD, h.radius_out, h.radius_in, h.psi_out, h.psi_in,
    h.mass_out, h.mass_in, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.lam_right_cont, ?_, h.nu_right_cont, ?_⟩
  · intro v a b _ _
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro u a b _ _
    change IntervalPrimitive (fun _ => -q)
      (fun v => (scaledFlat q c).radiusCoeff u v) a b
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro v a b _ _
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro u a b _ _
    simp [IntervalPrimitive, scaledFlat, SSFields.radiusCoeff, SSFields.mu, massRatio,
      intervalIntegrable_const]
  · intro u a b _ _
    exact flat_ac_const c a b
  · intro v a b _ _
    exact flat_ac_const c a b
  · intro a _
    have ht : Tendsto (fun v : ℝ => q * (v - a)) (𝓝 a) (𝓝 (q * (a - a))) :=
      (continuous_const.mul (continuous_id.sub continuous_const)).tendsto a
    simpa [scaledFlat] using ht.mono_left
      (inf_le_left.trans nhdsWithin_le_nhds)
  · intro a _
    exact tendsto_const_nhds
  · intro a _
    simpa [scaledFlat] using (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ)) _ (𝓝 0))
  · intro a _
    constructor <;> simp [scaledFlat]
  · intro a _
    simpa [scaledFlat] using (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℝ)) _ (𝓝 0))
  · intro p _
    change ContinuousWithinAt (fun _ : ℝ => q * c - q * c) _ _
    exact continuousWithinAt_const
  · intro p _
    change ContinuousWithinAt (fun _ : ℝ => -q * c - -q * c) _ _
    exact continuousWithinAt_const

/-- All characteristic portions have globally uniform zero variation in
flat space. Paper `e1a0fd5`, lines 220–275; Christodoulou items 1, 3, 5. -/
theorem scaledFlat_chrBounds (q c : ℝ) (hq : 0 < q) (K D : Set (ℝ × ℝ)) :
    ChrBVBoundsOn K D (scaledFlat q c) := by
  refine ⟨⟨q, q, hq, ?_⟩, ⟨0, ?_, ?_⟩⟩
  · intro p _
    simp [scaledFlat]
  · intro u
    have htheta : (scaledFlat q c).theta u = fun _ => 0 := by
      funext v
      exact (scaledFlat_sources q c u v).2.1
    rw [htheta]
    simp [scaledFlat]
  · intro v
    simp [scaledFlat, SSFields.zeta]

/-- Flat space belongs to the globally uniform Christodoulou class on any
 off-axis domain. Paper `e1a0fd5`, `lem:small-bv-existence`, lines 220–275. -/
theorem scaledFlat_christodoulouBV (q c : ℝ) (hq : 0 < q)
    (D : Set (ℝ × ℝ)) (A : Set ℝ) (hD : D ⊆ {p | p.1 < p.2}) :
    ChristodoulouBV D A (scaledFlat q c) :=
  ⟨scaledFlat_chrCore q c hq D A hD, scaledFlat_chrBounds q c hq univ D⟩

/-- Flat solutions belong to the minimal local BV source class on every domain.
Paper `e1a0fd5`, lines 66–84 and 220–275. -/
theorem scaledFlat_localBV (q c : ℝ) (hq : 0 < q) (D : Set (ℝ × ℝ)) :
    LocalBVSolution D (scaledFlat q c) :=
  (scaledFlat_localBV_full q c hq D).toMinimal

end AcExtensionPrinciple

end
