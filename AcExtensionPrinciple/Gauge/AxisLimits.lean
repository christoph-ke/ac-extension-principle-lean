module

public import AcExtensionPrinciple.Gauge.RightChart

/-!
# Axis limits with explicit local boundedness

Components for paper `e1a0fd5`, `equations.tex` lines 1390–1422.
Bounded individual derivative fields prevent a continuous gauge
Jacobian from destroying cancellation. Bounds are supplied by the local BV class.
-/

public section

namespace AcExtensionPrinciple

open Filter
open scoped Topology

/-- A bounded factor times a vanishing factor vanishes. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1395. -/
theorem bounded_mul_tendsto_zero {α : Type*} {L : Filter α} {f g : α → ℝ} {C : ℝ}
    (hf : ∀ᶠ x in L, |f x| ≤ C) (hg : Tendsto g L (𝓝 0)) :
    Tendsto (fun x => f x * g x) L (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [hf] with x hx
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right hx (abs_nonneg (g x))
  · simpa using hg.abs.const_mul C

/-- Vanishing of a weighted sum is equivalent to vanishing of its unweighted
sum when the variable weight tends to a nonzero constant and the second summand
is locally bounded. Paper `e1a0fd5`, `eq:continuation-null-gauge`, 1291–1296. -/
theorem weighted_sum_zero_iff {α : Type*} {L : Filter α} {n l w : α → ℝ} {c C : ℝ}
    (hc : c ≠ 0) (hw : Tendsto w L (𝓝 c)) (hl : ∀ᶠ x in L, |l x| ≤ C) :
    Tendsto (fun x => n x * c + l x * w x) L (𝓝 0) ↔
      Tendsto (fun x => n x + l x) L (𝓝 0) := by
  have hm : Tendsto (fun x => l x * (w x - c)) L (𝓝 0) :=
    bounded_mul_tendsto_zero hl (by simpa using hw.sub_const c)
  constructor
  · intro h
    have h' := (h.sub hm).div_const c
    simp only [sub_zero, zero_div] at h'
    convert h' using 1
    ext x
    field_simp
    ring
  · intro h
    have h' := (h.mul_const c).add hm
    simp only [zero_mul, zero_add] at h'
    convert h' using 1
    ext x
    ring

/-- Expansion axis limits are equivalent along the corresponding chart points.
The outgoing expansion bound comes from local BV variation on a compact outgoing
segment. Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_expansion_axis_limit_iff {S : SSFields} {T dT : ℝ → ℝ} {a C : ℝ}
    (hd : ContinuousAt dT a) (hn : dT a ≠ 0)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |S.lam (T a) (T (a + ε))| ≤ C) :
    Tendsto (fun ε => (S.pullback T dT).nu a (a + ε) +
      (S.pullback T dT).lam a (a + ε)) (𝓝[>] 0) (𝓝 0) ↔
    Tendsto (fun ε => S.nu (T a) (T (a + ε)) +
      S.lam (T a) (T (a + ε))) (𝓝[>] 0) (𝓝 0) := by
  apply weighted_sum_zero_iff hn _ hb
  exact hd.tendsto.comp (by simpa using
    (tendsto_const_nhds.add nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ => a + ε) (𝓝[>] 0) (𝓝 (a + 0))))

/-- The scalar-derivative cancellation has the same transformation law. The
outgoing derivative bound is supplied by local BV variation on a compact segment.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_psi_axis_limit_iff {S : SSFields} {T dT : ℝ → ℝ} {a C : ℝ}
    (hd : ContinuousAt dT a) (hn : dT a ≠ 0)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |S.dvpsi (T a) (T (a + ε))| ≤ C) :
    Tendsto (fun ε => (S.pullback T dT).dupsi a (a + ε) +
      (S.pullback T dT).dvpsi a (a + ε)) (𝓝[>] 0) (𝓝 0) ↔
    Tendsto (fun ε => S.dupsi (T a) (T (a + ε)) +
      S.dvpsi (T a) (T (a + ε))) (𝓝[>] 0) (𝓝 0) := by
  apply weighted_sum_zero_iff hn _ hb
  exact hd.tendsto.comp (by simpa using
    (tendsto_const_nhds.add nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ => a + ε) (𝓝[>] 0) (𝓝 (a + 0))))

/-- Returning from corresponding chart points to the original one-sided filter
uses the local chart's equality of image filters. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1395. -/
theorem axis_limit_reparam_iff {f T : ℝ → ℝ} {a z : ℝ}
    (hmap : Filter.map (fun ε : ℝ => T (a + ε) - T a) (𝓝[>] 0) = 𝓝[>] 0) :
    Tendsto (fun ε => f (T (a + ε) - T a)) (𝓝[>] 0) (𝓝 z) ↔
      Tendsto f (𝓝[>] 0) (𝓝 z) := by
  change Tendsto (f ∘ (fun ε => T (a + ε) - T a)) _ _ ↔ _
  rw [← tendsto_map'_iff, hmap]

/-- Expansion axis-limit equivalence with the class's original displacement
parameter. The right chart premise is discharged by the positive coordinate
derivative. Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_expansion_axis_limit_full_iff {S : SSFields} {T dT : ℝ → ℝ}
    {a b C : ℝ} (hab : a < b) (hc : ContinuousOn T (Set.Icc a b))
    (hm : StrictMonoOn T (Set.Icc a b)) (hd : ContinuousAt dT a) (hn : dT a ≠ 0)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |S.lam (T a) (T (a + ε))| ≤ C) :
    Tendsto (fun ε => (S.pullback T dT).nu a (a + ε) +
      (S.pullback T dT).lam a (a + ε)) (𝓝[>] 0) (𝓝 0) ↔
    Tendsto (fun δ => S.nu (T a) (T a + δ) + S.lam (T a) (T a + δ))
      (𝓝[>] 0) (𝓝 0) := by
  rw [pullback_expansion_axis_limit_iff hd hn hb]
  have h := axis_limit_reparam_iff
    (f := fun δ => S.nu (T a) (T a + δ) + S.lam (T a) (T a + δ)) (z := 0)
    (map_axis_displacement hab hc hm)
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/-- Scalar-derivative axis-limit equivalence with the class displacement
parameter. Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_psi_axis_limit_full_iff {S : SSFields} {T dT : ℝ → ℝ}
    {a b C : ℝ} (hab : a < b) (hc : ContinuousOn T (Set.Icc a b))
    (hm : StrictMonoOn T (Set.Icc a b)) (hd : ContinuousAt dT a) (hn : dT a ≠ 0)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |S.dvpsi (T a) (T (a + ε))| ≤ C) :
    Tendsto (fun ε => (S.pullback T dT).dupsi a (a + ε) +
      (S.pullback T dT).dvpsi a (a + ε)) (𝓝[>] 0) (𝓝 0) ↔
    Tendsto (fun δ => S.dupsi (T a) (T a + δ) + S.dvpsi (T a) (T a + δ))
      (𝓝[>] 0) (𝓝 0) := by
  rw [pullback_psi_axis_limit_iff hd hn hb]
  have h := axis_limit_reparam_iff
    (f := fun δ => S.dupsi (T a) (T a + δ) + S.dvpsi (T a) (T a + δ)) (z := 0)
    (map_axis_displacement hab hc hm)
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

end AcExtensionPrinciple

end
