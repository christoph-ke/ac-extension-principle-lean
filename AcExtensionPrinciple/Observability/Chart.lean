module

public import AcExtensionPrinciple.Solution.PrimitiveCalculus
public import AcExtensionPrinciple.Solution.PositiveAC
public import Mathlib.Topology.TietzeExtension

/-!
# An abstract normalized observability chart

Interface for paper `e1a0fd5`, `equations.tex` lines 1451 and
1460–1473 (`eq:observability-boundary-gauge`). The seven fields are stored
in `SSFields`: `nu = r_s`, `lam = r_t`, `dupsi = ψ_s`, `dvpsi = ψ_t`.
The axis is `t = g(s)`, rather than the diagonal of the original chart.
This file does not construct the change of coordinates.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The closed solid cylinder in the normalized chart. Paper `e1a0fd5`,
`equations.tex` lines 1460–1473. Earlier incoming labels may be negative. -/
@[expose] def chartCylinder (g : ℝ → ℝ) (T : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ q.1 ≤ T ∧ g q.1 ≤ q.2 ∧ q.2 ≤ q.1}

/-- The positive-radius part of a chart domain. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1484–1492. -/
@[expose] def chartInterior (D : Set (ℝ × ℝ)) (S : SSFields) : Set (ℝ × ℝ) :=
  {q | q ∈ D ∧ 0 < S.r q.1 q.2}

/-- Characteristic integral equations inherited under the increasing coordinate
changes. Paper `e1a0fd5`, lines 1460–1473 and 1518; regularity at lines 222,
1522. Unlike `LocalBVSolutionFull.offAxis`, the axis here is not `s = t`. -/
structure ChartIntegralEquations (D : Set (ℝ × ℝ)) (S : SSFields) : Prop where
  radius_t : ∀ s a b, a ≤ b → outSeg s a b ⊆ D →
    IntervalPrimitive (S.r s) (S.lam s) a b
  radius_s : ∀ t a b, a ≤ b → inSeg t a b ⊆ D →
    IntervalPrimitive (fun s => S.r s t) (fun s => S.nu s t) a b
  psi_t : ∀ s a b, a ≤ b → outSeg s a b ⊆ D →
    IntervalPrimitive (fun t => S.r s t * S.phi s t) (S.dvpsi s) a b
  psi_s : ∀ t a b, a ≤ b → inSeg t a b ⊆ D →
    IntervalPrimitive (fun s => S.r s t * S.phi s t) (fun s => S.dupsi s t) a b
  mass_t : ∀ s a b, a ≤ b → outSeg s a b ⊆ D →
    IntervalPrimitive (S.m s) (S.massV s) a b
  mass_s : ∀ t a b, a ≤ b → inSeg t a b ⊆ D →
    IntervalPrimitive (fun s => S.m s t) (fun s => S.massU s t) a b
  lam_s : ∀ t a b, a ≤ b → inSeg t a b ⊆ chartInterior D S →
    IntervalPrimitive (fun s => S.lam s t) (fun s => S.radiusCoeff s t) a b
  nu_t : ∀ s a b, a ≤ b → outSeg s a b ⊆ chartInterior D S →
    IntervalPrimitive (S.nu s) (S.radiusCoeff s) a b
  dvpsi_s : ∀ t a b, a ≤ b → inSeg t a b ⊆ chartInterior D S →
    IntervalPrimitive (fun s => S.dvpsi s t)
      (fun s => S.radiusCoeff s t * S.phi s t) a b
  dupsi_t : ∀ s a b, a ≤ b → outSeg s a b ⊆ chartInterior D S →
    IntervalPrimitive (S.dupsi s) (fun t => S.radiusCoeff s t * S.phi s t) a b

/-- Normalized chart hypotheses, not the conclusions of Lemma A.2. Paper
`e1a0fd5`, lines 1451, 1460–1473. Continuity and uniform BV bounds are inherited
from the regular local AC/BV class at lines 220–275; the choice of a continuous
axis graph records a regular increasing chart. No boundary AC, boundary chain
rule, Volterra formula, or amplitude estimate is assumed. -/
structure NormalizedChartData (b T K : ℝ) (S : SSFields) where
  g : ℝ → ℝ
  b_pos : 0 < b
  T_nonneg : 0 ≤ T
  K_ge_one : 1 ≤ K
  continuous_g : Continuous g
  monotone_g : MonotoneOn g (Icc 0 T)
  axis_before_boundary : ∀ s ∈ Icc 0 T, g s < s
  equations : ChartIntegralEquations (chartCylinder g T) S
  continuous_r : ContinuousOn (fun q => S.r q.1 q.2) (chartCylinder g T)
  continuous_m : ContinuousOn (fun q => S.m q.1 q.2) (chartCylinder g T)
  continuous_phi : ContinuousOn (fun q => S.phi q.1 q.2) (chartCylinder g T)
  continuous_lam : ContinuousOn (fun q => S.lam q.1 q.2) (chartCylinder g T)
  continuous_nu : ContinuousOn (fun q => S.nu q.1 q.2) (chartCylinder g T)
  signs : ∀ s t, (s, t) ∈ chartCylinder g T →
    0 < S.lam s t ∧ S.nu s t < 0 ∧ 0 ≤ S.mu s t
  gap : ∀ s t, (s, t) ∈ chartCylinder g T → K⁻¹ ≤ 1 - S.mu s t
  axis_values : ∀ s ∈ Icc 0 T, S.r s (g s) = 0 ∧ S.m s (g s) = 0
  boundary_gauge : ∀ s ∈ Icc 0 T, S.r s s = b ∧ S.nu s s = -1 ∧ S.lam s s = 1
  incoming_ratio : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T →
    (s, t) ∈ chartCylinder g T → S.lam t t / S.lam s t ≤ K
  axis_reached : ∀ t ∈ Icc 0 T, t + K * b ≤ T →
    ∃ s ∈ Icc t (t + K * b), g s = t
  psi_t_variation : ∀ C, IsCompact C → C ⊆ chartCylinder g T → ∃ A : ℝ,
    ∀ s a c, a ≤ c → outSeg s a c ⊆ C →
      eVariationOn (S.dvpsi s) (Icc a c) ≤ ENNReal.ofReal A
  psi_s_variation : ∀ C, IsCompact C → C ⊆ chartCylinder g T → ∃ A : ℝ,
    ∀ t a c, a ≤ c → inSeg t a c ⊆ C →
      eVariationOn (fun s => S.dupsi s t) (Icc a c) ≤ ENNReal.ofReal A

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

/-- The outer cylinder belongs to the chart. Paper `e1a0fd5`,
`eq:observability-boundary-gauge`, lines 1460–1466. -/
theorem boundary_mem {s : ℝ} (hs : s ∈ Icc 0 T) : (s, s) ∈ chartCylinder h.g T :=
  ⟨hs.1, hs.2, (h.axis_before_boundary s hs).le, le_rfl⟩

/-- The regular axis belongs to the chart. Paper `e1a0fd5`,
`equations.tex` lines 1451, 1460–1473. -/
theorem axis_mem {s : ℝ} (hs : s ∈ Icc 0 T) : (s, h.g s) ∈ chartCylinder h.g T :=
  ⟨hs.1, hs.2, le_rfl, (h.axis_before_boundary s hs).le⟩

/-- The K-gap is strictly positive. Paper `e1a0fd5`, line 1451. -/
theorem gap_pos {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) : 0 < 1 - S.mu s t :=
  (inv_pos.mpr (by linarith [h.K_ge_one])).trans_le (h.gap s t hq)

/-- An outgoing subsegment stays in the cylinder. Paper `e1a0fd5`,
`equations.tex` lines 1460–1473. -/
theorem out_subset {s a c : ℝ} (hs : s ∈ Icc 0 T) (ha : h.g s ≤ a) (hc : c ≤ s) :
    outSeg s a c ⊆ chartCylinder h.g T := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hx
  subst x
  exact ⟨hs.1, hs.2, ha.trans hy.1, hy.2.trans hc⟩

/-- An incoming subsegment stays in the cylinder. Paper `e1a0fd5`,
`equations.tex` lines 1460–1473 and 1520. -/
theorem in_subset {t a c : ℝ} (ha : 0 ≤ a) (hc : c ≤ T)
    (ht : t ≤ a) (hg : h.g c ≤ t) : inSeg t a c ⊆ chartCylinder h.g T := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hy
  subst y
  have hxc : x ∈ Icc 0 T := ⟨ha.trans hx.1, hx.2.trans hc⟩
  have hcc : c ∈ Icc 0 T := ⟨hxc.1.trans hx.2, hc⟩
  exact ⟨hxc.1, hxc.2, (h.monotone_g hxc hcc hx.2).trans hg, ht.trans hx.1⟩

/-- Radius is the integral of the positive outgoing expansion from the axis.
Paper `e1a0fd5`, lines 1451, 1460–1473 and `eq:radius-from-axis`. -/
theorem radius_from_axis {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) :
    S.r s t = ∫ z in h.g s..t, S.lam s z := by
  have hi := (h.equations.radius_t s (h.g s) t hq.2.2.1
    (h.out_subset ⟨hq.1, hq.2.1⟩ le_rfl hq.2.2.2)).2
  simpa [(h.axis_values s ⟨hq.1, hq.2.1⟩).1] using hi

/-- Radius is positive precisely above the regular axis. Paper `e1a0fd5`,
`equations.tex` lines 1451, 1460–1473. -/
theorem radius_pos {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) (ht : h.g s < t) :
    0 < S.r s t := by
  rw [h.radius_from_axis hq]
  have hc : ContinuousOn (S.lam s) (Icc (h.g s) t) :=
    h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => h.out_subset ⟨hq.1, hq.2.1⟩ le_rfl hq.2.2.2 ⟨by simp, hz⟩)
  apply intervalIntegral.integral_pos ht hc (fun z hz =>
    (h.signs s z (h.out_subset ⟨hq.1, hq.2.1⟩ le_rfl hq.2.2.2
      ⟨by simp, hz.1.le, hz.2⟩)).1.le)
  refine ⟨t, ⟨ht.le, le_rfl⟩, (h.signs s t hq).1⟩

/-- The axis scalar amplitude is zero. Paper `e1a0fd5`,
`equations.tex` lines 1451, 1522, 1530 and `eq:regular-axis`. -/
theorem psi_axis {s : ℝ} (hs : s ∈ Icc 0 T) : S.r s (h.g s) * S.phi s (h.g s) = 0 := by
  rw [(h.axis_values s hs).1, zero_mul]

end NormalizedChartData

end AcExtensionPrinciple

end
