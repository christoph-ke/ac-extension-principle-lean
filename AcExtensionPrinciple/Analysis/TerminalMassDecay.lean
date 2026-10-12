module

public import AcExtensionPrinciple.Reduced.Quantities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

/-!
# Terminal mass-ratio decay from a finite incoming blueshift integral

Internal helpers for paper commit `e1a0fd5`, `equations.tex`
lines 848–857 (`eq:terminal-radial-blueshift`, `eq:terminal-mass-decay`).
The annular estimate and absolute continuity of the nonnegative integral avoid
having to extract a disjoint subsequence of annuli.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A constant lower bound on an outward annulus; paper `e1a0fd5`,
`equations.tex` lines 848–857 (`eq:terminal-radial-blueshift`). -/
theorem annular_blueshift_lower_bound {R r : ℝ} {m : ℝ → ℝ}
    (hr : 0 < r) (h2r : 2 * r ≤ R) (hm : MonotoneOn m (Ioc 0 R))
    (hm0 : ∀ s ∈ Ioc 0 R, 0 ≤ m s) (hmu : ∀ s ∈ Ioc 0 R, 2 * m s < s) :
    ENNReal.ofReal (massRatio r (m r) / 4) ≤
      ∫⁻ s in Ioc r (2 * r),
        ENNReal.ofReal (massRatio s (m s) / ((1 - massRatio s (m s)) * s)) := by
  have hrR : r ∈ Ioc 0 R := ⟨hr, by linarith⟩
  have hpoint (s : ℝ) (hs : s ∈ Ioc r (2 * r)) :
      massRatio r (m r) / (4 * r) ≤
        massRatio s (m s) / ((1 - massRatio s (m s)) * s) := by
    have hsR : s ∈ Ioc 0 R := ⟨lt_trans hr hs.1, hs.2.trans h2r⟩
    have hs0 : 0 < s := hsR.1
    have hms : m r ≤ m s := hm hrR hsR hs.1.le
    have hms0 := hm0 s hsR
    have hmus0 : 0 ≤ massRatio s (m s) := by unfold massRatio; positivity
    have hmus1 : massRatio s (m s) < 1 := by
      unfold massRatio
      exact (div_lt_one hs0).mpr (hmu s hsR)
    have hden : 0 < (1 - massRatio s (m s)) * s := by positivity
    have hdenle : (1 - massRatio s (m s)) * s ≤ s := by nlinarith
    calc
      massRatio r (m r) / (4 * r) ≤ massRatio s (m s) / s := by
        unfold massRatio
        rw [div_div, div_div]
        apply (div_le_div_iff₀ (by positivity : 0 < r * (4 * r))
          (by positivity : 0 < s * s)).mpr
        have hss : s ^ 2 ≤ 4 * r ^ 2 := by nlinarith [hs.2]
        nlinarith [mul_nonneg (hm0 r hrR) (sub_nonneg.mpr hss),
          mul_nonneg (sub_nonneg.mpr hms) (sq_nonneg r)]
      _ ≤ _ := div_le_div_of_nonneg_left hmus0 hden hdenle
  have hle := setLIntegral_mono' (μ := volume) measurableSet_Ioc
    (fun s hs ↦ ENNReal.ofReal_le_ofReal (hpoint s hs))
  have hmr0 := hm0 r hrR
  have hconstant : 0 ≤ massRatio r (m r) / (4 * r) := by unfold massRatio; positivity
  rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hconstant] at hle
  have heq : massRatio r (m r) / (4 * r) * (2 * r - r) =
      massRatio r (m r) / 4 := by field_simp; ring
  rwa [heq] at hle

/-- Finite incoming blueshift forces terminal mass-ratio decay; paper `e1a0fd5`,
`equations.tex` lines 848–857 (`eq:terminal-mass-decay`). No additional
measurability assumption is needed. -/
theorem tendsto_massRatio_zero_of_lintegral_finite {R : ℝ} {m : ℝ → ℝ}
    (hR : 0 < R) (hm : MonotoneOn m (Ioc 0 R))
    (hm0 : ∀ r ∈ Ioc 0 R, 0 ≤ m r) (hmu : ∀ r ∈ Ioc 0 R, 2 * m r < r)
    (hfin : (∫⁻ r in Ioc 0 R,
      ENNReal.ofReal (massRatio r (m r) / ((1 - massRatio r (m r)) * r))) < ∞) :
    Tendsto (fun r ↦ massRatio r (m r)) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hvol : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (2 * r - r)) (𝓝[>] 0) (𝓝 0) := by
    have hlin : Tendsto (fun r : ℝ ↦ 2 * r - r) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero, sub_zero] using (hid.const_mul 2).sub hid
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hlin
  have hrestricted : Tendsto
      (fun r : ℝ ↦ (volume.restrict (Ioc 0 R)) (Ioc r (2 * r))) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol
      (fun r ↦ (bot_le : (0 : ℝ≥0∞) ≤ _))
    intro r
    exact (Measure.restrict_le_self _).trans_eq Real.volume_Ioc
  have hsmall := tendsto_setLIntegral_zero (ne_of_lt hfin) hrestricted
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds hR)] with r hr hrR
    have hmr := hm0 r ⟨hr, hrR.le⟩
    have hr0 : 0 < r := hr
    have hnonneg : 0 ≤ massRatio r (m r) := by unfold massRatio; positivity
    exact ha.trans_le hnonneg
  · intro eps heps
    have he : 0 < ENNReal.ofReal (eps / 4) := by positivity
    filter_upwards [self_mem_nhdsWithin,
      hid.eventually (gt_mem_nhds (show 0 < R / 2 by positivity)),
      hsmall.eventually (gt_mem_nhds he)] with r hr hrR hri
    have h2r : 2 * r ≤ R := by linarith
    have hsub : Ioc r (2 * r) ⊆ Ioc 0 R := fun s hs ↦
      ⟨lt_trans hr hs.1, hs.2.trans h2r⟩
    rw [Measure.restrict_restrict_of_subset hsub] at hri
    have hbound := (annular_blueshift_lower_bound hr h2r hm hm0 hmu).trans_lt hri
    have hlt := (ENNReal.ofReal_lt_ofReal_iff (show 0 < eps / 4 by positivity)).mp hbound
    linarith

end AcExtensionPrinciple

end
