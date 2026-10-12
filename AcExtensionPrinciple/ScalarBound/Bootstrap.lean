module

public import AcExtensionPrinciple.ScalarBound.Transport
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Closing the strip bootstrap

Paper commit `e1a0fd5`, `equations.tex`
lines 428–439 and 514–516. A compact first-contact argument makes the
width-continuity step precise without assuming differentiability.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- A strict improvement closes a continuous bootstrap on nested strips.
The hypotheses will be supplied by the running-ray maximum, joint θ
continuity, and the strip-difference estimate. Paper `e1a0fd5`, lines 514–515. -/
theorem close_scalar_strip_bootstrap {f : ℝ → ℝ → ℝ} {a U v η L : ℝ}
    (hc : ContinuousOn (fun p => f p.1 p.2) (Icc a U ×ˢ Icc (v - η) v))
    (hzero : ∀ u ∈ Icc a U, |f u v| < L)
    (himprove : ∀ w ∈ Icc 0 η,
      (∀ u ∈ Icc a U, ∀ s ∈ Icc (v - w) v, |f u s| ≤ L) →
      ∀ u ∈ Icc a U, ∀ s ∈ Icc (v - w) v, |f u s| < L) :
    ∀ u ∈ Icc a U, ∀ s ∈ Icc (v - η) v, |f u s| < L := by
  let K := Icc a U ×ˢ Icc (v - η) v
  let B := K ∩ (fun p : ℝ × ℝ => |f p.1 p.2|) ⁻¹' Ici L
  have hBc : IsCompact B := hc.abs.upperSemicontinuousOn.isCompact_inter_preimage_Ici
    (isCompact_Icc.prod isCompact_Icc) L
  by_contra hbad
  push Not at hbad
  obtain ⟨u, hu, s, hs, hfs⟩ := hbad
  have hBn : B.Nonempty := ⟨(u, s), ⟨⟨hu, hs⟩, hfs⟩⟩
  obtain ⟨q, hq, hmax⟩ := hBc.exists_isMaxOn hBn continuous_snd.continuousOn
  have hqK : q ∈ K := hq.1
  have hqw : v - q.2 ∈ Icc 0 η := by
    constructor <;> linarith [hqK.2.1, hqK.2.2]
  have hbound : ∀ u ∈ Icc a U, ∀ s ∈ Icc (v - (v - q.2)) v,
      |f u s| ≤ L := by
    intro u hu s hs
    by_contra hgt
    have hgt : L < |f u s| := lt_of_not_ge hgt
    have hsK : s ∈ Icc (v - η) v := by
      constructor <;> linarith [hqK.2.1, hs.1, hs.2]
    have hcf : ContinuousOn (fun t => |f u t|) (Icc s v) :=
      hc.abs.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hu, ⟨hsK.1.trans ht.1, ht.2⟩⟩)
    let T := (L + |f u s|) / 2
    have hTL : L < T := by dsimp [T]; linarith
    have hTs : T < |f u s| := by dsimp [T]; linarith
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hs.2 hcf
      (show T ∈ Icc (|f u v|) (|f u s|) from
        ⟨(hzero u hu).le.trans hTL.le, hTs.le⟩)
    dsimp only at hft
    have hst : s < t := by
      apply lt_of_le_of_ne ht.1
      intro he
      subst t
      exact hTs.ne hft.symm
    have htB : (u, t) ∈ B :=
      ⟨⟨hu, ⟨hsK.1.trans ht.1, ht.2⟩⟩, by change L ≤ |f u t|; rw [hft]; exact hTL.le⟩
    have htmax : t ≤ q.2 := hmax htB
    linarith [hs.1]
  have hstrict := himprove (v - q.2) hqw hbound q.1 hqK.1 q.2
    (by constructor <;> linarith [hqK.2.2])
  exact (not_lt_of_ge hq.2) hstrict

/-- Persistence at a maximizing time, with the numerical constants in the
paper. Paper `e1a0fd5`, lines 514–516, `eq:scalar-bound-strip-difference`. -/
theorem scalar_large_value_persists {x x₀ F : ℝ} (hF : 8 < F)
    (hmax : |x₀| = F - 1) (hdiff : |x - x₀| ≤ F / 2) : F / 4 ≤ |x| := by
  have ht : |x₀| ≤ |x| + |x - x₀| := by
    calc
      |x₀| = |x + (x₀ - x)| := by congr 1; ring
      _ ≤ |x| + |x₀ - x| := abs_add_le _ _
      _ = |x| + |x - x₀| := by rw [abs_sub_comm]
  linarith

end AcExtensionPrinciple

end
