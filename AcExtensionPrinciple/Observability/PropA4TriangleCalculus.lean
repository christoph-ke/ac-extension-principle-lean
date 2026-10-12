module

public import AcExtensionPrinciple.Observability.VolterraBounds
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Differentiating the lower limit of a triangular integral

Paper `e1a0fd5`, lines 1755–1759. Fubini's theorem reverses the
triangle, reducing differentiation of its lower limit to the ordinary
fundamental theorem of calculus for a continuous integrand.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Reverse integration over the characteristic triangle for a continuous
kernel. Paper `e1a0fd5`, lines 1755–1759. -/
theorem triangular_integral_reverse {F : ℝ × ℝ → ℝ} {s t : ℝ}
    (hF : Continuous F) (hts : t ≤ s) :
    (∫ σ in t..s, ∫ z in t..σ, F (σ, z)) =
      ∫ z in t..s, ∫ σ in z..s, F (σ, z) := by
  let G := fun σ z : ℝ => if z < σ then F (σ, z) else 0
  have hInt : IntegrableOn G.uncurry (uIoc t s ×ˢ uIoc t s) := by
    have hi : IntegrableOn F (Icc t s ×ˢ Icc t s) :=
      hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hj : IntegrableOn F (uIoc t s ×ˢ uIoc t s) := hi.mono_set (by
      rw [uIoc_of_le hts]
      exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    have hm : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
      measurableSet_lt measurable_snd measurable_fst
    exact hj.indicator hm
  have hout (σ : ℝ) (hσ : σ ∈ Icc t s) :
      (∫ z in t..s, G σ z) = ∫ z in t..σ, F (σ, z) := by
    have he : G σ = (Iio σ).indicator (fun z => F (σ, z)) := by
      funext z
      simp [G, indicator]
    rw [he, intervalIntegral.integral_of_le hts, setIntegral_indicator measurableSet_Iio]
    have hset : Ioc t s ∩ Iio σ = Ioo t σ := by
      ext z
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨hz, _⟩, hzσ⟩; exact ⟨hz, hzσ⟩
      · rintro ⟨hz, hzσ⟩; exact ⟨⟨hz, hzσ.le.trans hσ.2⟩, hzσ⟩
    rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hσ.1]
  have hin (z : ℝ) (hz : z ∈ Icc t s) :
      (∫ σ in t..s, G σ z) = ∫ σ in z..s, F (σ, z) := by
    have he : (fun σ => G σ z) = (Ioi z).indicator (fun σ => F (σ, z)) := by
      funext σ
      simp [G, indicator]
    rw [he, intervalIntegral.integral_of_le hts, setIntegral_indicator measurableSet_Ioi]
    have hset : Ioc t s ∩ Ioi z = Ioc z s := by
      ext σ
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨_, hσ⟩, hzσ⟩; exact ⟨hzσ, hσ⟩
      · rintro ⟨hzσ, hσ⟩; exact ⟨⟨hz.1.trans_lt hzσ, hσ⟩, hzσ⟩
    rw [hset, ← intervalIntegral.integral_of_le hz.2]
  calc
    _ = ∫ σ in t..s, ∫ z in t..s, G σ z := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      rw [uIcc_of_le hts] at hσ
      exact (hout σ hσ).symm
    _ = ∫ z in t..s, ∫ σ in t..s, G σ z := intervalIntegral_intervalIntegral_swap hInt
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le hts] at hz
      exact hin z hz

/-- Differentiate the triangular integral in its lower endpoint, within
`t ≤ s`. Paper `e1a0fd5`, lines 1755–1759. -/
theorem triangular_integral_hasDerivWithinAt_t {F : ℝ × ℝ → ℝ} {s t : ℝ}
    (hF : Continuous F) (hts : t ≤ s) :
    HasDerivWithinAt (fun x => ∫ σ in x..s, ∫ z in x..σ, F (σ, z))
      (-(∫ σ in t..s, F (σ, t))) (Iic s) t := by
  let J := fun z => ∫ σ in z..s, F (σ, z)
  have hJc : Continuous J :=
    continuous_moving_interval_integral (f := fun z σ : ℝ => F (σ, z))
      (hF.comp (continuous_snd.prodMk continuous_fst)) continuous_id continuous_const
  have hd := intervalIntegral.integral_hasDerivAt_left (hJc.intervalIntegrable t s)
    hJc.aestronglyMeasurable.stronglyMeasurableAtFilter hJc.continuousAt
  exact hd.hasDerivWithinAt.congr_of_mem
    (fun x hx => triangular_integral_reverse hF hx) hts

end PropA4
end AcExtensionPrinciple

end
