module

public import AcExtensionPrinciple.Cylinder.Geometry
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous parameter primitives on closed off-axis rectangles

Calculus helpers for paper `e1a0fd5`, lines 422–428 and 731–737.
Clamping gives a continuous extension without extending any solution equations.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A continuous rectangular field has a continuous extension by coordinate projection.
Paper `e1a0fd5`, calculus for lines 422–428 and 731–737. -/
theorem cylinder_rectangle_extension {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn (fun p => F p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    ∃ G : ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ => G p.1 p.2) ∧
      ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, G u v = F u v := by
  let G := fun u v => F (projIcc a b hab u) (projIcc c d hcd v)
  refine ⟨G, ?_, ?_⟩
  · exact hf.comp_continuous
      ((continuous_subtype_val.comp
        (continuous_projIcc (a := a) (b := b) (h := hab))).comp continuous_fst |>.prodMk
        ((continuous_subtype_val.comp
          (continuous_projIcc (a := c) (b := d) (h := hcd))).comp continuous_snd))
      (fun p => ⟨(projIcc a b hab p.1).2, (projIcc c d hcd p.2).2⟩)
  · intro u hu v hv
    simp only [G, projIcc_of_mem hab hu, projIcc_of_mem hcd hv]

/-- Continuity of a variable-upper incoming primitive on a closed rectangle.
Paper `e1a0fd5`, linear transport representation at lines 422–428. -/
theorem cylinder_rectangle_primitive_continuous {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn (fun p => F p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (fun p => ∫ s in a..p.1, F s p.2) (Icc a b ×ˢ Icc c d) := by
  obtain ⟨G, hG, he⟩ := cylinder_rectangle_extension hab hcd hf
  have hc : Continuous (fun p : ℝ × ℝ => ∫ s in a..p.1, G s p.2) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact hG.comp (continuous_snd.prodMk (continuous_fst.snd))
    · exact continuous_fst
  apply hc.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hp.1.1] at hs
  exact (he s ⟨hs.1, hs.2.trans hp.1.2⟩ p.2 hp.2).symm

/-- Continuity of a variable-upper outgoing primitive on a closed rectangle.
Paper `e1a0fd5`, off-axis ψ transport used at lines 731–737. -/
theorem cylinder_rectangle_primitive_continuous_out {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn (fun p => F p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (fun p => ∫ s in c..p.2, F p.1 s) (Icc a b ×ˢ Icc c d) := by
  have hs : ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (Icc c d ×ˢ Icc a b) :=
    hf.comp (continuous_snd.prodMk continuous_fst).continuousOn
      (fun p hp => ⟨hp.2, hp.1⟩)
  exact (cylinder_rectangle_primitive_continuous (F := fun u v => F v u) hcd hab hs).comp
    (continuous_snd.prodMk continuous_fst).continuousOn (fun p hp => ⟨hp.2, hp.1⟩)

/-- Differentiate a fixed incoming integral in the outgoing parameter.
Paper `e1a0fd5`, lines 422–428, 731–737 (off-axis transport regularity). -/
theorem cylinder_rectangle_integral_hasDerivAt {F Fv : ℝ → ℝ → ℝ} {a b c d u v : ℝ}
    (_hab : a ≤ b) (_hcd : c ≤ d) (hu : u ∈ Icc a b) (hv : v ∈ Ioo c d)
    (hf : ContinuousOn (fun p => F p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hf' : ContinuousOn (fun p => Fv p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hd : ∀ s ∈ Icc a b, ∀ t ∈ Ioo c d, HasDerivAt (F s) (Fv s t) t) :
    HasDerivAt (fun t => ∫ s in a..u, F s t) (∫ s in a..u, Fv s v) v := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf'
  have hs (t : ℝ) (ht : t ∈ Icc c d) : ContinuousOn (fun s => F s t) (Icc a u) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨⟨hs.1, hs.2.trans hu.2⟩, ht⟩)
  have hs' : ContinuousOn (fun s => Fv s v) (Icc a u) :=
    hf'.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨⟨hs.1, hs.2.trans hu.2⟩, ⟨hv.1.le, hv.2.le⟩⟩)
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a u)) (F := fun t s => F s t)
    (F' := fun t s => Fv s t) (bound := fun _ => C) (Ioo_mem_nhds hv.1 hv.2)
    ((show ∀ᶠ t in 𝓝 v, t ∈ Ioo c d from Ioo_mem_nhds hv.1 hv.2).mono (fun t ht =>
      (hs _ (Ioo_subset_Icc_self ht)).aestronglyMeasurable measurableSet_Icc |>.mono_set
        Ioc_subset_Icc_self))
    ((hs v (Ioo_subset_Icc_self hv)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hs'.aestronglyMeasurable measurableSet_Icc |>.mono_set Ioc_subset_Icc_self)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs t ht
        exact hC (s, t) ⟨⟨hs.1.le, hs.2.trans hu.2⟩, Ioo_subset_Icc_self ht⟩)
    (integrable_const C)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs t ht
        exact hd s ⟨hs.1.le, hs.2.trans hu.2⟩ t ht)
  simpa only [intervalIntegral.integral_of_le hu.1] using hder.2

end AcExtensionPrinciple

end
