module

public import AcExtensionPrinciple.Solution.PrimitiveCalculus
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Parameter calculus on compact off-axis rectangles

Internal analytic components for paper `e1a0fd5`, `equations.tex`
lines 422–426 and 594–601. Continuity and a continuous parameter derivative
justify incoming integrals and their outgoing derivatives.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- An incoming integral with a variable upper limit is continuous on a
compact rectangle. Paper `e1a0fd5`, lines 422–426. -/
theorem rectangle_integral_continuous {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in a..p.1, F s p.2) (Icc a b ×ˢ Icc c d) := by
  let E : ℝ → ℝ → ℝ := fun s v => F (projIcc a b hab s) (projIcc c d hcd v)
  have he : Continuous (fun p : ℝ × ℝ => E p.1 p.2) := by
    have hpa : Continuous (fun p : ℝ × ℝ => (projIcc a b hab p.1 : ℝ)) :=
      ((continuous_projIcc (h := hab)).comp continuous_fst).subtype_val
    have hpc : Continuous (fun p : ℝ × ℝ => (projIcc c d hcd p.2 : ℝ)) :=
      ((continuous_projIcc (h := hcd)).comp continuous_snd).subtype_val
    apply continuousOn_univ.mp
    exact hf.comp (hpa.prodMk hpc).continuousOn
      (fun p _ => ⟨(projIcc a b hab p.1).property, (projIcc c d hcd p.2).property⟩)
  have he' : Continuous (fun p : (ℝ × ℝ) × ℝ => E p.2 p.1.2) :=
    he.comp (continuous_snd.prodMk continuous_fst.snd)
  have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := a) (f := fun (p : ℝ × ℝ) s => E s p.2)
    (s := fun p => p.1) he' continuous_fst
  apply hh.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hp.1.1] at hs
  have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans hp.1.2⟩
  dsimp [E]
  rw [projIcc_of_mem hab hs', projIcc_of_mem hcd hp.2]

/-- A continuous outgoing derivative can be passed through each proper
incoming integral. Paper `e1a0fd5`, lines 594–601. -/
theorem rectangle_integral_hasDerivAt {F D : ℝ → ℝ → ℝ} {a b c d u v : ℝ}
    (hu : u ∈ Icc a b) (hv : v ∈ Ioo c d)
    (hf : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hd : ∀ s ∈ Icc a b, ∀ x ∈ Ioo c d, HasDerivAt (F s) (D s x) x) :
    HasDerivAt (fun x => ∫ s in a..u, F s x) (∫ s in a..u, D s v) v := by
  have hslice (x : ℝ) (hx : x ∈ Icc c d) : ContinuousOn (fun s => F s x) (Icc a u) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨⟨hs.1, hs.2.trans hu.2⟩, hx⟩)
  have hDslice : ContinuousOn (fun s => D s v) (Icc a u) :=
    hD.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨⟨hs.1, hs.2.trans hu.2⟩, Ioo_subset_Icc_self hv⟩)
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hD.norm
  have hK' : ∀ s ∈ Icc a u, ∀ x ∈ Ioo c d, ‖D s x‖ ≤ K := by
    intro s hs x hx
    exact hK ⟨(s, x), ⟨⟨hs.1, hs.2.trans hu.2⟩, Ioo_subset_Icc_self hx⟩, rfl⟩
  have hmeas : ∀ᶠ x in 𝓝 v, AEStronglyMeasurable (fun s => F s x)
      (volume.restrict (Icc a u)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with x hx
    exact (hslice x (Ioo_subset_Icc_self hx)).aestronglyMeasurable measurableSet_Icc
  have hint : IntegrableOn (fun s => F s v) (Icc a u) volume :=
    (hslice v (Ioo_subset_Icc_self hv)).integrableOn_Icc
  have hbound : ∀ᵐ s ∂volume.restrict (Icc a u), ∀ x ∈ Ioo c d, ‖D s x‖ ≤ K :=
    (ae_restrict_mem measurableSet_Icc).mono (fun s hs => hK' s hs)
  have hdiff : ∀ᵐ s ∂volume.restrict (Icc a u), ∀ x ∈ Ioo c d,
      HasDerivAt (fun x => F s x) (D s x) x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hd s ⟨hs.1, hs.2.trans hu.2⟩
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc a u)) (bound := fun _ => K)
    (Ioo_mem_nhds hv.1 hv.2) hmeas hint
    (hDslice.aestronglyMeasurable measurableSet_Icc) hbound
    (integrableOn_const isCompact_Icc.measure_ne_top) hdiff).2
  simpa only [intervalIntegral.integral_of_le hu.1,
    ← integral_Icc_eq_integral_Ioc] using hh

/-- A prescribed continuous derivative on a closed interval gives AC.
Paper `e1a0fd5`, lines 222 and 594–601. -/
theorem ac_of_continuous_hasDerivAt {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x) :
    AbsolutelyContinuousOnInterval f a b := by
  apply intervalPrimitive_ac (g := g) hab
  intro x hx
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hi : IntervalIntegrable g volume a x := (hg.mono hsub).intervalIntegrable_of_Icc hx.1
  refine ⟨hi, ?_⟩
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y (hsub (by simpa only [uIcc_of_le hx.1] using hy))) hi).symm

end AcExtensionPrinciple

end
