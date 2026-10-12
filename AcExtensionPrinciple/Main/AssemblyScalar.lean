module

public import AcExtensionPrinciple.Main.AssemblyExistence
public import AcExtensionPrinciple.Main.AssemblyTerminal

/-!
# The complete terminal scalar variation bound

Paper `e1a0fd5`, `equations.tex` `eq:terminal-bv-bound`, lines 1431–1443.
Pointwise uniqueness of φ suffices for this part of the terminal estimate;
no convention for derivative representatives is needed.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Adding a continuous left endpoint to a punctured interval leaves its
variation unchanged. Paper `e1a0fd5`, lines 1431–1443. -/
theorem terminal_variation_include_vertex {f : ℝ → ℝ} {a : ℝ} (ha : a < 0)
    (hc : ContinuousWithinAt f (Ici a) a) :
    eVariationOn f (Ioo a 0) = eVariationOn f (Ico a 0) := by
  have hnb : (𝓝[Iio (0 : ℝ) ∩ Ioi a] a).NeBot := by
    rw [nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ha))]
    infer_instance
  have he := eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    (s := Iio (0 : ℝ)) hnb (hc.mono inter_subset_right)
  have h₁ : Iio (0 : ℝ) ∩ Ioi a = Ioo a 0 := by ext x; simp [and_comm]
  have h₂ : Iio (0 : ℝ) ∩ Ici a = Ico a 0 := by ext x; simp [and_comm]
  simpa only [h₁, h₂] using he

/-- The φ term of the main terminal BV conclusion follows fully from
E1, E2, the standing assumptions and the small-cone premise.
Paper `e1a0fd5`, `eq:terminal-bv-bound`, lines 1431–1443. -/
theorem terminal_scalar_bv_of_small_cones (hE1 : SmallBVExistence) (hE2 : BVUniqueness)
    {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
    (hcones : SmallOutgoingConesStatement ui S) :
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) ≠ ⊤ := by
  obtain ⟨ū, hū, T, Sdev, _, hv, ht, _, _, _, _, _, _, _, _, hin, he, _⟩ :=
    selected_small_bv_development hE1 hE2 h hcones
  rcases hin with ⟨C, hin⟩
  have hb : 0 < T 0 := by simpa only [hv] using T.strictMono hū.2
  have hdevTV : eVariationOn (fun u => Sdev.phi u (T 0)) (Ioo 0 (T 0)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (le_add_self.trans le_self_add).trans (hin (T 0) hb).le
  have hlate : eVariationOn (fun u => S.phi u 0) (Ioo ū 0) ≠ ⊤ := by
    rw [eVariationOn.congr (g := fun u => Sdev.phi (T u) (T 0))
      (fun u hu => (he u 0 hu.1.le hu.2 le_rfl).2.1)]
    have himage : (T : ℝ → ℝ) '' Ioo ū 0 = Ioo 0 (T 0) := by
      simpa only [hv] using T.image_Ioo ū 0
    rw [variation_comp_monotoneOn (fun u => Sdev.phi u (T 0)) T
      (Ioo ū 0) (T.monotone.monotoneOn _), himage]
    exact hdevTV
  have hmid : ū < ū / 2 ∧ ū / 2 < 0 := by constructor <;> linarith [hū.2]
  have hs : inSeg 0 ū (ū / 2) ⊆ pastTriangle ui :=
    inSeg_subset_triangle hū.1.le hmid.2 hmid.2.le le_rfl
  have hc := StandingFull.continuous_in h.regularCenter.continuous_phi hs
    ū ⟨le_rfl, hmid.1.le⟩
  have hcGE : ContinuousWithinAt (fun u => S.phi u 0) (Ici ū) ū := by
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hmid.1] using hc
  have hlateClosed : eVariationOn (fun u => S.phi u 0) (Ico ū 0) ≠ ⊤ := by
    rw [← terminal_variation_include_vertex hū.2 hcGE]
    exact hlate
  rw [terminal_variation_add _ hū]
  exact ENNReal.add_ne_top.mpr ⟨(h.terminal_compact_bv hū).2.1, hlateClosed⟩

end AcExtensionPrinciple

end
