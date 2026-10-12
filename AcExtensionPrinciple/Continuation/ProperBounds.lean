module

public import AcExtensionPrinciple.Continuation.Domain
public import AcExtensionPrinciple.Gauge.Variation

/-!
# Uniform bounds on a proper original triangle

Original class-membership bounds, paper `e1a0fd5`, `equations.tex` lines 220–275 and 1390–1411. Q6
supplies compact bounds including v = 0. The scalar amplitudes θ,ζ are obtained from the class's
primitive derivative fields.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- The variation of a difference is at most the sum of the variations.
Paper `e1a0fd5`, lines 220–275 and 1411, component estimate for θ,ζ. -/
theorem variation_sub_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hm, hs⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [edist_eq_enorm_sub]
      convert (enorm_sub_le (a := f (u (i + 1)) - f (u i))
        (b := g (u (i + 1)) - g (u i))) using 1
      congr 1
      ring
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hm hs) (eVariationOn.sum_le hm hs)

/-- Separate variation bounds for the carried fields and amplitude bounds
give Christodoulou's θ,ζ bounds. Paper `e1a0fd5`, lines 220–275 and 1411.
In the application G,P come from continuity on the proper compact triangle;
the six TV premises come from LocalBVSolutionFull's compact segment bounds. -/
theorem chr_bounds_of_components {K D : Set (ℝ × ℝ)} {S : SSFields}
    {c N G P : ℝ} {E : ℝ≥0∞} (hc : 0 < c) (hE : E ≠ ⊤)
    (hb : ∀ p ∈ K ∩ D, c ≤ S.lam p.1 p.2 ∧ -S.nu p.1 p.2 ≤ N)
    (hamp : ∀ p ∈ K ∩ D,
      |S.lam p.1 p.2| ≤ G ∧ |S.nu p.1 p.2| ≤ G ∧ |S.phi p.1 p.2| ≤ P)
    (hout : ∀ u,
      eVariationOn (S.lam u) {v | (u, v) ∈ K ∩ D} ≤ E ∧
      eVariationOn (S.phi u) {v | (u, v) ∈ K ∩ D} ≤ E ∧
      eVariationOn (S.dvpsi u) {v | (u, v) ∈ K ∩ D} ≤ E)
    (hin : ∀ v,
      eVariationOn (fun u => S.nu u v) {u | (u, v) ∈ K ∩ D} ≤ E ∧
      eVariationOn (fun u => S.phi u v) {u | (u, v) ∈ K ∩ D} ≤ E ∧
      eVariationOn (fun u => S.dupsi u v) {u | (u, v) ∈ K ∩ D} ≤ E) :
    ChrBVBoundsOn K D S := by
  let F := E + (ENNReal.ofReal G * E + ENNReal.ofReal P * E)
  have hF : F ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hE, ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE⟩⟩
  have hEF : E ≤ F := le_self_add
  refine ⟨⟨c, N, hc, hb⟩, F.toReal, ?_, ?_⟩
  · intro u
    rw [ENNReal.ofReal_toReal hF]
    refine ⟨(hout u).1.trans hEF, (hout u).2.1.trans hEF, ?_⟩
    exact (variation_sub_le _ _ _).trans (add_le_add (hout u).2.2
      ((variation_mul_le _ _ _ (fun v hv => (hamp (u, v) hv).1)
        (fun v hv => (hamp (u, v) hv).2.2)).trans (add_le_add
          (mul_le_mul_right (hout u).2.1 _) (mul_le_mul_right (hout u).1 _))))
  · intro v
    rw [ENNReal.ofReal_toReal hF]
    refine ⟨(hin v).1.trans hEF, (hin v).2.1.trans hEF, ?_⟩
    exact (variation_sub_le _ _ _).trans (add_le_add (hin v).2.2
      ((variation_mul_le _ _ _ (fun u hu => (hamp (u, v) hu).2.1)
        (fun u hu => (hamp (u, v) hu).2.2)).trans (add_le_add
          (mul_le_mul_right (hin v).2.1 _) (mul_le_mul_right (hin v).1 _))))

/-- Q6's segment bounds control the whole outgoing portion of a proper
triangle, by enlarging it to the closed segment from the axis to v = 0.
Paper `e1a0fd5`, lines 220–275 and 1411. -/
theorem proper_triangle_out_variation {ū c C : ℝ} {f : ℝ → ℝ → ℝ}
    (h : ∀ u a b, a ≤ b → outSeg u a b ⊆ properOriginalTriangle ū c →
      eVariationOn (f u) (Icc a b) ≤ ENNReal.ofReal C) :
    ∀ u, eVariationOn (f u) {v | (u, v) ∈ properOriginalTriangle ū c} ≤
      ENNReal.ofReal C := by
  intro u
  by_cases hu : u ∈ Icc ū c
  · by_cases hu0 : u ≤ 0
    · have hs : outSeg u u 0 ⊆ properOriginalTriangle ū c := by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        simp only [mem_singleton_iff] at hx
        subst x
        exact ⟨hu, hy⟩
      exact (eVariationOn.mono _ (fun _ hv => hv.2)).trans (h u u 0 hu0 hs)
    · have he : {v | (u, v) ∈ properOriginalTriangle ū c} = ∅ := by
        ext v
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hv
        exact hu0 (hv.2.1.trans hv.2.2)
      simp [he]
  · have he : {v | (u, v) ∈ properOriginalTriangle ū c} = ∅ := by
      ext v
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun hv => hu hv.1
    simp [he]

/-- Q6's segment bounds control the whole incoming portion, including the
terminal ray v = 0. Paper `e1a0fd5`, lines 220–275 and 1411. -/
theorem proper_triangle_in_variation {ū c C : ℝ} {f : ℝ → ℝ → ℝ}
    (h : ∀ v a b, a ≤ b → inSeg v a b ⊆ properOriginalTriangle ū c →
      eVariationOn (fun u => f u v) (Icc a b) ≤ ENNReal.ofReal C) :
    ∀ v, eVariationOn (fun u => f u v) {u | (u, v) ∈ properOriginalTriangle ū c} ≤
      ENNReal.ofReal C := by
  intro v
  by_cases hv : ū ≤ min c v ∧ v ≤ 0
  · have hs : inSeg v ū (min c v) ⊆ properOriginalTriangle ū c := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      simp only [mem_singleton_iff] at hy
      subst y
      exact ⟨⟨hx.1, hx.2.trans (min_le_left _ _)⟩,
        hx.2.trans (min_le_right _ _), hv.2⟩
    have hslice : {u | (u, v) ∈ properOriginalTriangle ū c} ⊆ Icc ū (min c v) :=
      fun _ hu => ⟨hu.1.1, le_min hu.1.2 hu.2.1⟩
    exact (eVariationOn.mono _ hslice).trans
      (h v ū (min c v) hv.1 hs)
  · have he : {u | (u, v) ∈ properOriginalTriangle ū c} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hu
      exact hv ⟨le_min (hu.1.1.trans hu.1.2) (hu.1.1.trans hu.2.1), hu.2.2⟩
    simp [he]

/-- The original-chart uniform bounds, obtained from the standing class on the compact triangle {ū ≤
u ≤ c, u ≤ v ≤ 0}, c < 0. Paper `e1a0fd5`, lines 220–275 and 1411, Q6. No additional geometric
hypotheses are needed. -/
theorem StandingFull.proper_triangle_bounds {ui ū c : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ui ≤ ū) (hc : c < 0) :
    ChrBVBoundsOn univ (properOriginalTriangle ū c) S := by
  let K := properOriginalTriangle ū c
  have hK := isCompact_properOriginalTriangle ū c
  have hKD := properOriginalTriangle_subset hū hc
  rcases h.regularCenter.localBV.expansion_bounds K hK hKD with ⟨d, hd, hb⟩
  rcases h.regularCenter.localBV.expansion_variation K hK hKD with ⟨Clam, hlam, hnu⟩
  rcases h.regularCenter.localBV.scalar_ac_variation K hK hKD with ⟨Cphi, hphio, hphii⟩
  rcases h.regularCenter.localBV.psi_variation K hK hKD with ⟨Cpsi, hpsio, hpsii⟩
  rcases hK.exists_bound_of_continuousOn (h.regularCenter.continuous_lam.mono hKD)
    with ⟨L, hL⟩
  rcases hK.exists_bound_of_continuousOn (h.regularCenter.continuous_nu.mono hKD)
    with ⟨N, hN⟩
  rcases hK.exists_bound_of_continuousOn (h.regularCenter.continuous_phi.mono hKD)
    with ⟨P, hP⟩
  let E := ENNReal.ofReal Clam + ENNReal.ofReal Cphi + ENNReal.ofReal Cpsi
  have hE : E ≠ ⊤ := by simp [E]
  have hlamE : ENNReal.ofReal Clam ≤ E := le_self_add.trans le_self_add
  have hphiE : ENNReal.ofReal Cphi ≤ E := le_add_self.trans le_self_add
  have hpsiE : ENNReal.ofReal Cpsi ≤ E := le_add_self
  apply chr_bounds_of_components hd hE
    (fun p hp => hb p hp.2)
    (G := max L N) (P := P)
  · intro p hp
    exact ⟨(by simpa only [Real.norm_eq_abs] using (hL p hp.2).trans (le_max_left L N)),
      (by simpa only [Real.norm_eq_abs] using (hN p hp.2).trans (le_max_right L N)),
      (by simpa only [Real.norm_eq_abs] using hP p hp.2)⟩
  · intro u
    simp only [univ_inter]
    exact ⟨(proper_triangle_out_variation hlam u).trans hlamE,
      (proper_triangle_out_variation (fun u a b hab hs => (hphio u a b hab hs).2) u).trans hphiE,
      (proper_triangle_out_variation hpsio u).trans hpsiE⟩
  · intro v
    simp only [univ_inter]
    exact ⟨(proper_triangle_in_variation hnu v).trans hlamE,
      (proper_triangle_in_variation (fun v a b hab hs => (hphii v a b hab hs).2) v).trans hphiE,
      (proper_triangle_in_variation hpsii v).trans hpsiE⟩

end AcExtensionPrinciple

end
