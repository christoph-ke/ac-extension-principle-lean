module

public import AcExtensionPrinciple.Main.AssemblyScalar

/-!
# The primary terminal BV bounds in the original chart

Paper `e1a0fd5`, `equations.tex` lines 1431–1445. Pointwise incoming
agreement and the positive chart Jacobian transfer the E1 estimates.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Undo pointwise incoming identification in the inverse chart.
Paper `e1a0fd5`, lines 1431–1438. The Jacobian positivity is supplied by
`StandingFull.selected_chart`. -/
theorem incoming_agreement_original {S Sdev : SSFields} {T : ℝ ≃o ℝ}
    {dT : ℝ → ℝ} {u v : ℝ} (hp : 0 < dT u)
    (he : (S.pullback T.symm (inverseJacobian T dT)).nu (T u) (T v) =
        Sdev.nu (T u) (T v) ∧
      (S.pullback T.symm (inverseJacobian T dT)).dupsi (T u) (T v) =
        Sdev.dupsi (T u) (T v)) :
    S.nu u v = Sdev.nu (T u) (T v) * dT u ∧
      S.dupsi u v = Sdev.dupsi (T u) (T v) * dT u := by
  constructor
  · apply (div_eq_iff (ne_of_gt hp)).mp
    simpa [SSFields.pullback, inverseJacobian, div_eq_mul_inv] using he.1
  · apply (div_eq_iff (ne_of_gt hp)).mp
    simpa [SSFields.pullback, inverseJacobian, div_eq_mul_inv] using he.2

/-- The variation of a sum is at most the sum of the variations.
Paper `e1a0fd5`, `eq:terminal-expansion-gauge`, lines 1435–1443. -/
theorem terminal_variation_sum_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
        ≤ (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- E1 controls the normalized incoming derivative and logarithmic expansion
on the complete original terminal ray. Paper `e1a0fd5`,
`eq:terminal-bv-bound`, `eq:terminal-expansion-gauge`, lines 1431–1445. -/
theorem terminal_primary_bv_of_small_cones (hE1 : SmallBVExistence) (hE2 : BVUniqueness)
    {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
    (hcones : SmallOutgoingConesStatement ui S) :
    BoundedVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ico ui 0) ∧
      BoundedVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) := by
  obtain ⟨ū, hū, T, Sdev, _, hv, ht, _, _, hp, _, hdev, hgeom, _, _, hin, _, _, he⟩ :=
    selected_small_bv_development hE1 hE2 h hcones
  obtain ⟨c, hc, hcp⟩ := hp
  have hpos (u : ℝ) : 0 < selectedJacobian S ū u := hc.trans_le (hcp u)
  have hb : 0 < T 0 := by simpa only [hv] using T.strictMono hū.2
  obtain ⟨C, hin⟩ := hin
  have hTV := (hin (T 0) hb).le
  have hβdev : BoundedVariationOn (fun u => Sdev.dupsi u (T 0) / Sdev.nu u (T 0))
      (Ioo 0 (T 0)) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((le_self_add.trans le_self_add).trans hTV)
  have hlogdev : BoundedVariationOn (fun u => Real.log (-Sdev.nu u (T 0)))
      (Ioo 0 (T 0)) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_add_self.trans hTV)
  have hcoord (u : ℝ) (hu : u ∈ Ico ū 0) :
      S.nu u 0 = Sdev.nu (T u) (T 0) * selectedJacobian S ū u ∧
        S.dupsi u 0 = Sdev.dupsi (T u) (T 0) * selectedJacobian S ū u := by
    apply incoming_agreement_original (hpos u)
    exact he (T 0) (by rw [← ht]; exact ⟨hb, le_rfl⟩)
      (T u) ⟨by simpa only [hv] using T.monotone hu.1, T.strictMono hu.2⟩
  have himage : (T : ℝ → ℝ) '' Ioo ū 0 = Ioo 0 (T 0) := by
    simpa only [hv] using T.image_Ioo ū 0
  have hβlate : BoundedVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ioo ū 0) := by
    change eVariationOn _ _ ≠ ⊤
    rw [eVariationOn.congr (g := fun u => Sdev.dupsi (T u) (T 0) / Sdev.nu (T u) (T 0))
      (fun u hu => by
        rw [(hcoord u ⟨hu.1.le, hu.2⟩).1, (hcoord u ⟨hu.1.le, hu.2⟩).2]
        exact mul_div_mul_right _ _ (ne_of_gt (hpos u))),
      variation_comp_monotoneOn (fun u => Sdev.dupsi u (T 0) / Sdev.nu u (T 0))
        T (Ioo ū 0) (T.monotone.monotoneOn _), himage]
    exact hβdev
  have hlogcomp : BoundedVariationOn (fun u => Real.log (-Sdev.nu (T u) (T 0)))
      (Ioo ū 0) := by
    change eVariationOn _ _ ≠ ⊤
    rw [variation_comp_monotoneOn (fun u => Real.log (-Sdev.nu u (T 0)))
      T (Ioo ū 0) (T.monotone.monotoneOn _), himage]
    exact hlogdev
  have hj : EqOn (selectedJacobian S ū) (fun u => 2 * S.lam ū u) (Icc ū 0) := by
    intro u hu
    exact radialChartDerivative_on_interval hu
  have hlogj : BoundedVariationOn (fun u => Real.log (selectedJacobian S ū u))
      (Ioo ū 0) := by
    change eVariationOn _ _ ≠ ⊤
    rw [eVariationOn.congr (g := fun u => Real.log (2 * S.lam ū u))
      (fun u hu => congrArg Real.log (hj ⟨hu.1.le, hu.2.le⟩))]
    exact (h.selected_log_jacobian_bv hū).mono Ioo_subset_Icc_self
  have hloglate : BoundedVariationOn (fun u => Real.log (-S.nu u 0)) (Ioo ū 0) := by
    have hsum : BoundedVariationOn (fun u => Real.log (selectedJacobian S ū u) +
        Real.log (-Sdev.nu (T u) (T 0))) (Ioo ū 0) :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hlogj, hlogcomp⟩)
        (terminal_variation_sum_le _ _ _)
    change eVariationOn _ _ ≠ ⊤
    rw [eVariationOn.congr (g := fun u => Real.log (selectedJacobian S ū u) +
        Real.log (-Sdev.nu (T u) (T 0))) (fun u hu => by
      rw [(hcoord u ⟨hu.1.le, hu.2⟩).1, ← neg_mul]
      have hn : 0 < -Sdev.nu (T u) (T 0) := by
        have hh := hgeom (T u, T 0)
          ⟨by simpa only [hv] using (T.monotone hu.1.le), T.strictMono hu.2⟩
        linarith [hh.2.2.1]
      rw [Real.log_mul (ne_of_gt hn) (ne_of_gt (hpos u)), add_comm])]
    exact hsum
  let b := ū / 2
  have hūb : ū < b := by dsimp [b]; linarith [hū.2]
  have hb0 : b < 0 := by dsimp [b]; linarith [hū.2]
  have hs : inSeg 0 ū b ⊆ pastTriangle ui :=
    inSeg_subset_triangle hū.1.le hb0 hb0.le le_rfl
  have hnC : ContinuousWithinAt (fun u => S.nu u 0) (Ici ū) ū := by
    have hc := (h.regularCenter.localBV.nu_right_cont (ū, 0)
      (hs ⟨⟨le_rfl, hūb.le⟩, by simp⟩)).mono
      (show Icc ū b ⊆ {s | ū ≤ s ∧ (s, 0) ∈ pastTriangle ui} from
        fun s hs' => ⟨hs'.1, hs ⟨hs', by simp⟩⟩)
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hūb] using hc
  have hdC : ContinuousWithinAt (fun u => S.dupsi u 0) (Ici ū) ū := by
    have hc := (h.regularCenter.localBV.dupsi_right_cont (ū, 0)
      (hs ⟨⟨le_rfl, hūb.le⟩, by simp⟩)).mono
      (show Icc ū b ⊆ {s | ū ≤ s ∧ (s, 0) ∈ pastTriangle ui} from
        fun s hs' => ⟨hs'.1, hs ⟨hs', by simp⟩⟩)
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hūb] using hc
  have hn0 : S.nu ū 0 < 0 := h.nu_neg (p := (ū, 0)) ⟨hū.1.le, hū.2, hū.2.le, le_rfl⟩
  have hβC := hdC.div hnC (ne_of_lt hn0)
  have hlogC := hnC.neg.log (ne_of_gt (neg_pos.mpr hn0))
  change ContinuousWithinAt (fun u => S.dupsi u 0 / S.nu u 0) (Ici ū) ū at hβC
  change ContinuousWithinAt (fun u => Real.log (-S.nu u 0)) (Ici ū) ū at hlogC
  have hβclosed : BoundedVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ico ū 0) := by
    change eVariationOn _ _ ≠ ⊤
    rw [← terminal_variation_include_vertex hū.2 hβC]
    exact hβlate
  have hlogclosed : BoundedVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ū 0) := by
    change eVariationOn _ _ ≠ ⊤
    rw [← terminal_variation_include_vertex hū.2 hlogC]
    exact hloglate
  have hcompact := h.terminal_compact_bv hū
  constructor
  · change eVariationOn _ _ ≠ ⊤
    rw [terminal_variation_add _ hū]
    exact ENNReal.add_ne_top.mpr ⟨hcompact.1, hβclosed⟩
  · change eVariationOn _ _ ≠ ⊤
    rw [terminal_variation_add _ hū]
    exact ENNReal.add_ne_top.mpr ⟨hcompact.2.2.1, hlogclosed⟩

/-- All five terminal BV conclusions of Theorem 1 follow from E1, E2,
the standing class and the small-cone conclusion. Paper `e1a0fd5`, `thm:main`, lines 141–146 and
1431–1445. -/
theorem terminal_bv_of_small_cones (hE1 : SmallBVExistence) (hE2 : BVUniqueness)
    {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
    (hcones : SmallOutgoingConesStatement ui S) :
    eVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.dupsi u 0) (Ico ui 0) ≠ ⊤ := by
  obtain ⟨hβ, hlog⟩ := terminal_primary_bv_of_small_cones hE1 hE2 h hcones
  obtain ⟨hn, hd⟩ := h.terminal_derivative_bv_of_primary hβ hlog
  exact ⟨hβ, terminal_scalar_bv_of_small_cones hE1 hE2 h hcones, hlog, hn, hd⟩

end AcExtensionPrinciple

end
