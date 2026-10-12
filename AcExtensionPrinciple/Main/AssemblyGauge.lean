module

public import AcExtensionPrinciple.Main.AssemblyDevelopmentBounds

/-!
# The pulled-back development in the Christodoulou class

Paper `e1a0fd5`, `equations.tex` lines 1411–1422. The selected Jacobian is
positive, globally bounded and BV. The E1 bounds and compact amplitudes
supply its gauge core and the compactly localized variation bounds.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The continuation region occupied by the pulled-back E1 solution.
Paper `e1a0fd5`, `thm:main`, line 133 and lines 1411–1422. -/
@[expose] def lateContinuationDomain (ū : ℝ) : Set (ℝ × ℝ) :=
  {p | ū ≤ p.1 ∧ p.1 < p.2}

/-- The constant extensions retain global Jacobian BV and a uniform amplitude
bound. Paper `e1a0fd5`, `eq:continuation-null-gauge`, line 1422. -/
theorem selected_jacobian_global {S : SSFields} {ū : ℝ} (hū : ū < 0)
    (hc : Continuous (selectedJacobian S ū))
    (hv : BoundedVariationOn (selectedJacobian S ū) (Icc ū 0)) :
    BoundedVariationOn (selectedJacobian S ū) univ ∧
      ∃ J : ℝ, 0 ≤ J ∧ ∀ x, |selectedJacobian S ū x| ≤ J := by
  let U := fun x : ℝ => max ū (min x 0)
  have hmem (x : ℝ) : U x ∈ Icc ū 0 := ⟨le_max_left _ _, max_le hū.le (min_le_right _ _)⟩
  have he (x : ℝ) : selectedJacobian S ū (U x) = selectedJacobian S ū x := by
    simp only [selectedJacobian, radialChartDerivative_on_interval (hmem x)]
    rfl
  have hm : Monotone U := monotone_const.max (monotone_id.min monotone_const)
  constructor
  · change eVariationOn _ _ ≠ ⊤
    rw [← eVariationOn.congr (f := fun x => selectedJacobian S ū (U x))
      (fun x _ => he x), variation_comp_monotoneOn _ U univ (hm.monotoneOn _)]
    exact hv.mono (image_subset_iff.mpr (fun x _ => hmem x))
  · obtain ⟨J, hJ⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hc.continuousOn : ContinuousOn (selectedJacobian S ū) (Icc ū 0))
    refine ⟨max 0 J, le_max_left _ _, fun x => ?_⟩
    have hh : |selectedJacobian S ū (U x)| ≤ J := by
      simpa only [Real.norm_eq_abs] using hJ _ (hmem x)
    rw [he] at hh
    exact hh.trans (le_max_right _ _)

/-- Uniform Christodoulou variation and amplitude bounds also control the
raw ψ derivatives needed by gauge transport. Paper `e1a0fd5`, lines 222
and 1411–1422. The scalar-product bounds use the explicit amplitude premise. -/
theorem raw_variation_of_chr {D : Set (ℝ × ℝ)} {S : SSFields} {M : ℝ}
    (h : ChrBVBoundsOn univ D S)
    (ha : ∀ p ∈ D, |S.lam p.1 p.2| ≤ M ∧ |S.nu p.1 p.2| ≤ M ∧
      |S.phi p.1 p.2| ≤ M) : ∃ E : ℝ≥0∞, E ≠ ⊤ ∧ RawRayVariation D S E := by
  obtain ⟨C, hout, hin⟩ := h.variation_bounds
  let R := ENNReal.ofReal C
  let E := R + (ENNReal.ofReal M * R + ENNReal.ofReal M * R)
  have hE : E ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩⟩
  have hR : R ≤ E := le_self_add
  refine ⟨E, hE, ?_, ?_⟩
  · intro u
    have hh := hout u
    simp only [univ_inter] at hh
    refine ⟨hh.1.trans hR, hh.2.1.trans hR, ?_⟩
    have hmul := variation_mul_le (S.lam u) (S.phi u) {v | (u, v) ∈ D}
      (fun v hv => (ha (u, v) hv).1) (fun v hv => (ha (u, v) hv).2.2)
    have he : EqOn (S.dvpsi u) (fun v => S.theta u v + S.lam u v * S.phi u v)
        {v | (u, v) ∈ D} := by
      intro v _
      dsimp [SSFields.theta]
      ring
    rw [eVariationOn.congr he]
    apply (terminal_variation_sum_le _ _ _).trans
    apply add_le_add hh.2.2
    apply hmul.trans
    gcongr
    · exact hh.2.1
    · exact hh.1
  · intro v
    have hh := hin v
    simp only [univ_inter] at hh
    refine ⟨hh.1.trans hR, hh.2.1.trans hR, ?_⟩
    have hmul := variation_mul_le (fun u => S.nu u v) (fun u => S.phi u v)
      {u | (u, v) ∈ D} (fun u hu => (ha (u, v) hu).2.1)
      (fun u hu => (ha (u, v) hu).2.2)
    have he : EqOn (fun u => S.dupsi u v)
        (fun u => S.zeta u v + S.nu u v * S.phi u v) {u | (u, v) ∈ D} := by
      intro u _
      dsimp [SSFields.zeta]
      ring
    rw [eVariationOn.congr he]
    apply (terminal_variation_sum_le _ _ _).trans
    apply add_le_add hh.2.2
    apply hmul.trans
    gcongr
    · exact hh.2.1
    · exact hh.1

/-- E1's compact amplitudes discharge the axis boundedness premises of the
pullback core. Paper `e1a0fd5`, lines 1411–1422. -/
theorem selected_development_pullback_core {S Sdev : SSFields} {ui ū Co Ci : ℝ}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ}
    (hv : T ū = 0)
    (hd : ∀ x, HasDerivAt (T : ℝ → ℝ) (selectedJacobian S ū x) x)
    (hc : Continuous (selectedJacobian S ū))
    (hp : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ selectedJacobian S ū x)
    (hdev : ChristodoulouBV smallBVDomain (Ici 0) Sdev)
    (hg : SmallBVGeometry Sdev)
    (hdata : ∀ v > 0, Sdev.dvpsi 0 v = selectedInitialDatum S ū T v)
    (hout : ∀ u ≥ 0, smallBVOutgoingTV Sdev u < ENNReal.ofReal Co)
    (hin : ∀ v > 0, smallBVIncomingTV Sdev v < ENNReal.ofReal Ci) :
    ChrBVCore (lateContinuationDomain ū) (Ici ū)
      (Sdev.pullback T (selectedJacobian S ū)) := by
  obtain ⟨c, hc0, hcp⟩ := hp
  have hmap (p : ℝ × ℝ) (hp : p ∈ lateContinuationDomain ū) :
      (T p.1, T p.2) ∈ smallBVDomain :=
    ⟨by simpa only [hv] using T.monotone hp.1, T.strictMono hp.2⟩
  apply hdev.1.pullback T.strictMono T.continuous hmap
    (fun a ha => by change 0 ≤ T a; simpa only [hv] using T.monotone ha) (subset_univ _)
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    (fun a b _ _ x _ => (hd x).hasDerivWithinAt)
    (fun x _ => hc0.trans_le (hcp x)) hc.continuousOn
  intro a ha
  have hTa : 0 ≤ T a := by simpa only [hv] using T.monotone ha
  obtain ⟨M, _, hM⟩ := small_bv_raw_bounds (show 0 < T a + 1 by linarith)
    hdev hg hdata (h.selectedInitialDatum_continuous hū hv 0 (by simp)) hout hin
  refine ⟨M, ?_⟩
  have he : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ lateContinuationDomain ū},
      T v < T a + 1 :=
    Filter.Eventually.filter_mono (inf_le_left.trans nhdsWithin_le_nhds)
      (T.continuous.continuousAt.eventually_lt_const (by linarith))
  have hm : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ lateContinuationDomain ū},
      (a, v) ∈ lateContinuationDomain ū :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [he, hm] with v hv hpv
  have hh := hM (T a, T v) (hmap (a, v) hpv) hv.le
  exact ⟨hh.1, hh.2.2.2.1⟩

/-- A finite original-chart triangle has uniform pulled-back Christodoulou
bounds. Paper `e1a0fd5`, lines 1411–1422. The parameter B is a compact
coordinate upper bound, to be chosen after the compact set. -/
theorem selected_development_pullback_bounds {S Sdev : SSFields} {ui ū Co Ci B : ℝ}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ}
    (hv : T ū = 0) (hc : Continuous (selectedJacobian S ū))
    (hp : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ selectedJacobian S ū x)
    (hBV : BoundedVariationOn (selectedJacobian S ū) (Icc ū 0))
    (hdev : ChristodoulouBV smallBVDomain (Ici 0) Sdev) (hg : SmallBVGeometry Sdev)
    (hdata : ∀ v > 0, Sdev.dvpsi 0 v = selectedInitialDatum S ū T v)
    (hout : ∀ u ≥ 0, smallBVOutgoingTV Sdev u < ENNReal.ofReal Co)
    (hin : ∀ v > 0, smallBVIncomingTV Sdev v < ENNReal.ofReal Ci) :
    ChrBVBoundsOn univ {p | p ∈ lateContinuationDomain ū ∧ p.2 ≤ B}
      (Sdev.pullback T (selectedJacobian S ū)) := by
  let V := max 1 (T B)
  have hV : 0 < V := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let D := {p | p ∈ smallBVDomain ∧ p.2 ≤ V}
  let E := {p | p ∈ lateContinuationDomain ū ∧ p.2 ≤ B}
  have hsub : D ⊆ smallBVDomain := fun _ hp => hp.1
  obtain ⟨M, hM0, hM⟩ := small_bv_raw_bounds hV hdev hg hdata
    (h.selectedInitialDatum_continuous hū hv 0 (by simp)) hout hin
  have hraw : ∀ p ∈ D, |Sdev.lam p.1 p.2| ≤ M ∧ |Sdev.nu p.1 p.2| ≤ M ∧
      |Sdev.phi p.1 p.2| ≤ M ∧ |Sdev.dvpsi p.1 p.2| ≤ M ∧ |Sdev.dupsi p.1 p.2| ≤ M :=
    fun p hp => hM p hp.1 hp.2
  obtain ⟨R, hR, hr⟩ := raw_variation_of_chr (hdev.2.restrict hsub)
    (fun p hp => ⟨(hraw p hp).1, (hraw p hp).2.1, (hraw p hp).2.2.1⟩)
  obtain ⟨hJ, J, hJ0, hj⟩ := selected_jacobian_global hū.2 hc hBV
  obtain ⟨c, hc0, hcp⟩ := hp
  apply chr_pullback_bounds_of_raw (D := D) (E := E) (I := univ)
    (by norm_num : (0 : ℝ) < 1 / 3) hc0 hM0 hJ0 hR hJ T.monotone
  · intro p hp
    exact ⟨⟨by simpa only [hv] using T.monotone hp.1.1, T.strictMono hp.1.2⟩,
      (T.monotone hp.2).trans (le_max_right _ _)⟩
  · exact fun _ _ => ⟨mem_univ _, mem_univ _⟩
  · exact fun p hp => (hg p hp.1).1
  · exact hraw
  · exact hr
  · exact fun x _ => ⟨hcp x, hj x⟩
  · exact le_rfl

end AcExtensionPrinciple

end
