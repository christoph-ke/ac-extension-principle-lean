module

public import AcExtensionPrinciple.Main.AssemblyAgreement

/-!
# Compact amplitude bounds for the small-BV development

Paper `e1a0fd5`, `equations.tex` lines 1411–1422. Characteristic primitives,
the exact continuous initial datum and E1's uniform variation estimates
supply the amplitude bounds required by the gauge transport helpers.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Including a right-continuous initial point preserves variation.
Paper `e1a0fd5`, lines 1411–1443; BV representative convention at line 222. -/
theorem variation_include_left {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousWithinAt f (Ici a) a) :
    eVariationOn f (Ioo a b) = eVariationOn f (Ico a b) := by
  have hnb : (𝓝[Iio b ∩ Ioi a] a).NeBot := by
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab))]
    infer_instance
  have he := eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    (s := Iio b) hnb (hc.mono inter_subset_right)
  have h₁ : Iio b ∩ Ioi a = Ioo a b := by ext x; simp [and_comm]
  have h₂ : Iio b ∩ Ici a = Ico a b := by ext x; simp [and_comm]
  simpa only [h₁, h₂] using he

/-- E1 geometry bounds division by either expansion by three times the
numerator amplitude. Paper `e1a0fd5`, `eq:small-bv-geometry`, lines 1369–1373. -/
theorem abs_div_le_three {x y : ℝ} (hy : (1 / 3 : ℝ) ≤ |y|) :
    |x / y| ≤ 3 * |x| := by
  rw [abs_div]
  have hy0 : 0 < |y| := lt_of_lt_of_le (by norm_num) hy
  apply (div_le_iff₀ hy0).mpr
  nlinarith [abs_nonneg x]

/-- Incoming ψ transport supplies continuity of the initial duψ away from
its vertex. Paper `e1a0fd5`, lines 66–84, 222 and 1411–1422. -/
theorem ChrBVCore.continuous_initial_dupsi {S : SSFields} {V : ℝ}
    (h : ChrBVCore smallBVDomain (Ici 0) S) :
    ContinuousOn (S.dupsi 0) (Ioc 0 V) := by
  apply continuousOn_of_locally_continuousOn
  intro x hx
  have hhalf : 0 < x / 2 := by linarith [hx.1]
  have hlt : x / 2 < x := by linarith [hx.1]
  have hs : outSeg 0 (x / 2) V ⊆ smallBVDomain := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hu0 : u = 0 := hu
    subst u
    exact ⟨le_rfl, hhalf.trans_le hv.1⟩
  have hAC := intervalPrimitive_ac (hlt.le.trans hx.2)
    (fun z hz => h.dupsi_out 0 (x / 2) z hz.1
      ((prod_mono_right (Icc_subset_Icc le_rfl hz.2)).trans hs))
  have hC : ContinuousOn (S.dupsi 0) (Icc (x / 2) V) := by
    simpa only [uIcc_of_le (hlt.le.trans hx.2)] using hAC.continuousOn
  exact ⟨Ioi (x / 2), isOpen_Ioi, hlt,
    hC.mono (fun _ hv => ⟨hv.2.le, hv.1.2⟩)⟩

/-- The exact initial datum and the axis sum law bound initial duψ on a
punctured compact cone. Paper `e1a0fd5`, lines 1396–1402 and 1411–1422. -/
theorem initial_dupsi_bound {S : SSFields} {α : ℝ → ℝ} {V : ℝ} (hV : 0 < V)
    (h : ChrBVCore smallBVDomain (Ici 0) S)
    (hdata : ∀ v > 0, S.dvpsi 0 v = α v)
    (hc : ContinuousWithinAt α (Ici 0) 0) :
    ∃ M : ℝ, ∀ v ∈ Ioc 0 V, |S.dupsi 0 v| ≤ M := by
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓟 {v | (0, v) ∈ smallBVDomain} := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact ⟨le_rfl, hv⟩
  have hsum := (h.psi_axis_limit 0 (by simp)).mono_left (le_inf le_rfl hfilter)
  have hd : Tendsto (S.dvpsi 0) (𝓝[>] 0) (𝓝 (α 0)) := by
    apply ((hc.mono Ioi_subset_Ici_self).tendsto).congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hdata v hv).symm
  have hz : Tendsto (S.dupsi 0) (𝓝[>] 0) (𝓝 (-α 0)) := by
    simpa only [add_sub_cancel_left, zero_sub] using hsum.sub hd
  exact bounded_punctured_interval hV h.continuous_initial_dupsi hz

/-- The normalized incoming variation estimate also includes u = 0 by the
representative convention. Paper `e1a0fd5`, lines 1375–1382 and 1411–1443. -/
theorem incoming_normalized_variation_include_initial {S : SSFields} {v : ℝ}
    (h : ChrBVCore smallBVDomain (Ici 0) S) (hg : SmallBVGeometry S) (hv : 0 < v) :
    eVariationOn (fun u => S.dupsi u v / S.nu u v) (Ioo 0 v) =
      eVariationOn (fun u => S.dupsi u v / S.nu u v) (Ico 0 v) := by
  have hhalf : 0 < v / 2 ∧ v / 2 < v := by constructor <;> linarith
  have hs : inSeg v 0 (v / 2) ⊆ smallBVDomain := by
    rintro ⟨u, w⟩ ⟨hu, hw⟩
    have hwv : w = v := hw
    subst w
    exact ⟨hu.1, hu.2.trans_lt hhalf.2⟩
  have hd := h.dupsi_right_cont_on_inSeg hhalf.1.le hs
    (show (0 : ℝ) ∈ Icc 0 (v / 2) from ⟨le_rfl, hhalf.1.le⟩)
  have hn := (h.nu_right_cont (0, v) ⟨le_rfl, hv⟩).mono
    (show Icc 0 (v / 2) ⊆ {u | 0 ≤ u ∧ (u, v) ∈ smallBVDomain} from
      fun u hu => ⟨hu.1, hs ⟨hu, by simp⟩⟩)
  have hn0 : S.nu 0 v ≠ 0 := by
    have hh := (hg (0, v) ⟨le_rfl, hv⟩).2.2.1
    linarith
  have hc := hd.div hn hn0
  change ContinuousWithinAt (fun u => S.dupsi u v / S.nu u v) (Icc 0 (v / 2)) 0 at hc
  have hc' : ContinuousWithinAt (fun u => S.dupsi u v / S.nu u v) (Ici 0) 0 := by
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hhalf.1] using hc
  exact variation_include_left hv hc'

/-- All five raw fields needed for gauge BV transport have uniform amplitudes
on a finite development triangle. Paper `e1a0fd5`, lines 1411–1422.
No premise beyond E1's class, geometry, variation bounds and continuous
initial datum is imposed on a source statement. -/
theorem small_bv_raw_bounds {S : SSFields} {α : ℝ → ℝ} {V Co Ci : ℝ}
    (hV : 0 < V) (h : ChristodoulouBV smallBVDomain (Ici 0) S)
    (hg : SmallBVGeometry S) (hdata : ∀ v > 0, S.dvpsi 0 v = α v)
    (hc : ContinuousWithinAt α (Ici 0) 0)
    (hout : ∀ u ≥ 0, smallBVOutgoingTV S u < ENNReal.ofReal Co)
    (hin : ∀ v > 0, smallBVIncomingTV S v < ENNReal.ofReal Ci) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ smallBVDomain, p.2 ≤ V →
      |S.lam p.1 p.2| ≤ M ∧ |S.nu p.1 p.2| ≤ M ∧ |S.phi p.1 p.2| ≤ M ∧
        |S.dvpsi p.1 p.2| ≤ M ∧ |S.dupsi p.1 p.2| ≤ M := by
  have hseg : inSeg (V + 1) 0 V ⊆ smallBVDomain := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hv' : v = V + 1 := hv
    subst v
    exact ⟨hu.1, by linarith [hu.2]⟩
  have hphiC : ContinuousOn (fun u => S.phi u (V + 1)) (Icc 0 V) := by
    simpa only [uIcc_of_le hV.le] using (h.1.scalar_ac_in (V + 1) 0 V hV.le hseg).continuousOn
  have hdAC := intervalPrimitive_ac hV.le (fun x hx =>
    h.1.dvpsi_in (V + 1) 0 x hx.1
      ((prod_mono_left (Icc_subset_Icc le_rfl hx.2)).trans hseg))
  have hdC : ContinuousOn (fun u => S.dvpsi u (V + 1)) (Icc 0 V) := by
    simpa only [uIcc_of_le hV.le] using hdAC.continuousOn
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hphiC
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hdC
  obtain ⟨Z, hZ⟩ := initial_dupsi_bound hV h.1 hdata hc
  obtain ⟨C, hvar, _⟩ := h.2.variation_bounds
  let R := (ENNReal.ofReal C).toReal
  let A := (ENNReal.ofReal Co).toReal + 3 * |D|
  let B := (ENNReal.ofReal Ci).toReal + 3 * |Z|
  let F := R + |P|
  let M := max 1 (max F (max A B))
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  refine ⟨M, hM0, ?_⟩
  intro p hp hpV
  have hpu : p.1 ∈ Icc 0 V := ⟨hp.1, hp.2.le.trans hpV⟩
  have hgeom := hg p hp
  have hlpos : 0 < S.lam p.1 p.2 := lt_of_lt_of_le (by norm_num) hgeom.1
  have hnneg : S.nu p.1 p.2 < 0 := by linarith [hgeom.2.2.1]
  have hlam : |S.lam p.1 p.2| ≤ 1 := by rw [abs_of_pos hlpos]; linarith [hgeom.2.1]
  have hnu : |S.nu p.1 p.2| ≤ 1 := by rw [abs_of_neg hnneg]; linarith [hgeom.2.2.2.1]
  have hφ : |S.phi p.1 p.2| ≤ F := by
    have hs : Ioi p.1 ⊆ {v | (p.1, v) ∈ univ ∩ smallBVDomain} :=
      fun v hv => ⟨mem_univ _, hp.1, hv⟩
    have hv := (eVariationOn.mono _ hs).trans (hvar p.1).2.1
    have hBV : BoundedVariationOn (S.phi p.1) (Ioi p.1) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv
    have hb : V + 1 ∈ Ioi p.1 := by change p.1 < V + 1; linarith [hpu.2]
    have hbound := boundedVariation_abs_bound hBV hp.2 hb
    have hanchor : |S.phi p.1 (V + 1)| ≤ |P| := by
      have hh : |S.phi p.1 (V + 1)| ≤ P := by simpa only [Real.norm_eq_abs] using hP _ hpu
      exact hh.trans (le_abs_self _)
    exact hbound.trans (add_le_add (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv) hanchor)
  have hα : |S.dvpsi p.1 p.2 / S.lam p.1 p.2| ≤ A := by
    have hv : eVariationOn (fun v => S.dvpsi p.1 v / S.lam p.1 v) (Ioi p.1) ≤
        ENNReal.ofReal Co := (le_self_add.trans le_self_add).trans (hout _ hp.1).le
    have hBV : BoundedVariationOn (fun v => S.dvpsi p.1 v / S.lam p.1 v) (Ioi p.1) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv
    have hb : V + 1 ∈ Ioi p.1 := by change p.1 < V + 1; linarith [hpu.2]
    have hanchor : |S.dvpsi p.1 (V + 1) / S.lam p.1 (V + 1)| ≤ 3 * |D| := by
      have hg' := hg (p.1, V + 1) ⟨hp.1, hb⟩
      have hh : |S.dvpsi p.1 (V + 1)| ≤ |D| := by
        have hh' : |S.dvpsi p.1 (V + 1)| ≤ D := by simpa only [Real.norm_eq_abs] using hD _ hpu
        exact hh'.trans (le_abs_self _)
      exact (abs_div_le_three (hg'.1.trans (le_abs_self _))).trans (by gcongr)
    exact (boundedVariation_abs_bound hBV hp.2 hb).trans
      (add_le_add (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv) hanchor)
  have hβ : |S.dupsi p.1 p.2 / S.nu p.1 p.2| ≤ B := by
    have hv0 : 0 < p.2 := hp.1.trans_lt hp.2
    have hv : eVariationOn (fun u => S.dupsi u p.2 / S.nu u p.2) (Ico 0 p.2) ≤
        ENNReal.ofReal Ci := by
      rw [← incoming_normalized_variation_include_initial h.1 hg hv0]
      exact (le_self_add.trans le_self_add).trans (hin _ hv0).le
    have hBV : BoundedVariationOn (fun u => S.dupsi u p.2 / S.nu u p.2) (Ico 0 p.2) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv
    have hanchor : |S.dupsi 0 p.2 / S.nu 0 p.2| ≤ 3 * |Z| := by
      have hg' := hg (0, p.2) ⟨le_rfl, hv0⟩
      have hnu' : (1 / 3 : ℝ) ≤ |S.nu 0 p.2| := by
        exact hg'.2.2.1.trans (neg_le_abs _)
      exact (abs_div_le_three hnu').trans
        (mul_le_mul_of_nonneg_left ((hZ _ ⟨hv0, hpV⟩).trans (le_abs_self _)) (by norm_num))
    exact (boundedVariation_abs_bound hBV hp ⟨le_rfl, hv0⟩).trans
      (add_le_add (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv) hanchor)
  have hA0 : 0 ≤ A := add_nonneg ENNReal.toReal_nonneg (by positivity)
  have hB0 : 0 ≤ B := add_nonneg ENNReal.toReal_nonneg (by positivity)
  have hd : |S.dvpsi p.1 p.2| ≤ A := by
    have hh := mul_le_mul hα hlam (abs_nonneg _) hA0
    rw [← abs_mul, div_mul_cancel₀ _ (ne_of_gt hlpos), mul_one] at hh
    exact hh
  have hz : |S.dupsi p.1 p.2| ≤ B := by
    have hh := mul_le_mul hβ hnu (abs_nonneg _) hB0
    rw [← abs_mul, div_mul_cancel₀ _ (ne_of_lt hnneg), mul_one] at hh
    exact hh
  exact ⟨hlam.trans (le_max_left _ _), hnu.trans (le_max_left _ _),
    hφ.trans ((le_max_left _ _).trans (le_max_right _ _)),
    hd.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    hz.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩

end AcExtensionPrinciple

end
