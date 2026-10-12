module

public import AcExtensionPrinciple.LateCylinder.ClosedGeometry

/-!
# Lemma 2.6 on closed regular cylinders

Paper `e1a0fd5`, `lem:late-cylinder-variation`, equations.tex lines 792–833. This completes the
regular cylinder and exterior conditions, allowing a right endpoint on v = 0. The estimate on proper
initial subintervals extends to the endpoint by continuity, with the same constant and the same
boundary-time bound.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A uniform variation bound on proper initial subintervals extends to a
continuous closed endpoint. Paper `e1a0fd5`, endpoint calculus for
`eq:late-cylinder-variation`, lines 792–833. -/
theorem late_variation_closed_endpoint {f : ℝ → ℝ} {a b : ℝ} {T : ℝ≥0∞}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hbound : ∀ x ∈ Ico a b, eVariationOn f (Icc a x) ≤ T) :
    eVariationOn f (Icc a b) ≤ T := by
  have h1 : Icc a b ∩ Iio b = Ico a b := by
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      exact ⟨hx.1, hxb⟩
    · intro hx
      exact ⟨⟨hx.1, hx.2.le⟩, hx.2⟩
  have h2 : Icc a b ∩ Iic b = Icc a b := inter_eq_left.mpr (fun _x hx => hx.2)
  have hne : (𝓝[Icc a b ∩ Iio b] b).NeBot := by
    rw [h1]
    exact right_nhdsWithin_Ico_neBot hab
  have he := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt hne
    ((hc b ⟨hab.le, le_rfl⟩).mono inter_subset_left)
  rw [h1, h2] at he
  rw [← he, eVariationOn.eq_biSup_inter_Icc]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  apply (eVariationOn.mono f ?_).trans (hbound p.2 hp.2.1)
  intro x hx
  exact ⟨hx.1.1, hx.2.2⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Lemma 2.6 with a geometric K, on the full closed regular-cylinder interface. Paper `e1a0fd5`,
`lem:late-cylinder-variation`, lines 792–833, including terminal endpoints under the regular
cylinder and exterior conditions. -/
theorem late_cylinder_variation_closed_of_geometric {K H : ℝ}
    (hK : LateCylinderGeometry ui S K) (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps b u0 a0 a1, 0 < eps → eps ≤ 1 → 0 < b →
      ui ≤ u0 → a0 ≤ a1 → Icc a0 a1 ⊆ closedCylinderDomain ui b S →
      (∀ p ∈ pastTriangle ui, u0 ≤ p.1 → p.1 ≤ a1 → b ≤ S.r p.1 p.2 →
        S.mu p.1 p.2 ≤ eps) → initialACTail ui S u0 ≤ eps →
      K * b / eps ≤ a0 - u0 → lateCylinderTime S (cylinderV h b) a0 a1 ≤ H * b →
      eVariationOn (lateCylinderDatum S (cylinderV h b)) (Icc a0 a1) ≤
        ENNReal.ofReal (C * eps) := by
  obtain ⟨C, hC, hbound⟩ := h.late_cylinder_variation_of_geometric hK hH
  refine ⟨C, hC, ?_⟩
  intro eps b u0 a0 a1 heps heps1 hb hu0 ha hI hsmall hw hwait htime
  rcases eq_or_lt_of_le ha with he | ha'
  · subst a1
    simp only [Icc_self]
    rw [eVariationOn.subsingleton _ Set.subsingleton_singleton]
    exact bot_le
  have hv := h.late_closed_cylinder_continuous hb ha hI
  have hp : ∀ u ∈ Icc a0 a1, (u, cylinderV h b u) ∈ pastTriangle ui := by
    intro u hu
    have hvs := (h.late_closed_cylinder_spec hb (hI hu)).1
    exact ⟨(hI hu).1, (hI hu).2.1, hvs.1.le, hvs.2⟩
  have hn := (h.regularCenter.continuous_nu.comp (continuousOn_id.prodMk hv) hp).neg
  have hni := hn.intervalIntegrable_of_Icc (μ := volume) ha
  apply late_variation_closed_endpoint ha' (h.late_closed_datum_continuous hb ha hI)
  intro x hx
  have hxI : Icc a0 x ⊆ Icc a0 a1 := Icc_subset_Icc le_rfl hx.2.le
  have hIx : Icc a0 x ⊆ cylinderDomain ui b S := by
    intro u hu
    have huc := hI (hxI hu)
    have ha1 := hI (right_mem_Icc.mpr ha)
    have hg := h.late_incoming_radius_growth (fun _p hp' => (hK.2 _ hp').2.2)
      huc.1 (hu.2.trans hx.2.le) ha1.2.1 ha1.2.1 le_rfl
    have hK0 : 0 < K := zero_lt_one.trans_le hK.1
    have hdelta : 0 < K⁻¹ * (a1 - u) :=
      mul_pos (inv_pos.mpr hK0) (sub_pos.mpr (hu.2.trans_lt hx.2))
    exact ⟨huc.1, huc.2.1, by linarith [ha1.2.2]⟩
  have htx : lateCylinderTime S (cylinderV h b) a0 x ≤ H * b := by
    apply (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2.le ?_ hni).trans htime
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    exact (neg_pos.mpr (h.nu_neg (hp u ⟨hu.1.le, hu.2⟩))).le
  exact hbound eps b u0 a0 x heps heps1 hb hu0 hx.1 hIx
    (fun p hp' hu0p hpx hbp => hsmall p hp' hu0p (hpx.trans hx.2.le) hbp) hw hwait htx

/-- Lemma 2.6 under StandingFull, with exactly the regular cylinder and exterior
hypotheses, including a possible endpoint on v = 0. K is chosen before H; C is chosen before every
cylinder and small parameter. Paper `e1a0fd5`, `lem:late-cylinder-variation`, equations.tex lines
792–833. -/
theorem late_cylinder_variation_closed :
    ∃ K : ℝ, LateCylinderGeometry ui S K ∧ ∀ H : ℝ, 0 < H →
      ∃ C : ℝ, 0 < C ∧ ∀ eps b u0 a0 a1, 0 < eps → eps ≤ 1 → 0 < b →
        ui ≤ u0 → a0 ≤ a1 → Icc a0 a1 ⊆ closedCylinderDomain ui b S →
        (∀ p ∈ pastTriangle ui, u0 ≤ p.1 → p.1 ≤ a1 → b ≤ S.r p.1 p.2 →
          S.mu p.1 p.2 ≤ eps) → initialACTail ui S u0 ≤ eps →
        K * b / eps ≤ a0 - u0 → lateCylinderTime S (cylinderV h b) a0 a1 ≤ H * b →
        eVariationOn (lateCylinderDatum S (cylinderV h b)) (Icc a0 a1) ≤
        ENNReal.ofReal (C * eps) := by
  obtain ⟨K, hK⟩ := h.exists_late_cylinder_geometry
  exact ⟨K, hK, fun _H hH => h.late_cylinder_variation_closed_of_geometric hK hH⟩

end StandingFull

end AcExtensionPrinciple

end
