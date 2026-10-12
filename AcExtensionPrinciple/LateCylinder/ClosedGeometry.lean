module

public import AcExtensionPrinciple.LateCylinder.Uniform

/-!
# Regular cylinders including the terminal incoming boundary

Paper `e1a0fd5`, equations.tex lines 661–670 and 792–833.
Regularity permits a cylinder endpoint at v = 0. The canonical cylinder
returns zero at that endpoint; continuity follows from a compact inverse.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Available rays of a closed regular cylinder, including v = 0. Paper `e1a0fd5`, lines 661–670 and
792–798, regular cylinder and exterior conditions. -/
@[expose] def closedCylinderDomain (ui b : ℝ) (S : SSFields) : Set ℝ :=
  {u | ui ≤ u ∧ u < 0 ∧ b ≤ S.r u 0}

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The canonical cylinder also has the correct radius at a terminal
endpoint. Paper `e1a0fd5`, lines 661–670. -/
theorem late_closed_cylinder_spec {b u : ℝ} (hb : 0 < b)
    (hu : u ∈ closedCylinderDomain ui b S) :
    cylinderV h b u ∈ Ioc u 0 ∧ S.r u (cylinderV h b u) = b := by
  by_cases ht : b < S.r u 0
  · have hs := h.cylinderV_spec hb ⟨hu.1, hu.2.1, ht⟩
    exact ⟨⟨hs.1.1, hs.1.2.le⟩, hs.2⟩
  · have hz : cylinderV h b u = 0 := by
      simp [cylinderV, cylinderDomain, ht]
    rw [hz]
    exact ⟨⟨hu.2.1, le_rfl⟩, le_antisymm (not_lt.mp ht) hu.2.2⟩

/-- The closed cylinder graph is continuous up to either coordinate boundary.
Paper `e1a0fd5`, lines 661–670 and 731–737. -/
theorem late_closed_cylinder_continuous {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 ≤ a1)
    (hI : Icc a0 a1 ⊆ closedCylinderDomain ui b S) :
    ContinuousOn (cylinderV h b) (Icc a0 a1) := by
  let T : Set (ℝ × ℝ) := (Icc ui a1 ×ˢ Icc ui 0) ∩ {p | p.1 ≤ p.2}
  have ha1 := hI (right_mem_Icc.mpr ha)
  have hTD : T ⊆ pastTriangle ui := by
    intro p hp
    exact ⟨hp.1.1.1, hp.1.1.2.trans_lt ha1.2.1, hp.2, hp.1.2.2⟩
  have hT : IsCompact T :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_fst continuous_snd)
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let F : T → ℝ × ℝ := fun p => (p.1.1, S.r p.1.1 p.1.2)
  have hF : Continuous F :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (h.regularCenter.continuous_r.mono hTD).domRestrict
  have hinj : Function.Injective F := by
    intro p q he
    have hu : p.1.1 = q.1.1 := by simpa only [F] using congrArg Prod.fst he
    have hr : S.r p.1.1 p.1.2 = S.r p.1.1 q.1.2 := by
      simpa only [F, ← hu] using congrArg Prod.snd he
    apply Subtype.ext
    apply Prod.ext hu
    exact (h.radius_strictMono p.2.1.1.1 (p.2.1.1.2.trans_lt ha1.2.1)).injOn
      ⟨p.2.2, p.2.1.2.2⟩ ⟨by simpa only [hu, mem_ofPred_eq] using q.2.2, q.2.1.2.2⟩ hr
  let g : Icc a0 a1 → T := fun u => ⟨(u.1, cylinderV h b u.1), by
    have hu := hI u.2
    have hv := (h.late_closed_cylinder_spec hb hu).1
    exact ⟨⟨⟨hu.1, u.2.2⟩, ⟨hu.1.trans hv.1.le, hv.2⟩⟩, hv.1.le⟩⟩
  have hg : Continuous g := by
    apply (hF.isClosedEmbedding hinj).isEmbedding.continuous_iff.mpr
    have heq : F ∘ g = fun u : Icc a0 a1 => (u.1, b) := by
      ext u
      · rfl
      · exact (h.late_closed_cylinder_spec hb (hI u.2)).2
    rw [heq]
    exact continuous_subtype_val.prodMk continuous_const
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_snd.comp continuous_subtype_val).comp hg

/-- Joint continuity of the normalized datum at every off-axis triangle
point, including v = 0. Paper `e1a0fd5`, lines 422–426 and 731–737. -/
theorem late_datum_continuousWithinAt {p : ℝ × ℝ}
    (hp : p ∈ pastTriangle ui) (hpv : p.1 < p.2) :
    ContinuousWithinAt (fun p : ℝ × ℝ => S.dvpsi p.1 p.2 / S.lam p.1 p.2)
      (pastTriangle ui) p := by
  let U := (p.1 + p.2) / 2
  let a := (U + p.2) / 2
  have huU : p.1 < U := by dsimp [U]; linarith
  have hUa : U < a := by dsimp [a, U]; linarith
  have hav : a < p.2 := by dsimp [a, U]; linarith
  have hU0 : U < 0 := hUa.trans_le (hav.le.trans hp.2.2.2)
  have hab : a ≤ 0 := hav.le.trans hp.2.2.2
  have hRect := properRectangle_subset_triangle (ui := ui) hU0 hUa le_rfl
  have hc := (h.dvpsi_continuous_rectangle (hp.1.trans huU.le) hab hU0 hUa le_rfl).div
    (h.regularCenter.continuous_lam.mono hRect)
    (fun q hq => (h.lam_pos (hRect hq)).ne')
  have hn : Icc ui U ×ˢ Icc a 0 ∈ 𝓝[pastTriangle ui] p := by
    have hUn : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < U :=
      continuous_fst.continuousAt.eventually (Iio_mem_nhds huU)
    have han : ∀ᶠ q : ℝ × ℝ in 𝓝 p, a < q.2 :=
      continuous_snd.continuousAt.eventually (Ioi_mem_nhds hav)
    filter_upwards [self_mem_nhdsWithin, hUn.filter_mono nhdsWithin_le_nhds,
      han.filter_mono nhdsWithin_le_nhds] with q hq hUq haq
    exact ⟨⟨hq.1, hUq.le⟩, ⟨haq.le, hq.2.2.2⟩⟩
  exact (hc p ⟨⟨hp.1, huU.le⟩, ⟨hav.le, hp.2.2.2⟩⟩).mono_left (nhdsWithin_le_of_mem hn)

/-- Continuity of the closed cylinder datum, including its terminal endpoint.
Paper `e1a0fd5`, lines 731–737 and 792–833. -/
theorem late_closed_datum_continuous {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 ≤ a1)
    (hI : Icc a0 a1 ⊆ closedCylinderDomain ui b S) :
    ContinuousOn (lateCylinderDatum S (cylinderV h b)) (Icc a0 a1) := by
  have hv := h.late_closed_cylinder_continuous hb ha hI
  have hp : MapsTo (fun u => (u, cylinderV h b u)) (Icc a0 a1) (pastTriangle ui) := by
    intro u hu
    have hvs := (h.late_closed_cylinder_spec hb (hI hu)).1
    exact ⟨(hI hu).1, (hI hu).2.1, hvs.1.le, hvs.2⟩
  intro u hu
  have hmap : Tendsto (fun s => (s, cylinderV h b s)) (𝓝[Icc a0 a1] u)
      (𝓝[pastTriangle ui] (u, cylinderV h b u)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuousWithinAt_id.prodMk (hv u hu)).tendsto, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hp hs
  exact (h.late_datum_continuousWithinAt (hp hu)
    (h.late_closed_cylinder_spec hb (hI hu)).1.1).tendsto.comp hmap

end StandingFull

end AcExtensionPrinciple

end
