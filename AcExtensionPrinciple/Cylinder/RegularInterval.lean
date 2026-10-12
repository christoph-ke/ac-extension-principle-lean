module

public import AcExtensionPrinciple.Cylinder.IntervalCalculus
public import AcExtensionPrinciple.Cylinder.ScalarRegion

/-!
# Regular closed cylinder intervals

Paper statement encoding. Paper `e1a0fd5`, lines 661–749: a regular interval lies before u=0, starts
at or after ui, and satisfies r(u,0)≥b. Equality is permitted at the terminal edge v=0.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A regular closed cylinder interval, with the terminal characteristic edge included. Paper
`e1a0fd5`, lines 661–706, 742–749. -/
@[expose] def RegularCylinderInterval (ui : ℝ) (S : SSFields) (b a0 a1 : ℝ) : Prop :=
  a0 ≤ a1 ∧ ui ≤ a0 ∧ a1 < 0 ∧ ∀ u ∈ Icc a0 a1, b ≤ S.r u 0

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The terminal radius strictly decreases along incoming transport.
Paper `e1a0fd5`, `eq:radius`, lines 661–670, 742–749. -/
theorem cylinder_terminal_radius_strictAnti {x y : ℝ} (hx : ui ≤ x)
    (hy : y < 0) (hxy : x < y) : S.r y 0 < S.r x 0 := by
  have hs := inSeg_subset_triangle hx hy hy.le le_rfl
  have ht := h.regularCenter.localBV.radius_in 0 x y hxy.le hs
  have hc := continuous_in h.regularCenter.continuous_nu hs
  have hi : 0 < ∫ s in x..y, -S.nu s 0 :=
    intervalIntegral.integral_pos hxy hc.neg
      (fun s hs' => (neg_pos.mpr (h.nu_neg (p := (s, 0)) (hs ⟨⟨hs'.1.le, hs'.2⟩, by simp⟩))).le)
      ⟨x, ⟨le_rfl, hxy.le⟩,
        neg_pos.mpr (h.nu_neg (p := (x, 0)) (hs ⟨⟨le_rfl, hxy.le⟩, by simp⟩))⟩
  rw [intervalIntegral.integral_neg] at hi
  linarith [ht.2]

/-- Every parameter before the final endpoint has an interior cylinder intersection. Paper
`e1a0fd5`, lines 661–670, the regular closed-interval condition. -/
theorem cylinder_regular_interior {b a0 a1 u : ℝ}
    (hI : RegularCylinderInterval ui S b a0 a1) (hu : u ∈ Ico a0 a1) :
    u ∈ cylinderDomain ui b S := by
  refine ⟨hI.2.1.trans hu.1, hu.2.trans hI.2.2.1, ?_⟩
  exact (hI.2.2.2 a1 (right_mem_Icc.mpr hI.1)).trans_lt
    (h.cylinder_terminal_radius_strictAnti (hI.2.1.trans hu.1) hI.2.2.1 hu.2)

/-- The canonical curve also represents an endpoint on v=0, with r=b. Paper `e1a0fd5`,
`eq:cylinder-tangent`, lines 661–670, the regular closed-interval condition. -/
theorem cylinderV_spec_regular {b a0 a1 u : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (hu : u ∈ Icc a0 a1) :
    cylinderV h b u ∈ Ioc u 0 ∧ S.r u (cylinderV h b u) = b := by
  have hui := hI.2.1.trans hu.1
  have hu0 := hu.2.trans_lt hI.2.2.1
  have hbr := hI.2.2.2 u hu
  by_cases hstrict : b < S.r u 0
  · have hv := h.cylinderV_spec hb ⟨hui, hu0, hstrict⟩
    exact ⟨⟨hv.1.1, hv.1.2.le⟩, hv.2⟩
  · have hv0 : cylinderV h b u = 0 := by
      classical
      simp only [cylinderV]
      rw [dite_eq_right (by rintro ⟨_, _, _, hs⟩; exact hstrict hs)]
    rw [hv0]
    exact ⟨⟨hu0, le_rfl⟩, le_antisymm (le_of_not_gt hstrict) hbr⟩

/-- The canonical regular cylinder lies in the closed off-axis domain.
Paper `e1a0fd5`, lines 661–670, 731–737. -/
theorem cylinderV_mem_regular {b a0 a1 u : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (hu : u ∈ Icc a0 a1) :
    (u, cylinderV h b u) ∈ cylinderScalarRegion ui := by
  have hv := (h.cylinderV_spec_regular hb hI hu).1
  exact ⟨hI.2.1.trans hu.1, hv.1, hv.2⟩

/-- Continuity of the canonical graph on regular cylinder intervals, including an endpoint on v=0.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_continuousOn_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    ContinuousOn (cylinderV h b) (Icc a0 a1) := by
  let K : Set (ℝ × ℝ) := (Icc ui a1 ×ˢ Icc ui 0) ∩ {p | p.1 ≤ p.2}
  have hKD : K ⊆ pastTriangle ui := by
    intro p hp
    exact ⟨hp.1.1.1, hp.1.1.2.trans_lt hI.2.2.1, hp.2, hp.1.2.2⟩
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_fst continuous_snd)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K → ℝ × ℝ := fun p => (p.1.1, S.r p.1.1 p.1.2)
  have hF : Continuous F :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (h.regularCenter.continuous_r.mono hKD).domRestrict
  have hinj : Function.Injective F := by
    intro p q he
    have hu : p.1.1 = q.1.1 := by simpa only [F] using congrArg Prod.fst he
    have hr : S.r p.1.1 p.1.2 = S.r p.1.1 q.1.2 := by
      simpa only [F, ← hu] using congrArg Prod.snd he
    apply Subtype.ext
    apply Prod.ext hu
    exact (h.radius_strictMono p.2.1.1.1 (p.2.1.1.2.trans_lt hI.2.2.1)).injOn
      ⟨p.2.2, p.2.1.2.2⟩
      ⟨by simpa only [hu, mem_ofPred_eq] using q.2.2, q.2.1.2.2⟩ hr
  let g : Icc a0 a1 → K := fun u => ⟨(u.1, cylinderV h b u.1), by
    have hu := h.cylinderV_mem_regular hb hI u.2
    exact ⟨⟨⟨hu.1, u.2.2⟩, ⟨hu.1.trans hu.2.1.le, hu.2.2⟩⟩, hu.2.1.le⟩⟩
  have hg : Continuous g := by
    apply (hF.isClosedEmbedding hinj).isEmbedding.continuous_iff.mpr
    have heq : F ∘ g = fun u : Icc a0 a1 => (u.1, b) := by
      ext u
      · rfl
      · exact (h.cylinderV_spec_regular hb hI u.2).2
    rw [heq]
    exact continuous_subtype_val.prodMk continuous_const
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_snd.comp continuous_subtype_val).comp hg

/-- The ordinary tangent identity holds at all interior regular cylinder interval parameters. Paper
`e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_hasDerivAt_regular {b a0 a1 u : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (hu : u ∈ Ioo a0 a1) :
    HasDerivAt (cylinderV h b)
      (-S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u)) u :=
  h.cylinderV_hasDerivAt hb (h.cylinder_regular_interior hI ⟨hu.1.le, hu.2⟩)
    (hI.2.1.trans_lt hu.1)

/-- Tangent coefficients are continuous through the terminal characteristic edge. Paper `e1a0fd5`,
`eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_tangent_continuousOn_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    ContinuousOn (fun u => -S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u))
      (Icc a0 a1) := by
  have hc := continuousOn_id.prodMk (h.cylinderV_continuousOn_regular hb hI)
  have hm : MapsTo (fun u => (u, cylinderV h b u)) (Icc a0 a1) (pastTriangle ui) :=
    fun u hu => cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI hu)
  exact ((h.regularCenter.continuous_nu.comp hc hm).neg).div
    (h.regularCenter.continuous_lam.comp hc hm)
    (fun u hu => (h.lam_pos (hm hu)).ne')

/-- The regular cylinder graph is C¹ relative to its closed interval. Paper `e1a0fd5`,
`eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_contDiffOn_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (ha : a0 < a1) :
    ContDiffOn ℝ 1 (cylinderV h b) (Icc a0 a1) :=
  cylinder_interval_contDiffOn ha (h.cylinderV_continuousOn_regular hb hI)
    (h.cylinderV_tangent_continuousOn_regular hb hI)
    (fun _ hu => h.cylinderV_hasDerivAt_regular hb hI hu)

/-- The regular cylinder graph has a compact-interval Lipschitz constant. Paper `e1a0fd5`, lines
661–670, 731–737. -/
theorem cylinderV_lipschitz_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (ha : a0 < a1) :
    ∃ K : ℝ≥0, LipschitzOnWith K (cylinderV h b) (Icc a0 a1) :=
  (h.cylinderV_contDiffOn_regular hb hI ha).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc

/-- The regular cylinder graph is strictly increasing, including a possible endpoint on v=0. Paper
`e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_strictMonoOn_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) :
    StrictMonoOn (cylinderV h b) (Icc a0 a1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (h.cylinderV_continuousOn_regular hb hI)
  intro u hu
  have huI : u ∈ Ioo a0 a1 := by simpa only [interior_Icc] using hu
  rw [(h.cylinderV_hasDerivAt_regular hb hI huI).deriv]
  have hp := cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI
    (Ioo_subset_Icc_self huI))
  exact div_pos (neg_pos.mpr (h.nu_neg hp)) (h.lam_pos hp)

/-- The class-level incoming ray arrival bound on every sufficiently long regular cylinder interval.
Paper `e1a0fd5`, `eq:boundary-travel-time`, lines 742–749. -/
theorem cylinderV_axis_arrival_regular {K b a0 a1 : ℝ} (hK : CylinderKBounds ui S K)
    (hb : 0 < b) (hI : RegularCylinderInterval ui S b a0 a1)
    (ht : K * b ≤ cylinderTime S (cylinderV h b) a0 a1) :
    cylinderV h b a0 ≤ a1 ∧
      cylinderTime S (cylinderV h b) a0 (cylinderV h b a0) ≤ K * b := by
  exact h.cylinder_axis_arrival_time_le hK hI.1 (h.cylinderV_continuousOn_regular hb hI)
    (fun u hu => cylinderScalarRegion_subset ui (h.cylinderV_mem_regular hb hI hu))
    (fun _ hu => h.cylinderV_hasDerivAt_regular hb hI hu)
    (fun _ hu => (h.cylinderV_spec_regular hb hI hu).2)
    (h.cylinderV_spec_regular hb hI (left_mem_Icc.mpr hI.1)).1.1.le ht

end StandingFull

end AcExtensionPrinciple

end
