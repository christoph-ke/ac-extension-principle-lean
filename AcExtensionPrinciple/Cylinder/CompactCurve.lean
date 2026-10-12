module

public import AcExtensionPrinciple.Cylinder.Geometry
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Cylinder regularity at the initial outgoing ray

Paper `e1a0fd5`, `eq:cylinder-tangent`, lines
661–670. A compact inverse argument proves continuity also at u=ui; the
continuous tangent then extends to a one-sided derivative there.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Continuity of the canonical cylinder, including its initial-ray endpoint.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_continuousOn_closed {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 ≤ a1)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ContinuousOn (cylinderV h b) (Icc a0 a1) := by
  let K : Set (ℝ × ℝ) := (Icc ui a1 ×ˢ Icc ui 0) ∩ {p | p.1 ≤ p.2}
  have ha1 := hI (right_mem_Icc.mpr ha)
  have hKD : K ⊆ pastTriangle ui := by
    intro p hp
    exact ⟨hp.1.1.1, hp.1.1.2.trans_lt ha1.2.1, hp.2, hp.1.2.2⟩
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
    exact (h.radius_strictMono p.2.1.1.1 (p.2.1.1.2.trans_lt ha1.2.1)).injOn
      ⟨p.2.2, p.2.1.2.2⟩ ⟨by simpa only [hu, mem_ofPred_eq] using q.2.2, q.2.1.2.2⟩ hr
  let g : Icc a0 a1 → K := fun u => ⟨(u.1, cylinderV h b u.1), by
    have hu := hI u.2
    have hv := (h.cylinderV_spec hb hu).1
    exact ⟨⟨⟨hu.1, u.2.2⟩, ⟨hu.1.trans hv.1.le, hv.2.le⟩⟩, hv.1.le⟩⟩
  have hg : Continuous g := by
    apply (hF.isClosedEmbedding hinj).isEmbedding.continuous_iff.mpr
    have heq : F ∘ g = fun u : Icc a0 a1 => (u.1, b) := by
      ext u
      · rfl
      · exact (h.cylinderV_spec hb (hI u.2)).2
    rw [heq]
    exact continuous_subtype_val.prodMk continuous_const
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_snd.comp continuous_subtype_val).comp hg

/-- The tangent is continuous also at the initial-ray endpoint.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_tangent_continuousOn_closed {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 ≤ a1)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ContinuousOn (fun u => -S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u))
      (Icc a0 a1) := by
  have hc := continuousOn_id.prodMk (h.cylinderV_continuousOn_closed hb ha hI)
  have hm : MapsTo (fun u => (u, cylinderV h b u)) (Icc a0 a1) (pastTriangle ui) :=
    fun u hu => h.cylinder_mem hb (hI hu)
  exact ((h.regularCenter.continuous_nu.comp hc hm).neg).div
    (h.regularCenter.continuous_lam.comp hc hm)
    (fun u hu => ne_of_gt (h.lam_pos (hm hu)))

/-- Cylinder coordinates are AC even on intervals beginning at ui.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670, 731–737. -/
theorem cylinderV_ac_closed {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 ≤ a1)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    AbsolutelyContinuousOnInterval (cylinderV h b) a0 a1 := by
  apply cylinder_ac_of_continuous_derivative ha
    (h.cylinderV_continuousOn_closed hb ha hI)
    (h.cylinderV_tangent_continuousOn_closed hb ha hI)
  intro u hu
  exact h.cylinderV_hasDerivAt hb (hI (Ioo_subset_Icc_self hu))
    ((hI (left_mem_Icc.mpr ha)).1.trans_lt hu.1)

/-- The initial endpoint has a right derivative, and every cylinder point has the
relative derivative -ν_b/λ_b. Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_hasDerivWithinAt_closed {b a0 a1 u : ℝ} (hb : 0 < b)
    (ha : a0 < a1) (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) (hu : u ∈ Icc a0 a1) :
    HasDerivWithinAt (cylinderV h b)
      (-S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u)) (Icc a0 a1) u := by
  have hi := (hI (left_mem_Icc.mpr ha.le)).1
  rcases hu.1.eq_or_lt with he | heu
  · subst u
    have hd (s : ℝ) (hs : s ∈ Ioo a0 a1) :=
      h.cylinderV_hasDerivAt hb (hI (Ioo_subset_Icc_self hs)) (hi.trans_lt hs.1)
    have hcont := (h.cylinderV_continuousOn_closed hb ha.le hI) a0
      (left_mem_Icc.mpr ha.le)
    have hq := (h.cylinderV_tangent_continuousOn_closed hb ha.le hI) a0
      (left_mem_Icc.mpr ha.le)
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ha] at hq
    have hlim := hq.mono_left (nhdsWithin_mono a0 Ioi_subset_Ici_self)
    have hlimD : Tendsto (fun s => deriv (cylinderV h b) s) (𝓝[>] a0)
        (𝓝 (-S.nu a0 (cylinderV h b a0) / S.lam a0 (cylinderV h b a0))) := by
      apply hlim.congr'
      filter_upwards [Ioo_mem_nhdsGT ha] with s hs
      exact (hd s hs).deriv.symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (hcont.mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT ha) hlimD).mono Icc_subset_Ici_self
  · exact (h.cylinderV_hasDerivAt hb (hI hu) (hi.trans_lt heu)).hasDerivWithinAt

/-- C¹ regularity relative to the full closed cylinder interval, including u=ui.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_contDiffOn_closed {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 < a1)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ContDiffOn ℝ 1 (cylinderV h b) (Icc a0 a1) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc ha)]
  refine ⟨fun u hu => (h.cylinderV_hasDerivWithinAt_closed hb ha hI hu).differentiableWithinAt,
    ?_⟩
  apply (h.cylinderV_tangent_continuousOn_closed hb ha.le hI).congr
  intro u hu
  exact (h.cylinderV_hasDerivWithinAt_closed hb ha hI hu).derivWithin
    ((uniqueDiffOn_Icc ha) u hu)

/-- Uniform Lipschitz constant on every compact regular cylinder interval.
Paper `e1a0fd5`, lines 661–670, 731–737. -/
theorem cylinderV_lipschitz_closed {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 < a1)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    ∃ K : NNReal, LipschitzOnWith K (cylinderV h b) (Icc a0 a1) :=
  (h.cylinderV_contDiffOn_closed hb ha hI).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc

/-- Strict monotonicity on compact regular cylinder intervals, including their initial ray.
Paper `e1a0fd5`, `eq:cylinder-tangent`, lines 661–670. -/
theorem cylinderV_strictMonoOn_closed {b a0 a1 : ℝ} (hb : 0 < b) (ha : a0 ≤ a1)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) :
    StrictMonoOn (cylinderV h b) (Icc a0 a1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (h.cylinderV_continuousOn_closed hb ha hI)
  intro u hu
  have huI : u ∈ Ioo a0 a1 := by simpa only [interior_Icc] using hu
  rw [(h.cylinderV_hasDerivAt hb (hI (Ioo_subset_Icc_self huI))
    ((hI (left_mem_Icc.mpr ha)).1.trans_lt huI.1)).deriv]
  exact h.cylinderV_tangent_pos hb (hI (Ioo_subset_Icc_self huI))

/-- Both expressions for the boundary-time differential hold on the canonical cylinder.
Paper `e1a0fd5`, `eq:cylinder-time`, lines 671–673. -/
theorem cylinderV_time_tangent {b a0 a1 u : ℝ} (hb : 0 < b) (ha : a0 ≤ a1)
    (hI : Icc a0 a1 ⊆ cylinderDomain ui b S) (hu : u ∈ Ioo a0 a1) :
    deriv (cylinderTime S (cylinderV h b) a0) u = -S.nu u (cylinderV h b u) ∧
      deriv (cylinderTime S (cylinderV h b) a0) u =
        S.lam u (cylinderV h b u) * deriv (cylinderV h b) u := by
  have huC := Ioo_subset_Icc_self hu
  have hp := h.cylinder_mem hb (hI huC)
  have ht := (h.cylinder_time_hasDerivAt (h.cylinderV_continuousOn_closed hb ha hI)
    (fun s hs => h.cylinder_mem hb (hI hs)) hu).deriv
  refine ⟨ht, ?_⟩
  rw [ht, (h.cylinderV_hasDerivAt hb (hI huC)
    ((hI (left_mem_Icc.mpr ha)).1.trans_lt hu.1)).deriv]
  field_simp [(h.lam_pos hp).ne']

/-- The incoming ray reaches the axis within Kb on a sufficiently continued canonical cylinder.
Paper `e1a0fd5`, `eq:boundary-travel-time`, lines 745–749. -/
theorem cylinderV_axis_arrival {K b a0 a1 : ℝ} (hK : CylinderKBounds ui S K)
    (hb : 0 < b) (ha : a0 ≤ a1) (hI : Icc a0 a1 ⊆ cylinderDomain ui b S)
    (ht : K * b ≤ cylinderTime S (cylinderV h b) a0 a1) :
    cylinderV h b a0 ≤ a1 ∧
      cylinderTime S (cylinderV h b) a0 (cylinderV h b a0) ≤ K * b := by
  apply h.cylinder_axis_arrival_time_le hK ha (h.cylinderV_continuousOn_closed hb ha hI)
    (fun u hu => h.cylinder_mem hb (hI hu))
    (fun u hu => h.cylinderV_hasDerivAt hb (hI (Ioo_subset_Icc_self hu))
      ((hI (left_mem_Icc.mpr ha)).1.trans_lt hu.1))
    (fun u hu => (h.cylinderV_spec hb (hI hu)).2)
    (h.cylinderV_spec hb (hI (left_mem_Icc.mpr ha))).1.1.le ht

end AcExtensionPrinciple.StandingFull

end
