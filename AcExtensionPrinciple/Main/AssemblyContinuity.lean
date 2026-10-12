module

public import AcExtensionPrinciple.Main.AssemblyAxis

/-!
# Right continuity and regular-axis conditions of the patch

Paper `e1a0fd5`, `equations.tex` lines 222 and 1411–1422. The identified
representatives select a single source in each right neighborhood. Every
axis point has a coordinate neighborhood matching one regular source.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

section

variable {ui ū : ℝ} {S N P : SSFields} (hū : ū ∈ Ioo ui 0)
  (hold : FieldsAgreeOn (pastTriangle ui \ axis ui) P S)
  (hnew : FieldsAgreeOn (lateContinuationDomain ū) P N)

/-- A continuation point before the cut belongs to the old domain.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuation_point_old {p : ℝ × ℝ} (hp : p ∈ continuationDomain ui ū)
    (hu : p.1 < ū) : p ∈ pastTriangle ui \ axis ui := by
  rcases hp with ho | hn
  · exact ho
  · exact (not_le_of_gt hu hn.1).elim

include hū hold hnew

/-- Outgoing right continuity transfers from the selected source row.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_right_cont_out {q : SSFields → ℝ → ℝ → ℝ}
    (hq : LocalQuantity q)
    (hc₁ : ∀ p ∈ pastTriangle ui \ axis ui, ContinuousWithinAt (q S p.1)
      {v | p.2 ≤ v ∧ (p.1, v) ∈ pastTriangle ui \ axis ui} p.2)
    (hc₂ : ∀ p ∈ lateContinuationDomain ū, ContinuousWithinAt (q N p.1)
      {v | p.2 ≤ v ∧ (p.1, v) ∈ lateContinuationDomain ū} p.2)
    {p : ℝ × ℝ} (hp : p ∈ continuationDomain ui ū) :
    ContinuousWithinAt (q P p.1) {v | p.2 ≤ v ∧ (p.1, v) ∈ continuationDomain ui ū} p.2 := by
  by_cases hu : ū ≤ p.1
  · have hlate : p ∈ lateContinuationDomain ū :=
      ⟨hu, (continuationDomain_coordinates hū hp).2⟩
    have hs : {v | p.2 ≤ v ∧ (p.1, v) ∈ continuationDomain ui ū} ⊆
        {v | p.2 ≤ v ∧ (p.1, v) ∈ lateContinuationDomain ū} :=
      fun v hv => ⟨hv.1, hu, (continuationDomain_coordinates hū hv.2).2⟩
    exact ((hc₂ p hlate).mono hs).congr
      (fun v hv => hq P N p.1 v (hnew (p.1, v) (hs hv).2))
      (hq P N p.1 p.2 (hnew p hlate))
  · have hu' : p.1 < ū := not_le.mp hu
    have ho := continuation_point_old hp hu'
    have hs : {v | p.2 ≤ v ∧ (p.1, v) ∈ continuationDomain ui ū} ⊆
        {v | p.2 ≤ v ∧ (p.1, v) ∈ pastTriangle ui \ axis ui} :=
      fun v hv => ⟨hv.1, continuation_point_old hv.2 hu'⟩
    exact ((hc₁ p ho).mono hs).congr
      (fun v hv => hq P S p.1 v (hold (p.1, v) (hs hv).2))
      (hq P S p.1 p.2 (hold p ho))

/-- Incoming right continuity uses the development at and after the cut,
and the old class in a right neighborhood before it.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_right_cont_in {q : SSFields → ℝ → ℝ → ℝ}
    (hq : LocalQuantity q)
    (hc₁ : ∀ p ∈ pastTriangle ui \ axis ui, ContinuousWithinAt (fun u => q S u p.2)
      {u | p.1 ≤ u ∧ (u, p.2) ∈ pastTriangle ui \ axis ui} p.1)
    (hc₂ : ∀ p ∈ lateContinuationDomain ū, ContinuousWithinAt (fun u => q N u p.2)
      {u | p.1 ≤ u ∧ (u, p.2) ∈ lateContinuationDomain ū} p.1)
    {p : ℝ × ℝ} (hp : p ∈ continuationDomain ui ū) :
    ContinuousWithinAt (fun u => q P u p.2)
      {u | p.1 ≤ u ∧ (u, p.2) ∈ continuationDomain ui ū} p.1 := by
  by_cases hu : ū ≤ p.1
  · have hlate : p ∈ lateContinuationDomain ū :=
      ⟨hu, (continuationDomain_coordinates hū hp).2⟩
    have hs : {u | p.1 ≤ u ∧ (u, p.2) ∈ continuationDomain ui ū} ⊆
        {u | p.1 ≤ u ∧ (u, p.2) ∈ lateContinuationDomain ū} :=
      fun u hu' => ⟨hu'.1, hu.trans hu'.1, (continuationDomain_coordinates hū hu'.2).2⟩
    exact ((hc₂ p hlate).mono hs).congr
      (fun u hu' => hq P N u p.2 (hnew (u, p.2) (hs hu').2))
      (hq P N p.1 p.2 (hnew p hlate))
  · have hu' : p.1 < ū := not_le.mp hu
    have ho := continuation_point_old hp hu'
    let R := {u | p.1 ≤ u ∧ (u, p.2) ∈ continuationDomain ui ū}
    have hs : R ∩ Iio ū ⊆ {u | p.1 ≤ u ∧ (u, p.2) ∈ pastTriangle ui \ axis ui} :=
      fun u hu => ⟨hu.1.1, continuation_point_old hu.1.2 hu.2⟩
    have hc := ((hc₁ p ho).mono hs).congr
      (fun u hu => hq P S u p.2 (hold (u, p.2) (hs hu).2))
      (hq P S p.1 p.2 (hold p ho))
    simpa only [ContinuousWithinAt, R, nhdsWithin_inter_of_mem'
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hu'))] using hc

/-- Every axis point of the continuation matches one source class in a
coordinate neighborhood. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_axis_conditions
    (h₁ : ChrBVCore (pastTriangle ui \ axis ui) (Ico ui 0) S)
    (h₂ : ChrBVCore (lateContinuationDomain ū) (Ici ū) N)
    {a : ℝ} (ha : a ∈ Ici ui) :
    Tendsto (P.r a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) ∧
    Tendsto (P.m a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) ∧
    Tendsto (fun v => P.nu a v + P.lam a v)
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) ∧
    ChrAxisVanishingVariation (continuationDomain ui ū) P a ∧
    Tendsto (fun v => P.dvpsi a v + P.dupsi a v)
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) := by
  have htransfer {E : Set (ℝ × ℝ)} {A : Set ℝ} {Q : SSFields} {η : ℝ}
      (hη : 0 < η) (hcore : ChrBVCore E A Q) (haQ : a ∈ A)
      (hm : ∀ p ∈ continuationDomain ui ū, |p.1 - a| < η → |p.2 - a| < η →
        p ∈ E ∧ P.values p.1 p.2 = Q.values p.1 p.2) :
      Tendsto (P.r a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) ∧
      Tendsto (P.m a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) ∧
      Tendsto (fun v => P.nu a v + P.lam a v)
        (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) ∧
      ChrAxisVanishingVariation (continuationDomain ui ū) P a ∧
      Tendsto (fun v => P.dvpsi a v + P.dupsi a v)
        (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ continuationDomain ui ū}) (𝓝 0) :=
    ⟨axis_limit_local_transfer hη local_r hm (hcore.radius_axis_limit a haQ),
      axis_limit_local_transfer hη local_m hm (hcore.mass_axis_limit a haQ),
      axis_limit_local_transfer hη (local_nu.add local_lam) hm (hcore.expansion_axis_limit a haQ),
      axis_variation_local_transfer hη hm (hcore.scalar_axis_variation a haQ),
      axis_limit_local_transfer hη (local_dvpsi.add local_dupsi) hm (hcore.psi_axis_limit a haQ)⟩
  by_cases ha0 : a < 0
  · apply htransfer (η := -a) (by linarith) h₁ ⟨ha, ha0⟩
    intro p hp hp₁ hp₂
    have hu0 : p.1 < 0 := by linarith [(abs_lt.mp hp₁).2]
    have hv0 : p.2 < 0 := by linarith [(abs_lt.mp hp₂).2]
    have hcoord := continuationDomain_coordinates hū hp
    have ho : p ∈ pastTriangle ui \ axis ui :=
      past_offaxis_iff.mpr ⟨hcoord.1, hu0, hcoord.2, hv0.le⟩
    exact ⟨ho, hold p ho⟩
  · have ha0' : 0 ≤ a := not_lt.mp ha0
    apply htransfer (η := a - ū) (by linarith [hū.2]) h₂ (hū.2.le.trans ha0')
    intro p hp hp₁ _
    have hu : ū ≤ p.1 := by linarith [(abs_lt.mp hp₁).1]
    have hn : p ∈ lateContinuationDomain ū :=
      ⟨hu, (continuationDomain_coordinates hū hp).2⟩
    exact ⟨hn, hnew p hn⟩

end

end AcExtensionPrinciple

end
