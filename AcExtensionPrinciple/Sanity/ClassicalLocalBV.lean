module

public import AcExtensionPrinciple.Sanity.ClassicalAxis
public import AcExtensionPrinciple.Solution.FullReduction
public import AcExtensionPrinciple.Sanity.ClassicalVariation

/-!
# Classical solutions satisfy all local BV clauses
Paper `e1a0fd5`, lines 66–84 and 220–275, Luk–Oh Definition 2.1;
Christodoulou CPAM p. 1157. Bounds are uniform on the whole closed triangle.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ClassicalTriangleSolution

variable {ui : ℝ} {S : SSFields} (h : ClassicalTriangleSolution ui S)
include h

/-- One expansion bound works on the entire closed triangle.
Paper `e1a0fd5`, line 222, Def. 2.1(1); Christodoulou CPAM p. 1157. -/
theorem expansion_bounds : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closedTriangle ui,
    c ≤ S.lam p.1 p.2 ∧ -S.nu p.1 p.2 ≤ 1 / c := by
  have hn : (closedTriangle ui).Nonempty := ⟨(ui, ui), le_rfl, le_rfl, h.initial_negative.le⟩
  obtain ⟨x, hx, hmin⟩ := (classical_triangle_compact ui).exists_isMinOn hn
    h.c1_lam.continuousOn
  obtain ⟨y, hy, hmax⟩ := (classical_triangle_compact ui).exists_isMaxOn hn
    h.c1_nu.continuousOn.neg
  have hx0 := (h.expansions x hx).1
  have hy0 := neg_pos.mpr (h.expansions y hy).2
  let c := min (S.lam x.1 x.2) (1 / (-S.nu y.1 y.2))
  have hc : 0 < c := lt_min hx0 (one_div_pos.mpr hy0)
  refine ⟨c, hc, fun p hp => ⟨(min_le_left _ _).trans (hmin hp), ?_⟩⟩
  apply (hmax hp).trans
  apply (le_div_iff₀ hc).mpr
  calc
    -S.nu y.1 y.2 * c ≤ -S.nu y.1 y.2 * (1 / (-S.nu y.1 y.2)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hy0.le
    _ = 1 := by field_simp [(h.expansions y hy).2.ne]

omit h in
/-- Restrict a continuous classical field to a stored right-continuous outgoing trace.
Paper `e1a0fd5`, line 222, Luk–Oh BV convention pp. 1608–1609. -/
theorem right_cont_out {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (closedTriangle ui))
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    ContinuousWithinAt (fun w => f (p.1, w))
      {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2 := by
  exact (hf.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun w hw => classical_past_subset_closed ui hw.2)) p.2 ⟨le_rfl, hp⟩

omit h in
/-- Restrict a continuous classical field to a stored right-continuous incoming trace.
Paper `e1a0fd5`, line 222, Luk–Oh BV convention pp. 1608–1609. -/
theorem right_cont_in {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (closedTriangle ui))
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    ContinuousWithinAt (fun s => f (s, p.2))
      {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1 := by
  exact (hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun s hs => classical_past_subset_closed ui hs.2)) p.1 ⟨le_rfl, hp⟩

/-- Every classical solution satisfies every field of the full local BV class.
Paper `e1a0fd5`, lines 66–84 and 220–275; Christodoulou CPAM p. 1157. -/
theorem localBV_full : LocalBVSolutionFull (pastTriangle ui) S := by
  constructor
  · intro u a b hab hs; exact h.radius_out hab hs
  · intro v a b hab hs; exact h.radius_in hab hs
  · intro u a b hab hs; exact h.psi_out hab hs
  · intro v a b hab hs; exact h.psi_in hab hs
  · intro u a b hab hs; exact h.mass_out hab hs
  · intro v a b hab hs; exact h.mass_in hab hs
  · intro v a b hab hs; exact h.lam_in hab (hs.trans sdiff_subset)
  · intro u a b hab hs; exact h.nu_out hab (hs.trans sdiff_subset)
  · intro v a b hab hs; exact h.dvpsi_in hab (hs.trans sdiff_subset)
  · intro u a b hab hs; exact h.dupsi_out hab (hs.trans sdiff_subset)
  · intro K _ hK
    obtain ⟨c, hc, hb⟩ := h.expansion_bounds
    exact ⟨c, hc, fun p hp => hb p (classical_past_subset_closed ui (hK hp))⟩
  · intro K _ hK
    obtain ⟨C, hC, _⟩ := classical_uniform_variation h.c1_lam
    obtain ⟨D, _, hD⟩ := classical_uniform_variation h.c1_nu
    exact ⟨max C D,
      fun u a b hab hs => (hC u a b hab (hs.trans hK)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      fun v a b hab hs => (hD v a b hab (hs.trans hK)).trans
        (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  · intro a ha
    have haxis : (a, a) ∈ AcExtensionPrinciple.axis ui := ⟨ha.1, ha.2.1, rfl⟩
    have ht := axis_outgoing_limit (h.c1_nu.continuousOn.add h.c1_lam.continuousOn) haxis
    simpa [(h.axis a ha.1 ha.2.1.le).2.2] using ht
  · intro K _ hK
    obtain ⟨C, hC, hD⟩ := classical_uniform_variation h.c1_phi
    refine ⟨C, ?_, ?_⟩
    · intro u a b hab hs
      exact ⟨classical_ac_out (f := fun p : ℝ × ℝ => S.phi p.1 p.2) h.c1_phi hab
        ((hs.trans hK).trans (classical_past_subset_closed ui)), hC u a b hab (hs.trans hK)⟩
    · intro v a b hab hs
      exact ⟨classical_ac_in (f := fun p : ℝ × ℝ => S.phi p.1 p.2) h.c1_phi hab
        ((hs.trans hK).trans (classical_past_subset_closed ui)), hD v a b hab (hs.trans hK)⟩
  · intro a _; exact classical_axis_variation h.c1_phi a
  · intro K _ hK
    obtain ⟨C, hC, _⟩ := classical_uniform_variation h.c1_dvpsi
    obtain ⟨D, _, hD⟩ := classical_uniform_variation h.c1_dupsi
    exact ⟨max C D,
      fun u a b hab hs => (hC u a b hab (hs.trans hK)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      fun v a b hab hs => (hD v a b hab (hs.trans hK)).trans
        (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  · intro a ha
    have haxis : (a, a) ∈ AcExtensionPrinciple.axis ui := ⟨ha.1, ha.2.1, rfl⟩
    have ht := axis_outgoing_limit
      (h.c1_dvpsi.continuousOn.add h.c1_dupsi.continuousOn) haxis
    simpa [h.dvpsi_axis haxis, h.dupsi_axis haxis,
      (h.axis a ha.1 ha.2.1.le).2.2] using ht
  · intro a ha; exact ⟨(h.axis a ha.1 ha.2.1.le).1, (h.axis a ha.1 ha.2.1.le).2.1⟩
  · intro p hp; exact right_cont_out h.c1_lam.continuousOn hp
  · intro p hp; exact right_cont_out h.c1_dvpsi.continuousOn hp
  · intro p hp; exact right_cont_in h.c1_nu.continuousOn hp
  · intro p hp; exact right_cont_in h.c1_dupsi.continuousOn hp

/-- Every classical solution satisfies the minimal local BV source class.
Paper `e1a0fd5`, lines 66–84 and 220–275, Luk–Oh Definition 2.1. -/
theorem localBV : LocalBVSolution (pastTriangle ui) S :=
  h.localBV_full.toMinimal

end ClassicalTriangleSolution

end AcExtensionPrinciple

end
