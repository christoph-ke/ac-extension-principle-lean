module

public import AcExtensionPrinciple.LateCylinder.Estimate

/-!
# Lemma 2.6 at the solution-class level

Paper `e1a0fd5`, `lem:late-cylinder-variation`, equations.tex lines 792–833.
The exterior hypothesis requires μ ≤ ε at all points with
u₀ ≤ u ≤ a₁ and r ≥ b. The cylinder is the canonical regular graph from
Cylinder.Curve. H > 0 is an arbitrary fixed boundary-time parameter.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Lemma 2.6 with a supplied geometric K. This internal helper takes only the already proved Lemma
1.1 conclusions; the source statement below chooses K from the standing assumptions. Paper
`e1a0fd5`, `lem:late-cylinder-variation`, lines 792–833, the past exterior condition. -/
theorem late_cylinder_variation_of_geometric {K H : ℝ}
    (hK : LateCylinderGeometry ui S K) (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps b u0 a0 a1, 0 < eps → eps ≤ 1 → 0 < b →
      ui ≤ u0 → a0 ≤ a1 → Icc a0 a1 ⊆ cylinderDomain ui b S →
      (∀ p ∈ pastTriangle ui, u0 ≤ p.1 → p.1 ≤ a1 → b ≤ S.r p.1 p.2 →
        S.mu p.1 p.2 ≤ eps) → initialACTail ui S u0 ≤ eps →
      K * b / eps ≤ a0 - u0 → lateCylinderTime S (cylinderV h b) a0 a1 ≤ H * b →
      eVariationOn (lateCylinderDatum S (cylinderV h b)) (Icc a0 a1) ≤
        ENNReal.ofReal (C * eps) := by
  obtain ⟨B, hB, hsource⟩ := h.exists_small_exterior_source
  obtain ⟨D, hD, hrem⟩ := h.exists_radial_remainder_bound
  obtain ⟨M, hscalar⟩ := h.uniform_scalar_bound
  have hM : 0 ≤ M := by
    have hh := hscalar (ui, ui) ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
    exact (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)).trans hh
  have hK0 : 0 < K := zero_lt_one.trans_le hK.1
  let R := D / (K⁻¹) ^ 2 + B / (K⁻¹ * (K⁻¹) ^ 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let C := K + (R + M * K) * H
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro eps b u0 a0 a1 heps heps1 hb hu0 ha hI hsmall hw hwait htime
  rcases eq_or_lt_of_le ha with he | ha'
  · subst a1
    simp only [Icc_self]
    rw [eVariationOn.subsingleton _ (Set.subsingleton_singleton)]
    exact bot_le
  have hwa : 0 < K * b / eps := by positivity
  have hu0a : u0 < a0 := by linarith
  have huiA : ui < a0 := hu0.trans_lt hu0a
  let v := cylinderV h b
  have hv := h.late_cylinderV_continuousOn hb huiA hI
  have hm := (h.late_cylinderV_strictMonoOn hb huiA hI).monotoneOn
  obtain ⟨Kv, hLip⟩ := h.late_cylinderV_exists_lipschitzOnWith hb huiA ha' hI
  have hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui := fun u hu => h.cylinder_mem hb (hI hu)
  have hs : ∀ u ∈ Icc a0 a1, (u, v u) ∈ late_cylinderInterior ui := fun u hu =>
    ⟨huiA.trans_le hu.1, (h.cylinderV_spec hb (hI hu)).1⟩
  have ht : ∀ u ∈ Icc a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u :=
    fun u hu => h.late_cylinderV_hasDerivAt hb (hI hu) (huiA.trans_le hu.1)
  have hr : ∀ u ∈ Icc a0 a1, S.r u (v u) = b := fun u hu => (h.cylinderV_spec hb (hI hu)).2
  obtain ⟨hP, hF, hd⟩ := h.late_cylinder_trace_calculus ha hv hm hLip hs ht
  have hRem : ∀ u ∈ Icc a0 a1, |radialDatumRemainderIntegral ui S u (v u)| ≤ R * eps / b := by
    intro u hu
    have hu0u : u0 ≤ u := hu0a.le.trans hu.1
    have huv := (hs u hu).2.1
    have hv0 := (hs u hu).2.2
    apply h.late_remainder_le_of_bounds hK hB.le hD.le hb heps hu0 hu0u
      (hp u hu).2.1 huv hv0.le (hr u hu).ge (by linarith [hu.1])
      (hrem u0 (v u) hu0 (hu0u.trans_lt (hp u hu).2.1) (hu0u.trans_lt huv) hv0.le)
    intro s hss
    have hsp : (s, v u) ∈ pastTriangle ui :=
      ⟨hu0.trans hss.1, hss.2.trans_lt (hp u hu).2.1, (hss.2.trans_lt huv).le, hv0.le⟩
    have hgrowth := h.late_incoming_radius_growth (fun _p hp' => (hK.2 _ hp').2.2)
      (hu0.trans hss.1) hss.2 (hp u hu).2.1 huv hv0.le
    have hsr : b ≤ S.r s (v u) := by
      rw [hr u hu] at hgrowth
      have hplus : 0 ≤ K⁻¹ * (u - s) := mul_nonneg (inv_nonneg.mpr hK0.le) (sub_nonneg.mpr hss.2)
      linarith
    exact hsource eps u0 s (v u) heps heps1 hu0 hss.1 hsp
      (hb.trans_le hsr) (hsmall (s, v u) hsp hss.1 (hss.2.trans hu.2) hsr) hw
  have htail : (∫ u in a0..a1, |deriv (fun s => S.dvpsi ui (v s)) u|) ≤ eps := by
    apply (h.late_initial_trace_derivative_bound ha hu0
      (hu0a.le.trans (hp a0 ⟨le_rfl, ha⟩).2.1.le) hm ?_ hF).trans hw
    intro u hu
    exact ⟨(hu0a.le.trans hu.1).trans (hp u hu).2.2.1, (hp u hu).2.2.2⟩
  apply h.late_variation_from_trace_bounds hK hM hR hH.le hb heps ha hv hp hr
    (fun u hu => hsmall (u, v u) (hp u hu) (hu0a.le.trans hu.1) hu.2 (hr u hu).ge)
    (fun u hu => ?_) hRem hP hF hd htail htime
  have hh := hscalar (u, v u) (hp u hu)
  dsimp [outgoingAmplitude]
  linarith [abs_nonneg (S.dvpsi u (v u) / S.lam u (v u)), abs_nonneg (S.phi u (v u))]

/-- Lemma 2.6 under StandingFull alone: one geometric K works for every positive H, and C is chosen
before ε, b, u₀ and both interval endpoints. Paper `e1a0fd5`, `lem:late-cylinder-variation`, lines
792–833, the past exterior condition. -/
theorem late_cylinder_variation :
    ∃ K : ℝ, LateCylinderGeometry ui S K ∧ ∀ H : ℝ, 0 < H →
      ∃ C : ℝ, 0 < C ∧ ∀ eps b u0 a0 a1, 0 < eps → eps ≤ 1 → 0 < b →
        ui ≤ u0 → a0 ≤ a1 → Icc a0 a1 ⊆ cylinderDomain ui b S →
        (∀ p ∈ pastTriangle ui, u0 ≤ p.1 → p.1 ≤ a1 → b ≤ S.r p.1 p.2 →
          S.mu p.1 p.2 ≤ eps) → initialACTail ui S u0 ≤ eps →
        K * b / eps ≤ a0 - u0 → lateCylinderTime S (cylinderV h b) a0 a1 ≤ H * b →
        eVariationOn (lateCylinderDatum S (cylinderV h b)) (Icc a0 a1) ≤
        ENNReal.ofReal (C * eps) := by
  obtain ⟨K, hK⟩ := h.exists_late_cylinder_geometry
  exact ⟨K, hK, fun _H hH => h.late_cylinder_variation_of_geometric hK hH⟩

end StandingFull

end AcExtensionPrinciple

end
