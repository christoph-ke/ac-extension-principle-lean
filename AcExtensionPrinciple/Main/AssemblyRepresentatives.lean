module

public import AcExtensionPrinciple.Sanity.FlatSmallBV
public import AcExtensionPrinciple.Sanity.FlatStanding
public import AcExtensionPrinciple.Gauge.Reparam

/-!
# Audit of the BV representative convention

Paper `e1a0fd5`, `equations.tex` lines 1411–1422.
The previously proposed change of λ on one vertical characteristic is
excluded by the right-continuity convention now present in the class.
The elementary point-modification facts are retained for the audit.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace AssemblyRepresentativeAudit

/-- The unmodified half-gauge solution is the transformed original solution
of a valid standing-class example, with ui = −1 and selected cone ū = −1/2.
Its terminal characteristic is ṽ = 1, precisely the modified characteristic
below. Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem selected_flat_source :
    StandingFull (-1) (flat 0) ∧
      (flat 0).pullback (fun t => (t - 1) / 2) (fun _ => 1 / 2) = halfFlat 0 := by
  constructor
  · exact flat_standing_full (-1) 0 (by norm_num)
  · dsimp [flat, halfFlat, scaledFlat, SSFields.pullback]
    congr 1 <;> funext u v <;> ring

/-- Replace a constant's value at one characteristic label.
Paper `e1a0fd5`, lines 1411–1422; audit of BV representatives.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
@[expose] noncomputable def pointValue (c q x : ℝ) : ℝ := if x = 1 then q else c

/-- The point modification is invisible to Lebesgue integrals.
Paper `e1a0fd5`, lines 220–275 and 1411–1422.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem pointValue_ae (c q : ℝ) : pointValue c q =ᵐ[volume] fun _ => c := by
  have hn : ∀ᵐ x : ℝ, x ≠ 1 := by rw [ae_iff]; simp
  exact hn.mono (fun x hx => by simp [pointValue, hx])

/-- Every right limit is the original constant, including at the modified
point. Paper `e1a0fd5`, lines 220–275 and 1411–1422.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem pointValue_right_limit (c q a : ℝ) :
    Tendsto (pointValue c q) (𝓝[>] a) (𝓝 c) := by
  apply tendsto_const_nhds.congr'
  by_cases ha : a = 1
  · subst a
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [pointValue, ne_of_gt hx]
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_ne_nhds ha)] with x hx
    simp [pointValue, hx]

/-- A single point change contributes twice its distance from the original
constant to total variation on the complete line.
Paper `e1a0fd5`, lines 1411–1422; pointwise BV audit.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem pointValue_variation (c q : ℝ) :
    eVariationOn (pointValue c q) univ = edist q c + edist q c := by
  have hl : Tendsto (pointValue c q) (𝓝[<] (1 : ℝ)) (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [pointValue, ne_of_lt hx]
  have hli : eVariationOn (pointValue c q) (Iio 1) = 0 := by
    rw [eVariationOn.congr (g := fun _ => c) (fun x hx => by
      simp [pointValue, ne_of_lt hx])]
    exact flat_variation_const _ _
  have hri : eVariationOn (pointValue c q) (Ioi 1) = 0 := by
    rw [eVariationOn.congr (g := fun _ => c) (fun x hx => by
      simp [pointValue, ne_of_gt hx])]
    exact flat_variation_const _ _
  have hL := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
    (s := univ) (a := (1 : ℝ)) (by simpa using
      (inferInstance : (𝓝[<] (1 : ℝ)).NeBot)) (mem_univ 1) (by simpa using hl)
  have hR := eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist
    (s := univ) (a := (1 : ℝ)) (by simpa using
      (inferInstance : (𝓝[>] (1 : ℝ)).NeBot)) (mem_univ 1)
    (by simpa using pointValue_right_limit c q 1)
  have he := eVariationOn.union (pointValue c q)
    (isGreatest_Iic (a := (1 : ℝ))) (isLeast_Ici (a := (1 : ℝ)))
  simpa [Iic_union_Ici, hli, hri, pointValue] using he.trans
    (congrArg₂ (· + ·) (by simpa [hli, pointValue] using hL) (by simpa [hri, pointValue] using hR))

/-- Half-gauge Minkowski fields with λ's value changed on v = 1.
Paper `e1a0fd5`, lines 1411–1422; audit of the E1/E2 overlap premise.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
@[expose] noncomputable def fields (q : ℝ) : SSFields :=
  { halfFlat 0 with lam := fun _ v => pointValue (1 / 2) q v }

/-- The modified field retains all nonlinear sources at zero.
Paper `e1a0fd5`, lines 66–84 and 1411–1422.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem sources (q u v : ℝ) :
    (fields q).mu u v = 0 ∧ (fields q).theta u v = 0 ∧
    (fields q).zeta u v = 0 ∧ (fields q).radiusCoeff u v = 0 ∧
    (fields q).massV u v = 0 ∧ (fields q).massU u v = 0 := by
  simp [fields, halfFlat, scaledFlat, SSFields.mu, massRatio, SSFields.theta,
    SSFields.zeta, SSFields.radiusCoeff, SSFields.massV, SSFields.massU]

/-- The old point modification violates the BV representative convention.
Paper `e1a0fd5`, lines 222 and 1411–1422; Christodoulou p. 1197 and
Luk–Oh pp. 1608–1609. This closes the earlier representative audit.
Paper e1a0fd5 replaces the mass-reconstruction argument with BV uniqueness at line 1411. -/
theorem point_modification_not_core {q : ℝ} (hq : q ≠ 1 / 2) :
    ¬ ChrBVCore smallBVDomain (Ici 0) (fields q) := by
  intro h
  have hc := h.lam_right_cont (0, 1) (by norm_num [smallBVDomain])
  have hsub : Ioi (1 : ℝ) ⊆ {w | (0, 1).2 ≤ w ∧ ((0, 1).1, w) ∈ smallBVDomain} := by
    intro w hw
    exact ⟨hw.le, le_rfl, (zero_lt_one.trans hw)⟩
  have ht : Tendsto (pointValue (1 / 2) q) (𝓝[>] (1 : ℝ)) (𝓝 q) := by
    have hh := (hc.mono hsub).tendsto
    change Tendsto (pointValue (1 / 2) q) (𝓝[>] (1 : ℝ))
      (𝓝 (pointValue (1 / 2) q 1)) at hh
    simpa only [pointValue, ite_true] using hh
  exact hq (tendsto_nhds_unique ht (pointValue_right_limit (1 / 2) q 1))

end AssemblyRepresentativeAudit

end AcExtensionPrinciple

end
