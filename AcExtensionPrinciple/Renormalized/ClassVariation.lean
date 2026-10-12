module

public import AcExtensionPrinciple.Solution.Geometry
public import AcExtensionPrinciple.Solution.PositiveAC
public import AcExtensionPrinciple.Renormalized.IncomingIdentities

/-!
# Outgoing variation and renormalized fields in the solution class

Paper `e1a0fd5`, `equations.tex` lines 997–1023.
The variation uses the actual closed-cone representative of the datum.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Normalized outgoing datum. Paper `e1a0fd5`, `eq:outgoing-variation`,
lines 997–1001. -/
@[expose] noncomputable def SSFields.outgoingDatum (S : SSFields) (u v : ℝ) : ℝ :=
  S.dvpsi u v / S.lam u v

/-- Closed-cone total variation, with values in the extended nonnegative reals.
Paper `e1a0fd5`, `eq:outgoing-variation`, lines 997–1001. -/
@[expose] noncomputable def SSFields.outgoingVariation (S : SSFields) (u : ℝ) : ℝ≥0∞ :=
  eVariationOn (S.outgoingDatum u) (Icc u 0)

/-- Radial derivative of the outgoing datum, defined almost everywhere.
Paper `e1a0fd5`, `eq:radial-datum-derivative`, lines 555–558. -/
@[expose] noncomputable def SSFields.radialDatumDerivative (S : SSFields) (u v : ℝ) : ℝ :=
  deriv (S.outgoingDatum u) v / S.lam u v

/-- Renormalized derivative as a field. Paper `e1a0fd5`,
`eq:renormalized-derivative`, lines 1020–1021. -/
@[expose] noncomputable def SSFields.renormalizedDerivative
    (S : SSFields) (q : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  Renormalized.renormalizedDerivativeOf (S.r u v) (S.lam u v)
    (S.m u v) (S.dvphi u v) (q u v)

/-- Renormalized interaction as a field. Paper `e1a0fd5`,
`eq:renormalized-interaction`, lines 1022–1023. -/
@[expose] noncomputable def SSFields.renormalizedInteraction (S : SSFields) (u v : ℝ) : ℝ :=
  Renormalized.interactionOf (S.r u v) (S.lam u v) (S.nu u v)
    (S.m u v) (S.duphi u v) (S.dvphi u v)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)

include h

/-- On a compact interval of outgoing times the terminal values of `∂ᵥψ`
are continuous, by the incoming integral equation. Paper `e1a0fd5`,
lines 222 and 1001. -/
theorem dvpsi_terminal_ac {a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) :
    AbsolutelyContinuousOnInterval (fun u => S.dvpsi u 0) a b := by
  apply intervalPrimitive_ac (g := fun u => S.radiusCoeff u 0 * S.phi u 0) hab
  intro x hx
  exact h.regularCenter.localBV.dvpsi_in 0 a x hx.1
    (inSeg_subset_offAxis ha (hx.2.trans_lt hb) (hx.2.trans_lt hb) le_rfl)

/-- The local BV bounds imply a uniform bound for `V(u)` on each compact
subinterval of proper outgoing times. Paper `e1a0fd5`,
`eq:outgoing-variation`, lines 997–1001. No AC propagation premise is used. -/
theorem outgoingVariation_locally_bounded {a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) :
    ∃ C : ℝ, ∀ u ∈ Icc a b, S.outgoingVariation u ≤ ENNReal.ofReal C := by
  let K : Set (ℝ × ℝ) := (Icc a b ×ˢ Icc a 0) ∩ {p | p.1 ≤ p.2}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_fst continuous_snd)
  have hKD : K ⊆ pastTriangle ui := by
    rintro p ⟨⟨hu, hv⟩, huv⟩
    exact ⟨ha.trans hu.1, hu.2.trans_lt hb, huv, hv.2⟩
  have hseg (u : ℝ) (hu : u ∈ Icc a b) : outSeg u u 0 ⊆ K := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    simp only [mem_singleton_iff] at hx
    subst x
    exact ⟨⟨hu, ⟨hu.1.trans hv.1, hv.2⟩⟩, hv.1⟩
  obtain ⟨c, hc, he⟩ := h.regularCenter.localBV.expansion_bounds K hK hKD
  obtain ⟨Clam, hlam, _⟩ := h.regularCenter.localBV.expansion_variation K hK hKD
  obtain ⟨Cψ, hψ, _⟩ := h.regularCenter.localBV.psi_variation K hK hKD
  have hclam := h.regularCenter.continuous_lam.mono hKD
  obtain ⟨d, hd⟩ := hK.exists_bound_of_continuousOn hclam
  have hsub : Icc c d ⊆ Ioi 0 := fun x hx => hc.trans_le hx.1
  obtain ⟨L, hL⟩ := ((contDiffOn_id.inv (fun x hx => ne_of_gt hx)).mono hsub
    : ContDiffOn ℝ 1 (fun x : ℝ => x⁻¹) (Icc c d)).exists_lipschitzOnWith
      (by decide) (convex_Icc _ _) isCompact_Icc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [uIcc_of_le hab] using (h.dvpsi_terminal_ac hab ha hb).continuousOn)
  let D : ℝ≥0∞ := ENNReal.ofReal M + ENNReal.ofReal Cψ
  let E : ℝ≥0∞ := D * (L * ENNReal.ofReal Clam) +
    ENNReal.ofReal c⁻¹ * ENNReal.ofReal Cψ
  have hE : E ≠ ⊤ := by dsimp [E, D]; finiteness
  refine ⟨E.toReal, fun u hu => ?_⟩
  have hψu := hψ u u 0 (hu.2.trans_lt hb).le (hseg u hu)
  have hlamu := hlam u u 0 (hu.2.trans_lt hb).le (hseg u hu)
  have hnum (v : ℝ) (hv : v ∈ Icc u 0) : ‖S.dvpsi u v‖ₑ ≤ D := by
    have hdv := eVariationOn.edist_le (S.dvpsi u) hv
      (right_mem_Icc.mpr (hu.2.trans_lt hb).le)
    calc
      _ ≤ ‖S.dvpsi u 0‖ₑ + edist (S.dvpsi u v) (S.dvpsi u 0) := by
        simpa [edist_eq_enorm_sub] using
          enorm_add_le (S.dvpsi u 0) (S.dvpsi u v - S.dvpsi u 0)
      _ ≤ D := by
        apply add_le_add ?_ (hdv.trans hψu)
        simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
          ENNReal.ofReal_le_ofReal (hM u hu)
  have hmaps : MapsTo (S.lam u) (Icc u 0) (Icc c d) := by
    intro v hv
    have hkv := hseg u hu (show (u, v) ∈ outSeg u u 0 from ⟨rfl, hv⟩)
    exact ⟨(he (u, v) hkv).1,
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hd (u, v) hkv)⟩
  have hinv (v : ℝ) (hv : v ∈ Icc u 0) : ‖(S.lam u v)⁻¹‖ₑ ≤ ENNReal.ofReal c⁻¹ := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr (hc.trans_le (hmaps hv).1))]
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ hc (hmaps hv).1)
  have hiv := hL.comp_eVariationOn_le hmaps
  have hprod := eVariationOn_fun_mul_le hnum hinv
  change eVariationOn (fun v => S.dvpsi u v / S.lam u v) (Icc u 0) ≤ _
  simp only [div_eq_mul_inv]
  calc
    _ ≤ D * eVariationOn (fun v => (S.lam u v)⁻¹) (Icc u 0) +
        ENNReal.ofReal c⁻¹ * eVariationOn (S.dvpsi u) (Icc u 0) := hprod
    _ ≤ E := by
      dsimp [E]
      gcongr
      · exact hiv.trans (by gcongr)
    _ = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hE).symm

/-- Every proper cone has finite outgoing variation. Paper `e1a0fd5`,
`eq:outgoing-variation`, line 1001. -/
theorem outgoingVariation_ne_top {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    S.outgoingVariation u ≠ ⊤ := by
  obtain ⟨C, hC⟩ := h.outgoingVariation_locally_bounded le_rfl hu hu0
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC u ⟨le_rfl, le_rfl⟩)

end StandingFull

end AcExtensionPrinciple

end
