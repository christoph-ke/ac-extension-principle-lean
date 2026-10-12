module

public import AcExtensionPrinciple.GeometricBounds.Kappa
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Complete incoming scalar flux bounds

Paper `e1a0fd5`, `eq:incoming-flux-identity`,
`eq:incoming-flux-bound` (lines 334–341 and 360).
The logarithmic identity bounds each regular truncation. Monotone
convergence on an exhaustion controls the whole ray, including v = 0.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Uniform bounds on truncations control the lower integral on an open interval.
Paper `e1a0fd5`, `eq:incoming-flux-bound`, lines 341, 360 (monotone convergence). -/
theorem lintegral_Ioo_le_of_truncations {a b : ℝ} {f : ℝ → ℝ≥0∞} {C : ℝ≥0∞}
    (hab : a < b) (hbound : ∀ c ∈ Ico a b, (∫⁻ x in Ioo a c, f x) ≤ C) :
    (∫⁻ x in Ioo a b, f x) ≤ C := by
  let c : ℕ → ℝ := fun n => b - (b - a) / ((n : ℝ) + 2)
  have hc : ∀ n, c n ∈ Ico a b := by
    intro n
    have hn : 1 ≤ (n : ℝ) + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hn0 := zero_lt_one.trans_le hn
    constructor
    · dsimp [c]
      have hd : (b - a) / ((n : ℝ) + 2) ≤ b - a :=
        div_le_self (sub_pos.mpr hab).le hn
      linarith
    · exact sub_lt_self _ (div_pos (sub_pos.mpr hab) hn0)
  have ht : Tendsto c atTop (𝓝 b) := by
    have hd : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2
        (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [c] using tendsto_const_nhds.sub hd
  have he : Ioo a b = ⋃ n, Ioo a (c n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := (ht.eventually (Ioi_mem_nhds hx.2)).exists
      exact mem_iUnion.mpr ⟨n, hx.1, hn⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact ⟨hn.1, hn.2.trans (hc n).2⟩
  have hd : Directed (· ⊆ ·) (fun n => Ioo a (c n)) := by
    intro n m
    rcases le_total (c n) (c m) with hnm | hmn
    · exact ⟨m, Ioo_subset_Ioo_right hnm, Subset.rfl⟩
    · exact ⟨n, Subset.rfl, Ioo_subset_Ioo_right hmn⟩
  rw [he, setLIntegral_iUnion_of_directed f hd]
  exact iSup_le (fun n => hbound (c n) (hc n))

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming flux density is nonnegative away from the regular axis.
Paper `e1a0fd5`, `eq:incoming-flux-bound`, lines 334–341. -/
theorem incomingFlux_nonneg {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    0 ≤ S.incomingFlux u v :=
  mul_nonneg (div_nonneg (h.r_pos hp huv).le (neg_pos.mpr (h.nu_neg hp)).le)
    (sq_nonneg _)

/-- Every regular incoming truncation has the explicit uniform flux bound.
Paper `e1a0fd5`, `eq:incoming-flux-identity`, lines 334–339, 360. -/
theorem partial_incoming_flux_le {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    (∫ s in ui..u, S.incomingFlux s v) ≤
      Bstar ui S + Real.log (1 / initialGap ui S) := by
  have hi := h.incoming_flux_identity hp.1 le_rfl hp.2.1 huv hp.2.2.2
  have hpi : (ui, v) ∈ pastTriangle ui :=
    ⟨le_rfl, h.initial_negative, hp.1.trans hp.2.2.1, hp.2.2.2⟩
  have hu := Real.log_le_log (h.kappa_pos hpi) (h.kappa_upper hpi)
  have hl := Real.log_le_log (Real.exp_pos (-Bstar ui S)) (h.kappa_lower hp)
  rw [Real.log_exp] at hl
  linarith [hi.2]

/-- G6: the complete incoming scalar flux bound, including the terminal ray.
Paper `e1a0fd5`, `eq:incoming-flux-bound`, `eq:incoming-flux-identity`, lines 334–341, 360. -/
theorem incoming_flux_le {v : ℝ} (hv : v ∈ Ioc ui 0) :
    (∫⁻ u in Ioo ui v, ENNReal.ofReal (S.incomingFlux u v)) ≤
      ENNReal.ofReal (Bstar ui S + Real.log (1 / initialGap ui S)) := by
  apply lintegral_Ioo_le_of_truncations hv.1
  intro u hu
  have hp : (u, v) ∈ pastTriangle ui :=
    ⟨hu.1, hu.2.trans_le hv.2, hu.2.le, hv.2⟩
  have hi := h.incoming_flux_identity hu.1 le_rfl hp.2.1 hu.2 hv.2
  rw [← ofReal_intervalIntegral hu.1 hi.1 (fun s hs =>
    h.incomingFlux_nonneg
      ⟨hs.1.le, hs.2.trans hp.2.1, (hs.2.trans hu.2).le, hv.2⟩ (hs.2.trans hu.2))]
  exact ENNReal.ofReal_le_ofReal (h.partial_incoming_flux_le hp hu.2)

end StandingFull

end AcExtensionPrinciple

end
