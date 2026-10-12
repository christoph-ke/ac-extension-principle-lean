module

public import AcExtensionPrinciple.Redundancy.RestoreConventions

/-!
# Expansion right-continuity conventions are redundant
Paper commit `e1a0fd5`, `equations.tex` lines 220–275, Q1.
Restrictions of the retained joint continuity give both conventions.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Restrict joint continuity to any outgoing domain section. Paper `e1a0fd5`, lines 220–275,
Luk–Oh BV representative convention. -/
theorem q1_right_cont_out_of_continuous {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p => f p.1 p.2) D) {p : ℝ × ℝ} (hp : p ∈ D) :
    ContinuousWithinAt (f p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ D} p.2 := by
  exact (hf p hp).comp_of_eq
    ((continuous_const.prodMk continuous_id).continuousWithinAt :
      ContinuousWithinAt (fun w : ℝ => (p.1, w)) _ p.2)
    (fun _ hw => hw.2) rfl

/-- Restrict joint continuity to any incoming domain section. Paper `e1a0fd5`, lines 220–275,
Luk–Oh BV representative convention. -/
theorem q1_right_cont_in_of_continuous {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p => f p.1 p.2) D) {p : ℝ × ℝ} (hp : p ∈ D) :
    ContinuousWithinAt (fun u => f u p.2) {u | p.1 ≤ u ∧ (u, p.2) ∈ D} p.1 := by
  exact (hf p hp).comp_of_eq
    ((continuous_id.prodMk continuous_const).continuousWithinAt :
      ContinuousWithinAt (fun u : ℝ => (u, p.2)) _ p.1)
    (fun _ hu => hu.2) rfl

/-- The λ right-continuity field follows from the remaining joint continuity. Paper `e1a0fd5`,
lines 220–275, Luk–Oh pp. 1608–1609. -/
theorem lam_right_cont_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_lam_right_cont ui S) :
    ∀ p ∈ pastTriangle ui,
      ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2 :=
  fun _ hp => q1_right_cont_out_of_continuous h.continuous_lam hp

/-- The ν right-continuity field follows from the remaining joint continuity. Paper `e1a0fd5`,
lines 220–275, Luk–Oh pp. 1608–1609. -/
theorem nu_right_cont_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_nu_right_cont ui S) :
    ∀ p ∈ pastTriangle ui, ContinuousWithinAt (fun u => S.nu u p.2)
      {u | p.1 ≤ u ∧ (u, p.2) ∈ pastTriangle ui} p.1 :=
  fun _ hp => q1_right_cont_in_of_continuous h.continuous_nu hp

end AcExtensionPrinciple

end
