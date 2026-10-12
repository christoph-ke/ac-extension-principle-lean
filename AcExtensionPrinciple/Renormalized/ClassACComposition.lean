module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Tactic

/-!
# Absolute continuity under an increasing Lipschitz change of parameter

This module proves the absolute-continuity composition helper for the radius profile.
Paper `e1a0fd5`, `equations.tex` lines 1006–1015.
This is the composition needed for the inverse-radius coordinate.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A monotone change of parameter preserves disjoint half-open intervals.
Paper `e1a0fd5`, lines 1006–1015, inverse-radius AC calculus. -/
theorem monotoneOn_disjoint_uIoc {g : ℝ → ℝ} {s : Set ℝ} {x y z t : ℝ}
    (hg : MonotoneOn g s) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (ht : t ∈ s)
    (hd : Disjoint (uIoc x y) (uIoc z t)) :
    Disjoint (uIoc (g x) (g y)) (uIoc (g z) (g t)) := by
  have hmin_mem {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) : min a b ∈ s := by
    rcases le_total a b with h | h
    · simpa only [min_eq_left h] using ha
    · simpa only [min_eq_right h] using hb
  have hmax_mem {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) : max a b ∈ s := by
    rcases le_total a b with h | h
    · simpa only [max_eq_right h] using hb
    · simpa only [max_eq_left h] using ha
  have hmin {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) : g (min a b) = min (g a) (g b) := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, min_eq_left (hg ha hb h)]
    · rw [min_eq_right h, min_eq_right (hg hb ha h)]
  have hmax {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) : g (max a b) = max (g a) (g b) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (hg ha hb h)]
    · rw [max_eq_left h, max_eq_left (hg hb ha h)]
  simp only [uIoc, Ioc_disjoint_Ioc] at hd ⊢
  have he := hg (hmin_mem (hmax_mem hx hy) (hmax_mem hz ht))
    (hmax_mem (hmin_mem hx hy) (hmin_mem hz ht)) hd
  simpa only [hmin (hmax_mem hx hy) (hmax_mem hz ht),
    hmax (hmin_mem hx hy) (hmin_mem hz ht), hmin hx hy, hmin hz ht,
    hmax hx hy, hmax hz ht] using he

/-- An AC profile composed with a monotone Lipschitz parameter remains AC.
Paper `e1a0fd5`, lines 1006–1015, construction of the radius profile. -/
theorem ac_comp_monotone_lipschitz {f g : ℝ → ℝ} {a b c d : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : MonotoneOn g (uIcc c d)) (hL : LipschitzOnWith K g (uIcc c d))
    (hmaps : MapsTo g (uIcc c d) (uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun x => f (g x)) c d := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  have hK : 0 < (K : ℝ) + 1 := by positivity
  refine ⟨δ / ((K : ℝ) + 1), div_pos hδ hK, ?_⟩
  intro E hE hlen
  let T : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => (g (E.2 i).1, g (E.2 i).2))
  have hT : T ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
    refine ⟨fun i hi => ⟨hmaps (hE.1 i hi).1, hmaps (hE.1 i hi).2⟩, ?_⟩
    intro i hi j hj hij
    exact monotoneOn_disjoint_uIoc hg (hE.1 i hi).1 (hE.1 i hi).2
      (hE.1 j hj).1 (hE.1 j hj).2 (hE.2 hi hj hij)
  apply hbound T hT
  have hdist : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) ≤
      (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hL.dist_le_mul _ (hE.1 i hi).1 _ (hE.1 i hi).2
  have hs : 0 ≤ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 :=
    Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have hsmall := (lt_div_iff₀ hK).mp hlen
  exact hdist.trans_lt (by nlinarith)

end AcExtensionPrinciple

end
