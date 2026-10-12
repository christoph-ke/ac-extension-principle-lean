module

public import AcExtensionPrinciple.Redundancy.Geometry
public import Mathlib.Topology.Order.ProjIcc

/-!
# Joint continuity from separate continuity and one monotone coordinate
Paper commit `e1a0fd5`, `equations.tex` lines 66–84 and 220–275, `eq:mass`.
This elementary helper avoids assuming bounded mass integrands near the axis.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Separate continuity and antitonicity in the first coordinate give joint continuity. The
hypotheses will be discharged by the characteristic mass primitives and their signs. Paper
`e1a0fd5`, `eq:mass`, lines 66–84 and 222. -/
theorem q1_joint_continuous_of_antitone {f : ℝ → ℝ → ℝ}
    (hu : ∀ v, Continuous (fun u => f u v))
    (hv : ∀ u, Continuous (f u))
    (hm : ∀ v, Antitone (fun u => f u v)) :
    Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp (hu p.2).continuousAt (ε / 2)
    (by positivity)
  let a := p.1 - δ / 2
  let b := p.1 + δ / 2
  have hap : a < p.1 := by dsimp [a]; linarith
  have hpb : p.1 < b := by dsimp [b]; linarith
  have hfa : dist (f a p.2) (f p.1 p.2) < ε / 2 := by
    apply hδf
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hap)]
    dsimp [a]
    linarith
  have hfb : dist (f b p.2) (f p.1 p.2) < ε / 2 := by
    apply hδf
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hpb)]
    dsimp [b]
    linarith
  obtain ⟨δa, hδa, hδaf⟩ := Metric.continuousAt_iff.mp (hv a).continuousAt (ε / 2)
    (by positivity)
  obtain ⟨δb, hδb, hδbf⟩ := Metric.continuousAt_iff.mp (hv b).continuousAt (ε / 2)
    (by positivity)
  refine ⟨min (δ / 2) (min δa δb), lt_min (by positivity) (lt_min hδa hδb), ?_⟩
  intro q hq
  have hqu : dist q.1 p.1 < δ / 2 := (show dist q.1 p.1 ≤ dist q p from by
      rw [Prod.dist_eq]
      exact le_max_left _ _).trans_lt
    (hq.trans_le (min_le_left _ _))
  have hqva : dist q.2 p.2 < δa := (show dist q.2 p.2 ≤ dist q p from by
      rw [Prod.dist_eq]
      exact le_max_right _ _).trans_lt
    (hq.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hqvb : dist q.2 p.2 < δb := (show dist q.2 p.2 ≤ dist q p from by
      rw [Prod.dist_eq]
      exact le_max_right _ _).trans_lt
    (hq.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have haqu : a ≤ q.1 := by
    rw [Real.dist_eq, abs_lt] at hqu
    dsimp [a]
    linarith [hqu.1]
  have hqub : q.1 ≤ b := by
    rw [Real.dist_eq, abs_lt] at hqu
    dsimp [b]
    linarith [hqu.2]
  have hqa := hδaf hqva
  have hqb := hδbf hqvb
  have hlow := hm q.2 hqub
  have hupp := hm q.2 haqu
  rw [Real.dist_eq, abs_lt] at hfa hfb hqa hqb ⊢
  constructor <;> linarith

/-- On a closed rectangle, continuous characteristic restrictions and antitonicity in the incoming
coordinate imply joint continuity. Clamping extends the restrictions to all real labels. Paper
`e1a0fd5`, `eq:mass`, lines 66–84 and 220–275. -/
theorem q1_rectangle_continuous_of_antitone {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hu : ∀ v ∈ Icc c d, ContinuousOn (fun u => f u v) (Icc a b))
    (hv : ∀ u ∈ Icc a b, ContinuousOn (f u) (Icc c d))
    (hm : ∀ v ∈ Icc c d, AntitoneOn (fun u => f u v) (Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc a b ×ˢ Icc c d) := by
  let C := fun x : ℝ => max a (min b x)
  let D := fun x : ℝ => max c (min d x)
  have hC : Continuous C := continuous_const.max (continuous_const.min continuous_id)
  have hD : Continuous D := continuous_const.max (continuous_const.min continuous_id)
  have hCm (x : ℝ) : C x ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hDm (x : ℝ) : D x ∈ Icc c d :=
    ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩
  have hCmono : Monotone C := monotone_const.max (monotone_const.min monotone_id)
  have hc := q1_joint_continuous_of_antitone (f := fun u v => f (C u) (D v))
    (fun v => (hu (D v) (hDm v)).comp_continuous hC hCm)
    (fun u => (hv (C u) (hCm u)).comp_continuous hD hDm)
    (fun v u₁ u₂ hu₁₂ => hm (D v) (hDm v) (hCm u₁) (hCm u₂) (hCmono hu₁₂))
  apply hc.continuousOn.congr
  intro p hp
  simp only [C, D, min_eq_right hp.1.2, max_eq_right hp.1.1,
    min_eq_right hp.2.2, max_eq_right hp.2.1]

end AcExtensionPrinciple

end
