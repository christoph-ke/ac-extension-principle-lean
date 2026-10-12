module

public import AcExtensionPrinciple.Solution.PositiveAC

/-!
# AC restriction of a separated rough datum

Paper `e1a0fd5`, `equations.tex` lines 731–737,
`eq:separated-datum-derivative`. Monotone Lipschitz reparametrization preserves
absolute continuity of the one-dimensional initial datum.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Monotone maps preserve disjoint unordered half-open intervals.
Paper `e1a0fd5`, calculus input to lines 731–737. -/
theorem cylinder_disjoint_uIoc_image {g : ℝ → ℝ} {a b x y z w : ℝ}
    (hg : MonotoneOn g (uIcc a b))
    (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b)
    (hz : z ∈ uIcc a b) (hw : w ∈ uIcc a b)
    (hd : Disjoint (uIoc x y) (uIoc z w)) :
    Disjoint (uIoc (g x) (g y)) (uIoc (g z) (g w)) := by
  have hmin {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) :
      g (min s t) = min (g s) (g t) ∧ g (max s t) = max (g s) (g t) := by
    rcases le_total s t with hst | hts
    · simp [min_eq_left hst, max_eq_right hst, min_eq_left (hg hs ht hst),
        max_eq_right (hg hs ht hst)]
    · simp [min_eq_right hts, max_eq_left hts, min_eq_right (hg ht hs hts),
        max_eq_left (hg ht hs hts)]
  have hmem {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) :
      min s t ∈ uIcc a b ∧ max s t ∈ uIcc a b := by
    rcases le_total s t with hst | hts
    · simpa only [min_eq_left hst, max_eq_right hst] using And.intro hs ht
    · simpa only [min_eq_right hts, max_eq_left hts] using And.intro ht hs
  rw [uIoc, uIoc, Ioc_disjoint_Ioc] at hd ⊢
  have hxy := hmem hx hy
  have hzw := hmem hz hw
  have hd' := hg (hmem hxy.2 hzw.2).1 (hmem hxy.1 hzw.1).2 hd
  simpa only [(hmin hxy.2 hzw.2).1, (hmin hxy.1 hzw.1).2,
    (hmin hx hy).1, (hmin hx hy).2, (hmin hz hw).1, (hmin hz hw).2] using hd'

/-- An AC datum stays AC under a monotone Lipschitz cylinder coordinate.
Paper `e1a0fd5`, lines 731–737, `eq:cylinder-time`. -/
theorem cylinder_ac_comp_monotone_lipschitz {f g : ℝ → ℝ} {a b c d : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f c d)
    (hg : MonotoneOn g (uIcc a b)) (hL : LipschitzOnWith K g (uIcc a b))
    (hm : MapsTo g (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (fun x => f (g x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro eps heps
  obtain ⟨delta, hdelta, hsmall⟩ := hf eps heps
  refine ⟨delta / ((K : ℝ) + 1), by positivity, ?_⟩
  intro E hE hlength
  let F : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => (g (E.2 i).1, g (E.2 i).2))
  have hF : F ∈ AbsolutelyContinuousOnInterval.disjWithin c d := by
    refine ⟨fun i hi => ⟨hm (hE.1 i hi).1, hm (hE.1 i hi).2⟩, ?_⟩
    intro i hi j hj hij
    exact cylinder_disjoint_uIoc_image hg (hE.1 i hi).1 (hE.1 i hi).2
      (hE.1 j hj).1 (hE.1 j hj).2 (hE.2 hi hj hij)
  apply hsmall F hF
  have hb : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) ≤
      ((K : ℝ) + 1) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact (hL.dist_le_mul _ (hE.1 i hi).1 _ (hE.1 i hi).2).trans
      (by nlinarith [(show 0 ≤ dist (E.2 i).1 (E.2 i).2 from dist_nonneg)])
  apply hb.trans_lt
  simpa only [mul_comm] using
    (lt_div_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp hlength

/-- The linear transport representation yields AC of (∂ᵥψ/λ)_b.
The smooth remainder and reciprocal-expansion regularity are helper premises;
these are the off-axis transport/decomposition conclusions at lines 731–737.
Paper `e1a0fd5`, `eq:separated-datum-derivative`, lines 731–737. -/
theorem cylinder_P_ac_of_transport {ui a b : ℝ} {S : SSFields}
    {v L R P : ℝ → ℝ} {Kv KL KR : ℝ≥0}
    (hdata : AbsolutelyContinuousOnInterval (S.dvpsi ui) ui 0)
    (hv : MonotoneOn v (uIcc a b)) (hvL : LipschitzOnWith Kv v (uIcc a b))
    (hvD : MapsTo v (uIcc a b) (uIcc ui 0))
    (hL : LipschitzOnWith KL L (uIcc a b)) (hL0 : ∀ x ∈ uIcc a b, 0 < L x)
    (hR : LipschitzOnWith KR R (uIcc a b))
    (htransport : ∀ x ∈ uIcc a b, P x = S.dvpsi ui (v x) / L x + R x) :
    AbsolutelyContinuousOnInterval P a b := by
  have hi := cylinder_ac_comp_monotone_lipschitz hdata hv hvL hvD
  have hli := positive_ac_inv hL.absolutelyContinuousOnInterval hL0
  apply ((hi.fun_mul hli).fun_add hR.absolutelyContinuousOnInterval).congr
  intro x hx
  simpa only [div_eq_mul_inv] using (htransport x hx).symm

end AcExtensionPrinciple

end
