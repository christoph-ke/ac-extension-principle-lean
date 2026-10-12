module

public import AcExtensionPrinciple.Observability.FromSolution
public import AcExtensionPrinciple.Gauge.ContinuationMap

/-!
# A regular linear extension of the incoming inverse coordinate

Paper `e1a0fd5`, `equations.tex` line 1460.
The slope on earlier labels is exactly the Jacobian at the first entering
ray. Matching derivatives gives C¹ regularity and preserves Jacobian BV.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Extend the inverse incoming coordinate below its first entry time,
using its derivative at the join. Paper `e1a0fd5`, line 1460, regular
extension as in line 1422. -/
@[expose] noncomputable def incomingLinearExtension (f d : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then f 0 + d 0 * t else f t

/-- The inverse incoming Jacobian is constant on the extension. Paper
`e1a0fd5`, line 1460, regular extension as in line 1422. -/
@[expose] noncomputable def incomingExtensionJacobian (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  d (max t 0)

/-- Earlier labels have precisely the requested affine coordinate.
Paper `e1a0fd5`, line 1460, regular extension as in line 1422. -/
theorem incomingLinearExtension_of_nonpos (f d : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0) :
    incomingLinearExtension f d t = f 0 + d 0 * t := by
  simp [incomingLinearExtension, ht]

/-- Entering labels retain their original inverse coordinate, including
the join. Paper `e1a0fd5`, lines 1460–1465. -/
theorem incomingLinearExtension_of_nonneg (f d : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    incomingLinearExtension f d t = f t := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simp [incomingLinearExtension]
  · simp [incomingLinearExtension, not_le.mpr h]

/-- The reflected continuation map is the incoming linear extension.
Paper `e1a0fd5`, lines 1422 and 1460. -/
theorem incomingLinearExtension_reflection (f d : ℝ → ℝ) (t : ℝ) :
    incomingLinearExtension f d t =
      -continuationMap (fun x => -f (-x) / 2) (fun x => d (-x) / 2) (-t) := by
  rcases le_total t 0 with ht | ht
  · rw [incomingLinearExtension_of_nonpos f d ht,
      continuationMap_of_nonneg _ _ (neg_nonneg.mpr ht)]
    simp only [neg_zero]
    ring
  · rw [incomingLinearExtension_of_nonneg f d ht,
      continuationMap_of_nonpos _ _ (neg_nonpos.mpr ht)]
    simp only [neg_neg]
    ring

/-- Matching the entry Jacobian yields differentiability on the entire
earlier-label extension. Ordinary entry derivatives are sufficient here;
the domain-relative version follows by the same matching argument.
Paper `e1a0fd5`, lines 1422 and 1460–1465. -/
theorem hasDerivAt_incomingLinearExtension {f d : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (d t) t) :
    ∀ t ∈ Iic T, HasDerivAt (incomingLinearExtension f d)
      (incomingExtensionJacobian d t) t := by
  have hr : ∀ x ∈ Icc (-T) 0,
      HasDerivAt (fun x => -f (-x) / 2) (d (-x) / 2) x := by
    intro x hx
    have hd := (((hf (-x) ⟨neg_nonneg.mpr hx.2,
      by linarith [hx.1]⟩).comp x (hasDerivAt_id x).neg).neg).div_const 2
    convert hd using 1 <;> simp [Function.comp_def]
  intro t ht
  have he := hasDerivAt_continuationMap (neg_nonpos.mpr hT) hr (-t)
    (by change -T ≤ -t; exact neg_le_neg ht)
  have hd := ((he.comp t (hasDerivAt_id t).neg).neg)
  have hfun : (fun x => -continuationMap (fun x => -f (-x) / 2)
      (fun x => d (-x) / 2) (-x)) = incomingLinearExtension f d :=
    funext (fun x => (incomingLinearExtension_reflection f d x).symm)
  change HasDerivAt (fun x => -continuationMap (fun x => -f (-x) / 2)
    (fun x => d (-x) / 2) (-x)) _ t at hd
  rw [hfun] at hd
  convert hd using 1
  unfold incomingExtensionJacobian continuationDerivative
  have hmin : -(min (-t) 0) = max t 0 := by
    rcases le_total t 0 with ht | ht
    · rw [min_eq_right (neg_nonneg.mpr ht), max_eq_right ht, neg_zero]
    · rw [min_eq_left (neg_nonpos.mpr ht), max_eq_left ht, neg_neg]
  simp only [hmin]
  ring

/-- The matched Jacobian is continuous through the first entering ray.
Paper `e1a0fd5`, line 1460, regular extension as in line 1422. -/
theorem continuousOn_incomingExtensionJacobian {d : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ContinuousOn d (Icc 0 T)) :
    ContinuousOn (incomingExtensionJacobian d) (Iic T) := by
  exact hd.comp (continuous_id.max continuous_const).continuousOn
    (fun _ ht => ⟨le_max_right _ _, max_le ht hT⟩)

/-- The positive entry Jacobian remains positive on earlier labels.
Paper `e1a0fd5`, lines 1460–1465. -/
theorem incomingExtensionJacobian_pos {d : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, 0 < d t) :
    ∀ t ∈ Iic T, 0 < incomingExtensionJacobian d t :=
  fun _ ht => hd _ ⟨le_max_right _ _, max_le ht hT⟩

/-- Constant extension preserves the BV required for the weighted scalar
derivative fields. Paper `e1a0fd5`, lines 1441–1443 and 1460–1465. -/
theorem boundedVariation_incomingExtensionJacobian {d : ℝ → ℝ} {a T : ℝ}
    (hT : 0 ≤ T) (hd : BoundedVariationOn d (Icc 0 T)) :
    BoundedVariationOn (incomingExtensionJacobian d) (Icc a T) := by
  apply ne_top_of_le_ne_top hd
  exact eVariationOn.comp_le_of_monotoneOn d _
    (fun _ _ _ _ h => max_le_max_right 0 h)
    (fun _ ht => ⟨le_max_right _ _, max_le ht.2 hT⟩)

/-- Strict increase of the matched extension follows from positive
Jacobian; no extra source hypothesis is used. Paper `e1a0fd5`,
lines 1460–1465 and the extension at line 1422. -/
theorem strictMonoOn_incomingLinearExtension {f d : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (d t) t)
    (hd : ∀ t ∈ Icc 0 T, 0 < d t) :
    StrictMonoOn (incomingLinearExtension f d) (Iic T) := by
  have he := hasDerivAt_incomingLinearExtension hT hf
  apply strictMonoOn_of_deriv_pos (convex_Iic T)
  · exact fun x hx => (he x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [(he x (interior_subset hx)).deriv]
    exact incomingExtensionJacobian_pos hT hd x (interior_subset hx)

end AcExtensionPrinciple

end
