module

public import AcExtensionPrinciple.Observability.PropA4Operator

/-!
# Pointwise weighted inversion for the concrete exterior operator

Paper `e1a0fd5`, lines 1742–1747 and 1777–1779. Compactness supplies the
finite weighted norm of a continuous input; the concrete contraction
bound then controls it by twice the weighted norm of its residual.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set
open scoped Topology BoundedContinuousFunction

/-- A continuous function on the actual exterior domain is bounded by
twice its weighted Volterra residual. Continuity is the function-space
premise; the coefficient restriction holds at all three printed weights.
Paper `e1a0fd5`, lines 1742–1747 and 1777–1779. -/
theorem exterior_residual_bound {b T K P q B : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (hc : 1 / (4 * (2 - q) * (1 - q)) ≤ 1 / 2) (hB : 0 ≤ B)
    {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F (exteriorDomain h P))
    (hres : ∀ p ∈ exteriorDomain h P,
      |F p - triangleVolterra (fun p => chartPotential S p.1 p.2) F p.1 p.2| ≤
        B * S.r p.1 p.2 ^ q) :
    ∀ p ∈ exteriorDomain h P, |F p| ≤ 2 * B * S.r p.1 p.2 ^ q := by
  let : CompactSpace (exteriorDomain h P) :=
    isCompact_iff_compactSpace.mp (isCompact_exteriorDomain h)
  have hr : Continuous (fun p : exteriorDomain h P => S.r p.val.1 p.val.2) :=
    (h.continuous_r.mono (fun _ hp => hp.1)).domRestrict
  have hrq : Continuous (fun p : exteriorDomain h P => S.r p.val.1 p.val.2 ^ q) :=
    hr.rpow_const (fun p => Or.inl (exteriorDomain_interior h hP p.property).2.ne')
  let f : exteriorDomain h P →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun p => F p.val / S.r p.val.1 p.val.2 ^ q,
      hF.domRestrict.div hrq (fun p => (Real.rpow_pos_of_pos
        (exteriorDomain_interior h hP p.property).2 q).ne')⟩
  have hf (p : exteriorDomain h P) : ‖f p‖ = |F p.val| / S.r p.val.1 p.val.2 ^ q := by
    change ‖F p.val / S.r p.val.1 p.val.2 ^ q‖ = _
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (exteriorDomain_interior h hP p.property).2 q)]
  have hbound : ∀ p ∈ exteriorDomain h P, |F p| ≤ ‖f‖ * S.r p.1 p.2 ^ q := by
    intro p hp
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (exteriorDomain_interior h hP hp).2 q)).mp
      (by rw [← hf ⟨p, hp⟩]; exact f.norm_coe_le_norm _)
  let c := 1 / (4 * (2 - q) * (1 - q))
  have hc0 : 0 ≤ c := by
    dsimp [c]
    apply div_nonneg (by norm_num)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hpoint : ∀ p : exteriorDomain h P, ‖f p‖ ≤ B + c * ‖f‖ := by
    intro p
    have hrpos := Real.rpow_pos_of_pos (exteriorDomain_interior h hP p.property).2 q
    have hvol := exterior_volterra_weighted_bound h hP hmass hq (norm_nonneg f)
      hF hbound p.property
    have hsum : |F p.val| ≤ (B + c * ‖f‖) * S.r p.val.1 p.val.2 ^ q := by
      calc
        _ = |(F p.val - triangleVolterra (fun p => chartPotential S p.1 p.2)
              F p.val.1 p.val.2) + triangleVolterra (fun p => chartPotential S p.1 p.2)
              F p.val.1 p.val.2| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hres _ p.property) hvol)
        _ = _ := by dsimp [c]; ring
    rw [hf]
    exact (div_le_iff₀ hrpos).mpr hsum
  have hnorm : ‖f‖ ≤ B + c * ‖f‖ :=
    (BoundedContinuousFunction.norm_le (add_nonneg hB (mul_nonneg hc0 (norm_nonneg f)))).mpr
      hpoint
  have hnorm2 : ‖f‖ ≤ 2 * B := by
    have hmul := mul_le_mul_of_nonneg_right hc (norm_nonneg f)
    change c * ‖f‖ ≤ (1 / 2) * ‖f‖ at hmul
    linarith
  intro p hp
  exact (hbound p hp).trans (mul_le_mul_of_nonneg_right hnorm2
    (Real.rpow_nonneg (exteriorDomain_interior h hP hp).2.le q))

end PropA4
end AcExtensionPrinciple

end
