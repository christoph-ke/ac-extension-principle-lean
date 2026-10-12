module

public import AcExtensionPrinciple.Observability.PropA4ExteriorDomain
public import AcExtensionPrinciple.Observability.Neumann

/-!
# The concrete weighted exterior Volterra operator

Paper `e1a0fd5`, lines 1742–1755. Conjugating by the radius power
realizes the weighted norm on bounded continuous functions on the
invariant exterior domain.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set
open scoped Topology BoundedContinuousFunction

/-- Lift a bounded exterior function with its radius weight; the
values outside the invariant domain are immaterial to its operator.
Paper `e1a0fd5`, lines 1742–1747. -/
@[expose] noncomputable def weightedExteriorLift {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (P q : ℝ) (f : exteriorDomain h P →ᵇ ℝ) : ℝ × ℝ → ℝ := by
  classical
  exact fun p => if hp : p ∈ exteriorDomain h P then S.r p.1 p.2 ^ q * f ⟨p, hp⟩ else 0

/-- On the exterior domain the lift has its defining radius weight.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedExteriorLift_eq {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (f : exteriorDomain h P →ᵇ ℝ)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    weightedExteriorLift h P q f p = S.r p.1 p.2 ^ q * f ⟨p, hp⟩ := by
  simp [weightedExteriorLift, hp]

/-- Weighted exterior lifts are continuous on the domain.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedExteriorLift_continuous {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (f : exteriorDomain h P →ᵇ ℝ) :
    ContinuousOn (weightedExteriorLift h P q f) (exteriorDomain h P) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hr : Continuous (fun p : exteriorDomain h P => S.r p.val.1 p.val.2) :=
    (h.continuous_r.mono (fun _ hp => hp.1)).domRestrict
  have hc := (hr.rpow_const (p := q) (fun p => Or.inl
    (exteriorDomain_interior h hP p.property).2.ne')).mul f.continuous
  convert hc using 1
  funext p
  exact weightedExteriorLift_eq h f p.property

/-- The norm of the unweighted input controls its lifted radius weight.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedExteriorLift_bound {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (f : exteriorDomain h P →ᵇ ℝ)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    |weightedExteriorLift h P q f p| ≤ ‖f‖ * S.r p.1 p.2 ^ q := by
  have hr := (exteriorDomain_interior h hP hp).2
  rw [weightedExteriorLift_eq h f hp, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr q)]
  simpa only [mul_comm, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left (f.norm_coe_le_norm ⟨p, hp⟩) (Real.rpow_nonneg hr.le q)

/-- The weighted operator value on the exterior domain.
Paper `e1a0fd5`, lines 1742–1747. -/
@[expose] noncomputable def weightedVolterraValue {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (P q : ℝ) (f : exteriorDomain h P →ᵇ ℝ)
    (p : exteriorDomain h P) : ℝ :=
  S.r p.val.1 p.val.2 ^ (-q) * triangleVolterra (fun p => chartPotential S p.1 p.2)
    (weightedExteriorLift h P q f) p.val.1 p.val.2

/-- The weighted operator output is continuous.
Paper `e1a0fd5`, lines 1742–1755. -/
theorem weightedVolterraValue_continuous {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (f : exteriorDomain h P →ᵇ ℝ) :
    Continuous (weightedVolterraValue h P q f) := by
  have hr : Continuous (fun p : exteriorDomain h P => S.r p.val.1 p.val.2) :=
    (h.continuous_r.mono (fun _ hp => hp.1)).domRestrict
  exact (hr.rpow_const (p := -q) (fun p => Or.inl
    (exteriorDomain_interior h hP p.property).2.ne')).mul
    (exterior_volterra_continuous h hP (weightedExteriorLift_continuous h hP f)).domRestrict

/-- The concrete weighted output has the printed uniform norm bound.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedVolterraValue_bound {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (f : exteriorDomain h P →ᵇ ℝ) (p : exteriorDomain h P) :
    ‖weightedVolterraValue h P q f p‖ ≤ (1 / (4 * (2 - q) * (1 - q))) * ‖f‖ := by
  have hr := (exteriorDomain_interior h hP p.property).2
  have hb := exterior_volterra_weighted_norm_bound h hP hmass hq (norm_nonneg f)
    (weightedExteriorLift_continuous h hP f)
    (fun z hz => weightedExteriorLift_bound h hP f hz) p.property
  rw [weightedVolterraValue, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hr (-q)), Real.rpow_neg hr.le]
  simpa only [div_eq_mul_inv, mul_comm] using hb

/-- Package the weighted operator output as a bounded continuous
function. Paper `e1a0fd5`, lines 1742–1755. -/
@[expose] noncomputable def weightedVolterraMap {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (f : exteriorDomain h P →ᵇ ℝ) : exteriorDomain h P →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (weightedVolterraValue h P q f)
    (weightedVolterraValue_continuous h hP f) ((1 / (4 * (2 - q) * (1 - q))) * ‖f‖)
    (weightedVolterraValue_bound h hP hmass hq f)

/-- Weighted lifts preserve addition. Paper `e1a0fd5`, lines 1742–1755. -/
theorem weightedExteriorLift_add {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (f g : exteriorDomain h P →ᵇ ℝ) :
    weightedExteriorLift h P q (f + g) =
      weightedExteriorLift h P q f + weightedExteriorLift h P q g := by
  funext p
  by_cases hp : p ∈ exteriorDomain h P <;> simp [weightedExteriorLift, hp, mul_add]

/-- Weighted lifts preserve scalar multiplication. Paper `e1a0fd5`, lines 1742–1755. -/
theorem weightedExteriorLift_smul {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (c : ℝ) (f : exteriorDomain h P →ᵇ ℝ) :
    weightedExteriorLift h P q (c • f) = c • weightedExteriorLift h P q f := by
  funext p
  by_cases hp : p ∈ exteriorDomain h P <;>
    simp [weightedExteriorLift, hp, smul_eq_mul, mul_left_comm]

/-- The actual weighted Volterra operator as a continuous linear map.
Paper `e1a0fd5`, lines 1742–1755. -/
@[expose] noncomputable def weightedVolterraOperator {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) : (exteriorDomain h P →ᵇ ℝ) →L[ℝ] (exteriorDomain h P →ᵇ ℝ) := by
  let A : (exteriorDomain h P →ᵇ ℝ) →ₗ[ℝ] (exteriorDomain h P →ᵇ ℝ) := {
    toFun := weightedVolterraMap h hP hmass hq
    map_add' := by
      intro f g
      ext p
      change weightedVolterraValue h P q (f + g) p =
        weightedVolterraValue h P q f p + weightedVolterraValue h P q g p
      have htri := exteriorDomain_triangle h hP p.property
      have ht : 0 ≤ p.val.2 :=
        (mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le).trans p.property.2.1
      have hpoint := exteriorDomain_interior h hP p.property
      unfold weightedVolterraValue
      rw [weightedExteriorLift_add, triangleVolterra_add_on p.property.1.2.2.2
        (continuous_potential_on h (h.volterra_triangle_subset ht hpoint))
        ((weightedExteriorLift_continuous h hP f).mono htri)
        ((weightedExteriorLift_continuous h hP g).mono htri), mul_add]
    map_smul' := by
      intro c f
      ext p
      change weightedVolterraValue h P q (c • f) p = c * weightedVolterraValue h P q f p
      unfold weightedVolterraValue
      rw [weightedExteriorLift_smul, triangleVolterra_smul]
      ring }
  exact A.mkContinuous (1 / (4 * (2 - q) * (1 - q))) (fun f => by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (by
      apply div_nonneg (by norm_num)
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) (norm_nonneg f))).mpr
    exact weightedVolterraValue_bound h hP hmass hq f)

/-- Evaluation of the concrete weighted continuous linear operator.
Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedVolterraOperator_apply {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (f : exteriorDomain h P →ᵇ ℝ) (p : exteriorDomain h P) :
    weightedVolterraOperator h hP hmass hq f p = weightedVolterraValue h P q f p := rfl

/-- The concrete weighted operator has precisely the advertised norm
coefficient. Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedVolterraOperator_norm_le {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) :
    ‖weightedVolterraOperator h hP hmass hq‖ ≤ 1 / (4 * (2 - q) * (1 - q)) := by
  have hc : 0 ≤ 1 / (4 * (2 - q) * (1 - q)) :=
    div_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro f
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hc (norm_nonneg f))).mpr
  intro p
  rw [weightedVolterraOperator_apply]
  exact weightedVolterraValue_bound h hP hmass hq f p

/-- At each of the three weights used in the paper, the concrete
operator norm is at most `1/3`. Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedVolterraOperator_norm_le_third {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (hweight : q = 0 ∨ q = 1 / 2 ∨ q = -(1 / 2)) :
    ‖weightedVolterraOperator h hP hmass hq‖ ≤ 1 / 3 := by
  apply (weightedVolterraOperator_norm_le h hP hmass hq).trans
  rcases hweight with rfl | rfl | rfl <;> norm_num

/-- The weighted inverse exists for every weight whose printed
coefficient is at most `1/2`. Paper `e1a0fd5`, lines 1742–1747. -/
theorem weightedVolterraOperator_inverse {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (hc : 1 / (4 * (2 - q) * (1 - q)) ≤ 1 / 2) :
    (1 - weightedVolterraOperator h hP hmass hq) *
        observationResolvent (weightedVolterraOperator h hP hmass hq) = 1 ∧
      observationResolvent (weightedVolterraOperator h hP hmass hq) *
        (1 - weightedVolterraOperator h hP hmass hq) = 1 := by
  apply observationResolvent_inverse
  exact lt_of_le_of_lt ((weightedVolterraOperator_norm_le h hP hmass hq).trans hc)
    (by norm_num)

/-- The actual weighted inverse has norm at most `2`. Paper
`e1a0fd5`, lines 1742–1747. -/
theorem weightedVolterraOperator_resolvent_norm_le_two {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (hc : 1 / (4 * (2 - q) * (1 - q)) ≤ 1 / 2) :
    ‖observationResolvent (weightedVolterraOperator h hP hmass hq)‖ ≤ 2 := by
  exact observationResolvent_norm_le_two _
    ((weightedVolterraOperator_norm_le h hP hmass hq).trans hc)

/-- Positivity of the actual chart kernel gives positivity of its
weighted operator. Paper `e1a0fd5`, lines 1747–1755. -/
theorem weightedVolterraOperator_positive {b T K P q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (f : exteriorDomain h P →ᵇ ℝ) (hf : ∀ p, 0 ≤ f p)
    (p : exteriorDomain h P) : 0 ≤ weightedVolterraOperator h hP hmass hq f p := by
  have hr := (exteriorDomain_interior h hP p.property).2
  rw [weightedVolterraOperator_apply, weightedVolterraValue]
  apply mul_nonneg (Real.rpow_nonneg hr.le (-q))
  unfold triangleVolterra
  apply intervalIntegral.integral_nonneg p.property.1.2.2.2
  intro σ hσ
  apply intervalIntegral.integral_nonneg hσ.1
  intro z hz
  have hmem := exteriorDomain_triangle h hP p.property
    (show (σ, z) ∈ chartTriangle p.val.2 p.val.1 from ⟨hz.1, hz.2, hσ.2⟩)
  apply mul_nonneg (h.potential_nonneg hmem.1)
  rw [weightedExteriorLift_eq h f hmem]
  exact mul_nonneg (Real.rpow_nonneg (exteriorDomain_interior h hP hmem).2.le q) (hf _)

end PropA4
end AcExtensionPrinciple

end
