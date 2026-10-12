module

public import AcExtensionPrinciple.Observability.PropA4UnitSolution
public import AcExtensionPrinciple.Observability.PropA4AmplitudeRegularity
public import AcExtensionPrinciple.Observability.PropA4ResolventBound
public import AcExtensionPrinciple.Observability.PropA4OscillationKernel

/-!
# The exact exterior scalar remainder

Paper `e1a0fd5`, lines 1766–1779. The boundary primitive and remainder
are continuous on the actual exterior domain, and the remainder has
exactly the inhomogeneous Volterra equation displayed in the proof.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- The boundary primitive appearing in the exact scalar decomposition.
Paper `e1a0fd5`, lines 1766–1769. -/
@[expose] noncomputable def exteriorBoundaryPrimitive {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (p : ℝ × ℝ) : ℝ :=
  ∫ z in h.g p.1..p.2, S.dvpsi z z

/-- The amplitude is continuous on the exterior domain. The late-time
premise follows from the observation duration. Paper `e1a0fd5`, lines 1700–1707. -/
theorem amplitude_continuous_on_exterior {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => amplitude h p.1) (exteriorDomain h P) := by
  have hc : ContinuousOn (amplitude h) (Icc (K * b) T) := by
    simpa only [uIcc_of_le hT] using (amplitude_ac h hT).continuousOn
  exact hc.comp continuousOn_fst
    (fun p hp => ⟨hp.2.1.trans hp.1.2.2.2, hp.1.2.1⟩)

/-- The boundary primitive is continuous even though its integrand is
only BV. Its Volterra representation supplies this continuity.
Paper `e1a0fd5`, lines 1766–1769. -/
theorem exteriorBoundaryPrimitive_continuous {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T) :
    ContinuousOn (exteriorBoundaryPrimitive h) (exteriorDomain h P) := by
  have hψ : ContinuousOn (fun p : ℝ × ℝ => chartPsi S p.1 p.2) (exteriorDomain h P) :=
    (h.continuous_r.mul h.continuous_phi).mono (fun _ hp => hp.1)
  have hc := (hψ.sub (amplitude_continuous_on_exterior h hT)).sub
    (exterior_volterra_continuous h hP hψ)
  apply hc.congr
  intro p hp
  have he := volterra_amplitude h (hp.2.1.trans hp.1.2.2.2)
    (exteriorDomain_interior h hP hp)
  change exteriorBoundaryPrimitive h p = _
  dsimp only [exteriorBoundaryPrimitive, Pi.sub_apply] at *
  linarith

/-- The remainder in the paper's exact scalar decomposition.
Paper `e1a0fd5`, lines 1766–1769. -/
@[expose] noncomputable def exteriorRemainder {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (p : ℝ × ℝ) : ℝ :=
  chartPsi S p.1 p.2 - amplitude h p.1 * exteriorUnitSolution h hP hmass p -
    exteriorBoundaryPrimitive h p

/-- Exact scalar decomposition, with no estimated error term.
Paper `e1a0fd5`, `eq:observability-scalar-decomposition`, lines 1766–1769. -/
theorem exterior_scalar_decomposition {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) (p : ℝ × ℝ) :
    chartPsi S p.1 p.2 = amplitude h p.1 * exteriorUnitSolution h hP hmass p +
      exteriorBoundaryPrimitive h p + exteriorRemainder h hP hmass p := by
  unfold exteriorRemainder
  ring

/-- The concrete remainder is continuous in the weighted operator space.
Paper `e1a0fd5`, lines 1766–1779. -/
theorem exteriorRemainder_continuous {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    ContinuousOn (exteriorRemainder h hP hmass) (exteriorDomain h P) :=
  (((h.continuous_r.mul h.continuous_phi).mono (fun _ hp => hp.1)).sub
    ((amplitude_continuous_on_exterior h hT).mul (exteriorUnitSolution_continuous h hP hmass))).sub
    (exteriorBoundaryPrimitive_continuous h hP hT)

/-- Substitution gives exactly the forcing printed for `(I - 𝒦)R`.
Paper `e1a0fd5`, lines 1770–1779. -/
theorem exteriorRemainder_equation {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (hT : K * b ≤ T)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    exteriorRemainder h hP hmass p -
        triangleVolterra (fun p => chartPotential S p.1 p.2)
          (exteriorRemainder h hP hmass) p.1 p.2 =
      triangleVolterra (fun p => chartPotential S p.1 p.2)
        (fun z => exteriorBoundaryPrimitive h z +
          (amplitude h z.1 - amplitude h p.1) * exteriorUnitSolution h hP hmass z)
        p.1 p.2 := by
  let W := exteriorUnitSolution h hP hmass
  let R := exteriorRemainder h hP hmass
  let Q := fun z => exteriorBoundaryPrimitive h z + (amplitude h z.1 - amplitude h p.1) * W z
  let ψ := fun z : ℝ × ℝ => chartPsi S z.1 z.2
  let V := fun z : ℝ × ℝ => chartPotential S z.1 z.2
  have htri := exteriorDomain_triangle h hP hp
  have hVc := continuous_potential_on h (fun z hz => exteriorDomain_interior h hP (htri hz))
  have hRc := (exteriorRemainder_continuous h hP hT hmass).mono htri
  have hWc := (exteriorUnitSolution_continuous h hP hmass).mono htri
  have hAc := (amplitude_continuous_on_exterior h hT).mono htri
  have hQc : ContinuousOn Q (chartTriangle p.2 p.1) :=
    ((exteriorBoundaryPrimitive_continuous h hP hT).mono htri).add
      ((hAc.sub continuousOn_const).mul hWc)
  have hψc : ContinuousOn ψ (chartTriangle p.2 p.1) :=
    (h.continuous_r.mul h.continuous_phi).mono (fun z hz => (htri hz).1)
  have hid : R + Q = ψ + (-amplitude h p.1) • W := by
    funext z
    dsimp [R, Q, ψ, exteriorRemainder, W]
    ring
  have hi := triangleVolterra_add_on hp.1.2.2.2 hVc hRc hQc
  rw [hid, triangleVolterra_add_on hp.1.2.2.2 hVc hψc
    (hWc.const_smul (-amplitude h p.1)), triangleVolterra_smul] at hi
  have hψeq := volterra_amplitude h (hp.2.1.trans hp.1.2.2.2)
    (exteriorDomain_interior h hP hp)
  have hWeq := exteriorUnitSolution_equation h hP hmass hp
  have hR : R p = ψ p - amplitude h p.1 * W p - exteriorBoundaryPrimitive h p := rfl
  change R p - triangleVolterra V R p.1 p.2 = triangleVolterra V Q p.1 p.2
  change ψ p = amplitude h p.1 + exteriorBoundaryPrimitive h p +
    triangleVolterra V ψ p.1 p.2 at hψeq
  change W p = 1 + triangleVolterra V W p.1 p.2 at hWeq
  rw [hR, hψeq, hWeq]
  dsimp only [V] at hi ⊢
  linarith

end PropA4
end AcExtensionPrinciple

end
