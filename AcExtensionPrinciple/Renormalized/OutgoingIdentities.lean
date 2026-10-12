module

public import AcExtensionPrinciple.Reduced.OutgoingRay

/-!
# Renormalized identities along outgoing rays

Paper commit `e1a0fd5`, `equations.tex` lines 596, 621,
1020–1078 and 1336. The radial datum is the quotient `(λφ + r ∂ᵥφ) / λ`.
The standing condition `λ > 0` near the point (paper line 120) identifies its
scalar amplitude with the difference of the datum and `φ`.

The retained counterexample explains why pointwise positivity alone is insufficient.
-/

public section

namespace AcExtensionPrinciple.Renormalized

/-- The interaction `𝒞 = μ + (1 - μ) A B`. Paper `e1a0fd5`,
`eq:renormalized-interaction`, lines 1022–1023. -/
@[expose] noncomputable def interactionOf (r lam nu m phiU phiV : ℝ) : ℝ :=
  massRatio r m + (1 - massRatio r m) * (r / lam * phiV) * (r / nu * phiU)

/-- The derivative `j = (1 - μ) λ (q - A³/r)`. Paper `e1a0fd5`,
`eq:renormalized-derivative`, lines 1020–1021. -/
@[expose] noncomputable def renormalizedDerivativeOf (r lam m phiV q : ℝ) : ℝ :=
  (1 - massRatio r m) * lam * (q - (r / lam * phiV) ^ 3 / r)

/-- The pointwise outgoing equations and the quotient-datum derivative do not imply
`eq:renormalized-radial-transport`. Paper `e1a0fd5`, lines 1033 and 1062–1067;
the missing neighborhood regularity is part of the paper's solution class, line 222.
Here `r = 1 + v`, `m = v/2`, `ν = -1`, `φ = 1 - v`, `φᵤ = -v`, `q = 0`,
and `λ`, `φᵥ` vanish off `v = 0` with values `1`, `-1` at `0`.
Then the quotient datum is identically zero, while `𝒞 = μ` has derivative `1`
and the proposed right-hand side is `0`. Also `A(0) = -1` and `A(v) = 0`
for `v ≠ 0`, so `eq:scalar-amplitude-radial-derivative` (line 621) fails. -/
theorem pointwise_hypotheses_insufficient_example :
    ∃ (r lam nu m phi phiU phiV q : ℝ → ℝ),
      HasDerivAt r (lam 0) 0 ∧
      HasDerivAt nu
        (kappaOf (lam 0) (massRatio (r 0) (m 0)) *
          varkappaOf (r 0) (massRatio (r 0) (m 0)) * nu 0) 0 ∧
      HasDerivAt m
        (r 0 ^ 2 / (2 * kappaOf (lam 0) (massRatio (r 0) (m 0))) * phiV 0 ^ 2) 0 ∧
      HasDerivAt phi (phiV 0) 0 ∧
      HasDerivAt phiU (-(nu 0 / r 0) * phiV 0 - (lam 0 / r 0) * phiU 0) 0 ∧
      HasDerivAt (fun s => (lam s * phi s + r s * phiV s) / lam s) (lam 0 * q 0) 0 ∧
      0 < r 0 ∧ 0 < lam 0 ∧ nu 0 < 0 ∧ massRatio (r 0) (m 0) < 1 ∧
      ¬HasDerivAt (fun s => interactionOf (r s) (lam s) (nu s) (m s) (phiU s) (phiV s))
        ((r 0 / nu 0 * phiU 0) *
            renormalizedDerivativeOf (r 0) (lam 0) (m 0) (phiV 0) (q 0) -
          (lam 0 / r 0) * interactionOf (r 0) (lam 0) (nu 0) (m 0) (phiU 0) (phiV 0)) 0 ∧
      ¬DifferentiableAt ℝ (fun s => r s / lam s * phiV s) 0 := by
  let r : ℝ → ℝ := fun s => 1 + s
  let lam : ℝ → ℝ := fun s => if s = 0 then 1 else 0
  let nu : ℝ → ℝ := fun _ => -1
  let m : ℝ → ℝ := fun s => s / 2
  let phi : ℝ → ℝ := fun s => 1 - s
  let phiU : ℝ → ℝ := fun s => -s
  let phiV : ℝ → ℝ := fun s => if s = 0 then -1 else 0
  let q : ℝ → ℝ := fun _ => 0
  have hr : HasDerivAt r 1 0 := by
    simpa [r] using (hasDerivAt_id (0 : ℝ)).const_add 1
  have hm : HasDerivAt m (1 / 2) 0 := by
    simpa [m] using (hasDerivAt_id (0 : ℝ)).div_const 2
  have hp : HasDerivAt phi (-1) 0 := by
    simpa [phi] using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hpu : HasDerivAt phiU (-1) 0 := by
    simpa [phiU] using (hasDerivAt_id (0 : ℝ)).const_sub 0
  have hP : (fun s => (lam s * phi s + r s * phiV s) / lam s) = fun _ => 0 := by
    funext s
    by_cases hs : s = 0 <;> simp [lam, phi, r, phiV, hs]
  have hC : (fun s => interactionOf (r s) (lam s) (nu s) (m s) (phiU s) (phiV s)) =
      fun s => massRatio (r s) (m s) := by
    funext s
    by_cases hs : s = 0 <;> simp [interactionOf, lam, phiV, phiU, hs]
  have hmu : HasDerivAt (fun s => massRatio (r s) (m s)) 1 0 := by
    have hm' : HasDerivAt m
        (r 0 ^ 2 / (2 * kappaOf (lam 0) (massRatio (r 0) (m 0))) * phiV 0 ^ 2) 0 := by
      simpa [r, lam, m, phiV, massRatio, kappaOf] using hm
    simpa [r, lam, m, phiV, massRatio] using
      OutgoingRay.mass_ratio (by simpa [lam] using hr) hm'
        (by simp [r]) (by simp [lam])
  refine ⟨r, lam, nu, m, phi, phiU, phiV, q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lam] using hr
  · simpa [r, lam, nu, m, massRatio, kappaOf, varkappaOf] using
      (hasDerivAt_const (0 : ℝ) (-1 : ℝ))
  · simpa [r, lam, m, phiV, massRatio, kappaOf] using hm
  · simpa [phiV] using hp
  · simpa [r, lam, nu, phiV, phiU] using hpu
  · rw [hP]
    simpa [q] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  · simp [r]
  · simp [lam]
  · simp [nu]
  · simp [r, m, massRatio]
  · refine ⟨?_, ?_⟩
    · intro h
      rw [hC] at h
      have hz : HasDerivAt (fun s => massRatio (r s) (m s)) 0 0 := by
        simpa [r, lam, nu, m, phiU, phiV, q, interactionOf,
          renormalizedDerivativeOf, massRatio] using h
      have he := hmu.unique hz
      norm_num at he
    · intro hA
      have hzero : (fun s => (r s / lam s * phiV s) * phiU s) = fun _ => 0 := by
        funext s
        by_cases hs : s = 0 <;> simp [lam, phiV, phiU, hs]
      have h := hA.hasDerivAt.fun_mul hpu
      rw [hzero] at h
      have hz : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 1 0 := by
        simpa [r, lam, phiV, phiU] using h
      have he := hz.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
      norm_num at he

namespace Outgoing

open Filter Topology

variable {r lam nu m phi phiU phiV q : ℝ → ℝ} {v : ℝ}

local notation "μ" => (fun s => massRatio (r s) (m s))
local notation "κ" => (fun s => kappaOf (lam s) (μ s))
local notation "γ" => (fun s => gammaOf (nu s) (μ s))
local notation "ϰ" => (fun s => varkappaOf (r s) (μ s))
local notation "A" => (fun s => r s / lam s * phiV s)
local notation "B" => (fun s => r s / nu s * phiU s)
local notation "𝒞" => (fun s => interactionOf (r s) (lam s) (nu s) (m s) (phiU s) (phiV s))
local notation "j" => (fun s => renormalizedDerivativeOf (r s) (lam s) (m s) (phiV s) (q s))

/-- The outgoing amplitude derivative follows from the quotient datum derivative.
Paper `e1a0fd5`, `eq:radial-datum-derivative`, line 557, and lines 1064–1065;
the neighbourhood positivity of `λ` is the standing condition at line 120. -/
theorem scalar_amplitude_from_datum
    (hP : HasDerivAt (fun s => (lam s * phi s + r s * phiV s) / lam s)
      (lam v * q v) v)
    (hphi : HasDerivAt phi (phiV v) v)
    (hlam : ∀ᶠ s in 𝓝 v, 0 < lam s) :
    HasDerivAt A (lam v * q v - phiV v) v := by
  apply (hP.sub hphi).congr_of_eventuallyEq
  filter_upwards [hlam] with s hs
  dsimp
  rw [normalized_scalar_eq (r s) (phi s) (phiV s) (ne_of_gt hs)]
  ring

/-- Radial scalar amplitude derivative. Paper `e1a0fd5`,
`eq:scalar-amplitude-radial-derivative`, line 621. -/
theorem scalar_amplitude_radial_derivative
    (hP : HasDerivAt (fun s => (lam s * phi s + r s * phiV s) / lam s)
      (lam v * q v) v)
    (hphi : HasDerivAt phi (phiV v) v)
    (hlam : ∀ᶠ s in 𝓝 v, 0 < lam s) (hr0 : 0 < r v) :
    HasDerivAt A (lam v * (q v - A v / r v)) v := by
  convert scalar_amplitude_from_datum hP hphi hlam using 1
  dsimp
  field_simp [ne_of_gt hr0, ne_of_gt (hlam.self_of_nhds)]

/-- Radial transport of the interaction. Paper `e1a0fd5`,
`eq:renormalized-radial-transport`, line 1033, proof lines 1062–1067. -/
theorem interaction_transport (hr : HasDerivAt r (lam v) v)
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v)
    (hm : HasDerivAt m (r v ^ 2 / (2 * κ v) * phiV v ^ 2) v)
    (hphiU : HasDerivAt phiU (-(nu v / r v) * phiV v - (lam v / r v) * phiU v) v)
    (hP : HasDerivAt (fun s => (lam s * phi s + r s * phiV s) / lam s)
      (lam v * q v) v)
    (hphi : HasDerivAt phi (phiV v) v)
    (hlam : ∀ᶠ s in 𝓝 v, 0 < lam s)
    (hr0 : 0 < r v) (hnu0 : nu v < 0) (hmu : μ v < 1) :
    HasDerivAt 𝒞 (B v * j v - (lam v / r v) * 𝒞 v) v := by
  have hmu' := OutgoingRay.radial_mass_ratio hr hm hr0 hlam.self_of_nhds
  have hA := scalar_amplitude_from_datum hP hphi hlam
  have hB := OutgoingRay.scalar_amplitude hr hnu hphiU hr0 hnu0
  convert hmu'.add (((hmu'.const_sub 1).mul hA).mul hB) using 1
  · funext s
    rfl
  · dsimp [interactionOf, renormalizedDerivativeOf, kappaOf, varkappaOf]
    field_simp [ne_of_gt hr0, ne_of_gt hlam.self_of_nhds, ne_of_lt hnu0,
      ne_of_gt (sub_pos.mpr hmu)]
    ring

/-- The radius-weighted interaction has derivative `r B j`. Paper `e1a0fd5`,
`equations.tex` line 1078, proof of `eq:renormalized-radial-primitive`. -/
theorem radius_interaction_transport (hr : HasDerivAt r (lam v) v)
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v)
    (hm : HasDerivAt m (r v ^ 2 / (2 * κ v) * phiV v ^ 2) v)
    (hphiU : HasDerivAt phiU (-(nu v / r v) * phiV v - (lam v / r v) * phiU v) v)
    (hP : HasDerivAt (fun s => (lam s * phi s + r s * phiV s) / lam s)
      (lam v * q v) v)
    (hphi : HasDerivAt phi (phiV v) v)
    (hlam : ∀ᶠ s in 𝓝 v, 0 < lam s)
    (hr0 : 0 < r v) (hnu0 : nu v < 0) (hmu : μ v < 1) :
    HasDerivAt (fun s => r s * 𝒞 s) (r v * B v * j v) v := by
  convert hr.mul (interaction_transport hr hnu hm hphiU hP hphi hlam hr0 hnu0 hmu) using 1
  field_simp [ne_of_gt hr0]
  ring

/-- Radial derivative of the normalized scalar transport coefficient. Paper `e1a0fd5`,
`eq:transport-coefficient-derivative`, line 596. -/
theorem transport_coefficient_derivative (hr : HasDerivAt r (lam v) v)
    (hnu : HasDerivAt nu (κ v * ϰ v * nu v) v)
    (hm : HasDerivAt m (r v ^ 2 / (2 * κ v) * phiV v ^ 2) v)
    (hr0 : 0 < r v) (hlam0 : 0 < lam v) (hmu : μ v < 1) :
    HasDerivAt (fun s => -(γ s * ϰ s))
      (lam v * (-γ v / r v ^ 2) * (A v ^ 2 - 2 * μ v)) v := by
  have hmu' := OutgoingRay.radial_mass_ratio hr hm hr0 hlam0
  have hg := hnu.div (hmu'.const_sub 1) (ne_of_gt (sub_pos.mpr hmu))
  have hv := hmu'.div hr (ne_of_gt hr0)
  convert (hg.mul hv).neg using 1
  · funext s
    rfl
  · dsimp [gammaOf, kappaOf, varkappaOf]
    field_simp [ne_of_gt hr0, ne_of_gt hlam0, ne_of_gt (sub_pos.mpr hmu)]
    ring

/-- The differentiated datum splits into its renormalized and cubic terms.
Paper `e1a0fd5`, `equations.tex` line 1336, proof of Proposition 3.5. -/
theorem datum_derivative_decomposition (hmu : μ v < 1) :
    lam v * q v = j v / (1 - μ v) + (lam v / r v) * A v ^ 3 := by
  change lam v * q v =
    (1 - μ v) * lam v * (q v - A v ^ 3 / r v) / (1 - μ v) +
      (lam v / r v) * A v ^ 3
  rw [mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hmu))]
  ring

end Outgoing

end AcExtensionPrinciple.Renormalized

end
