module

public import AcExtensionPrinciple.Weighted.Prop34Local
public import AcExtensionPrinciple.Weighted.ClassMeasurableStrip

/-!
# Joint measurable representatives of the frozen and radial operators

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1282.
Parameter-dependent integrals are measurable even when their Bochner
integrals vanish by the nonintegrability convention. The representatives
agree with the literal formulas everywhere off the axis.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Integrating a jointly measurable integrand between measurable moving
endpoints gives a measurable function of the two parameters. Paper
`e1a0fd5`, lines 1265–1282, measurability of the solution operators. -/
theorem measurable_setIntegral_between {a b : ℝ × ℝ → ℝ}
    {G : (ℝ × ℝ) × ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hG : Measurable G) :
    Measurable (fun p => ∫ s in Ioc (a p) (b p), G (p, s)) := by
  let D : Set ((ℝ × ℝ) × ℝ) := {q | a q.1 < q.2 ∧ q.2 ≤ b q.1}
  have hD : MeasurableSet D :=
    (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))
  have hm := (hG.indicator hD).stronglyMeasurable.integral_prod_right' (ν := volume)
  have he (p : ℝ × ℝ) :
      (∫ s, D.indicator G (p, s)) = ∫ s in Ioc (a p) (b p), G (p, s) := by
    change (∫ s, (Ioc (a p) (b p)).indicator (fun s => G (p, s)) s) = _
    exact integral_indicator measurableSet_Ioc
  simpa only [he] using hm.measurable

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual incoming integrating factor has a measurable extension on
each proper triangle, including the axis convention. Paper `e1a0fd5`,
`eq:frozen-linear-transport`, lines 1257–1276. -/
theorem weighted_exists_measurable_kappa {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ K : ℝ × ℝ → ℝ, Measurable K ∧
      EqOn (fun p => S.kappa p.1 p.2) K (weightedTruncatedDomain u₀ U) := by
  obtain ⟨R, hR, heR⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_r
  obtain ⟨M, hM, heM⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_m
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_lam
  refine ⟨fun p => L p / (1 - massRatio (R p) (M p)),
    hL.div (measurable_const.sub ((hM.const_mul 2).div hR)), ?_⟩
  intro p hp
  simp only [← heL hp, ← heR hp, ← heM hp, SSFields.kappa, SSFields.mu, kappaOf]

/-- The literal frozen formula admits a joint measurable extension from
every off-axis rectangle, without an integrability premise. Paper
`e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weightedFrozenSolution_measurable_rectangle {u₀ U b c : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbc : b < c) (hc0 : c ≤ 0) {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF : Measurable F) :
    ∃ Z : ℝ × ℝ → ℝ, Measurable Z ∧
      EqOn (weightedFrozenSolution S u₀ J₀ F) Z (Icc u₀ b ×ˢ Icc c 0) := by
  obtain ⟨K, hK, heK⟩ := h.weighted_exists_measurable_kappa hi hU
  obtain ⟨A, hA, heA, _⟩ := h.frozen_source_coefficient_rectangle hi hab hbc hc0
  let G := fun q : (ℝ × ℝ) × ℝ => A (q.2, q.1.2) * F (q.2, q.1.2)
  have hG : Measurable G :=
    (hA.mul hF).comp (measurable_snd.prodMk measurable_fst.snd)
  let I := fun p : ℝ × ℝ => ∫ s in Ioc u₀ p.1, G (p, s)
  have hI : Measurable I := measurable_setIntegral_between measurable_const measurable_fst hG
  let Z := fun p : ℝ × ℝ => (K (u₀, p.2) * J₀ p.2 + I p) / K p
  refine ⟨Z, ((hK.comp (measurable_const.prodMk measurable_snd)).mul
    (hJ₀.comp measurable_snd) |>.add hI).div hK, ?_⟩
  intro p hp
  have hpD : p ∈ weightedTruncatedDomain u₀ U :=
    ⟨hp.1.1, hp.1.2.trans hbU, (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le, hp.2.2⟩
  have h0D : (u₀, p.2) ∈ weightedTruncatedDomain u₀ U :=
    ⟨le_rfl, hab.trans hbU, hab.trans (hbc.le.trans hp.2.1), hp.2.2⟩
  have heI : (∫ s in u₀..p.1,
      3 * S.kappa s p.2 * S.nu s p.2 * S.dvphi s p.2 * F (s, p.2)) = I p := by
    rw [intervalIntegral.integral_of_le hp.1.1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only [G]
    rw [← heA (x := (s, p.2)) ⟨⟨hs.1.le, hs.2.trans hp.1.2⟩, hp.2⟩]
  dsimp only [weightedFrozenSolution, Z]
  rw [← heK hpD, ← heK h0D, heI]

/-- Choose a joint measurable representative of the literal frozen formula
on the whole proper off-axis strip. All finite-source ray equations proved
earlier consequently refer to this same formula. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1282. -/
theorem weightedFrozenSolution_measurable_strip {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF : Measurable F) :
    ∃ Z : ℝ × ℝ → ℝ, Measurable Z ∧
      EqOn (weightedFrozenSolution S u₀ J₀ F) Z (weightedOffAxisStrip u₀ U) := by
  rw [weightedOffAxisStrip_eq_iUnion]
  apply measurable_piecewise_of_countable_extensions
    (fun _ => measurableSet_Icc.prod measurableSet_Icc)
  intro q
  exact h.weightedFrozenSolution_measurable_rectangle hi hU q.2.1
    (min_le_left _ _) q.2.2.1 q.2.2.2 hJ₀ hF

/-- The literal radial operator admits a joint measurable extension on the
proper off-axis strip for every measurable input. No finite-energy premise
is needed for measurability. Paper `e1a0fd5`, `eq:weighted-radial-operator`
and lines 1278–1282. -/
theorem weightedRadialOperator_measurable_strip {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) {W : ℝ × ℝ → ℝ} (hW : Measurable W) :
    ∃ T : ℝ × ℝ → ℝ, Measurable T ∧
      EqOn (weightedRadialOperator S W) T (weightedOffAxisStrip u₀ U) := by
  obtain ⟨R, hR, heR⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_r
  obtain ⟨A, hA, heA⟩ := h.weighted_exists_measurable_amplitude_strip hi hU
  let G := fun q : (ℝ × ℝ) × ℝ => R (q.1.1, q.2) *
    (A (q.1.1, q.2) * W (q.1.1, q.2))
  have hG : Measurable G := (hR.mul (hA.mul hW)).comp
    (measurable_fst.fst.prodMk measurable_snd)
  let I := fun p : ℝ × ℝ => ∫ s in Ioc p.1 p.2, G (p, s)
  have hI : Measurable I := measurable_setIntegral_between measurable_fst measurable_snd hG
  refine ⟨fun p => (R p ^ 2)⁻¹ * I p, (hR.pow_const 2).inv.mul hI, ?_⟩
  intro p hp
  have hpD : p ∈ weightedTruncatedDomain u₀ U :=
    ⟨hp.1, hp.2.1, hp.2.2.1.le, hp.2.2.2⟩
  have heI : (∫ s in p.1..p.2,
      S.r p.1 s * (weightedIncomingAmplitude S p.1 s * W (p.1, s))) = I p := by
    rw [intervalIntegral.integral_of_le hp.2.2.1.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hsD : (p.1, s) ∈ weightedTruncatedDomain u₀ U :=
      ⟨hp.1, hp.2.1, hs.1.le, hs.2.trans hp.2.2.2⟩
    dsimp only [G]
    rw [← heR hsD,
      ← heA (x := (p.1, s)) ⟨hp.1, hp.2.1, hs.1, hs.2.trans hp.2.2.2⟩]
  dsimp only [weightedRadialOperator]
  rw [← heR hpD, heI]

end StandingFull

end AcExtensionPrinciple

end
