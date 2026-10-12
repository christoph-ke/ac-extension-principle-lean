module

public import AcExtensionPrinciple.Decay.ClassCylinderStatements
public import AcExtensionPrinciple.Decay.ClassRayConsequences
public import AcExtensionPrinciple.Analysis.GeometricRecurrence
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Iterated boundary-energy loss on a long regular cylinder

Paper `e1a0fd5`, lines 893–909. For any sufficiently late target time, choose
N complete boundary-time intervals ending at that target. This also controls
times in partial intervals without fixing a single subdivision in advance.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DecayCylinder

/-- Subinterval restriction preserves the same curve and boundary clock.
Paper `e1a0fd5`, lines 700–706 and 751–801. -/
@[expose] def restrict {ui b a₀ a₁ a d : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) :
    DecayCylinder ui S b a d where
  v := c.v
  tau := c.tau
  radius_pos := c.radius_pos
  initial_le := c.initial_le.trans ha
  ordered := had
  terminal_negative := hd.trans_lt c.terminal_negative
  points u hu := c.points u ⟨ha.trans hu.1, hu.2.trans hd⟩
  smooth_v := c.smooth_v.mono (Icc_subset_Icc ha hd)
  tangent u hu := c.tangent u ⟨ha.trans_lt hu.1, hu.2.trans_le hd⟩
  continuous_tau := c.continuous_tau.mono (Icc_subset_Icc ha hd)
  clock x y hx hxy hy := c.clock x y (ha.trans hx) hxy (hy.trans hd)

/-- Every cylinder point belongs to the solution triangle. Paper `e1a0fd5`,
lines 664–675 and 884–891. -/
theorem point_mem {ui b a₀ a₁ u : ℝ} {S : SSFields} (c : DecayCylinder ui S b a₀ a₁)
    (hu : u ∈ Icc a₀ a₁) : (u, c.v u) ∈ pastTriangle ui :=
  ⟨c.initial_le.trans hu.1, hu.2.trans_lt c.terminal_negative,
    (c.points u hu).1.le, (c.points u hu).2.1⟩

/-- Outgoing time is at most K times boundary time. Paper `e1a0fd5`,
`eq:required-cylinder-duration`, lines 905–909. -/
theorem time_le {ui b a₀ a₁ K a d : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (hg : CylinderKBounds ui S K)
    (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁) : d - a ≤ K * (c.tau d - c.tau a) := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hg.1
  have hc := c.clock a d ha had hd
  have hi : K⁻¹ * (d - a) ≤ c.tau d - c.tau a := by
    rw [hc.2]
    calc
      _ = ∫ _u in a..d, K⁻¹ := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on had intervalIntegrable_const hc.1
        (fun u hu => (hg.2 (u, c.v u) (c.point_mem ⟨ha.trans hu.1, hu.2.trans hd⟩)).2.2.2)
  have hm := mul_le_mul_of_nonneg_left hi hK.le
  rwa [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at hm

/-- The boundary clock is strictly increasing on a regular cylinder.
Paper `e1a0fd5`, `eq:cylinder-time`, lines 671–675 and 905–909. -/
theorem clock_strict {ui b a₀ a₁ K : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (hg : CylinderKBounds ui S K) :
    StrictMonoOn c.tau (Icc a₀ a₁) := by
  intro a ha d hd had
  have hh := c.time_le hg ha.1 had.le hd.2
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hg.1
  nlinarith

end DecayCylinder

/-- Choose ε below any proposed failure level, then N, with uniform numerical
smallness conditions. Paper `e1a0fd5`, lines 898–905. -/
theorem decay_choose_parameters {C₀ Q rho eta : ℝ} (_hC : 0 ≤ C₀) (hQ : 0 ≤ Q)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ eps ≤ eta / 2 ∧ Q * eps ≤ 1 / 16 ∧
      ∃ N : ℕ, C₀ * rho ^ N ≤ eps / 16 := by
  let eps := min (eta / 2) (min 1 (1 / (16 * (Q + 1))))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have h1 : eps ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have heta' : eps ≤ eta / 2 := min_le_left _ _
  have hden : 0 < 16 * (Q + 1) := by positivity
  have hsmall : Q * eps ≤ 1 / 16 := by
    have hl : eps ≤ 1 / (16 * (Q + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ hden).mp hl
    nlinarith
  have ht : Tendsto (fun n : ℕ => C₀ * rho ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hrho hrho1).const_mul C₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually
    (gt_mem_nhds (show 0 < eps / 16 by positivity)))
  exact ⟨eps, heps, h1, heta', hsmall, N, (hN N le_rfl).le⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

omit h in
/-- Energy is small at every time after the uniform waiting and contraction duration. Lemma 2.6
supplies the variation premise; `affine_recurrence_le` supplies the iterated affine bound. Paper
`e1a0fd5`, `eq:iterated-boundary-decay`, `eq:late-cylinder-energy-smallness`,
`eq:required-cylinder-duration`, 802–817. -/
theorem decay_cylinder_energy {K H C₀ C₁ D rho eps b a₀ a₁ u : ℝ} {N : ℕ}
    (hg : CylinderKBounds ui S K)
    (h25 : Lemma25Statement ui S H C₁ rho)
    (h26 : ∀ eps b u₀ x y (c : DecayCylinder ui S b x y),
      0 < eps → eps ≤ 1 → ui ≤ u₀ → u₀ ≤ x →
      (∀ s v, (s, v) ∈ pastTriangle ui → u₀ ≤ s → s ≤ y → b ≤ S.r s v → S.mu s v ≤ eps) →
      initialACTail ui S u₀ ≤ eps → K * b / eps ≤ x - u₀ → c.tau y - c.tau x ≤ H * b →
      eVariationOn (cylinderDatum S c) (Icc x y) ≤ ENNReal.ofReal (D * eps))
    (hD : 0 ≤ D) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (c : DecayCylinder ui S b a₀ a₁)
    (hE : ∀ s ∈ Icc a₀ a₁, decayCylinderEnergy S c s ≤ C₀ * b)
    (hext : ∀ s v, (s, v) ∈ pastTriangle ui → a₀ ≤ s → s ≤ a₁ → b ≤ S.r s v →
      S.mu s v ≤ eps)
    (htail : initialACTail ui S a₀ ≤ eps)
    (hu : u ∈ Icc a₀ a₁)
    (hwait : a₀ + K * b / eps + K * ((N : ℝ) * H * b) ≤ u)
    (hsmall : (C₁ * D ^ 2 / (1 - rho)) * eps ≤ 1 / 16)
    (htransient : C₀ * rho ^ N ≤ eps / 16) :
    decayCylinderEnergy S c u ≤ eps * b / 8 := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hg.1
  have hH := h25.1
  have hC₁ := h25.2.1
  have hrho := h25.2.2.1
  have hrho1 := h25.2.2.2.1
  have hb := c.radius_pos
  let w := a₀ + K * b / eps
  have haw : a₀ ≤ w := by
    have hh : 0 ≤ K * b / eps := by positivity
    dsimp [w]
    linarith
  have hwu : w ≤ u := by
    have hn : 0 ≤ K * ((N : ℝ) * H * b) := by positivity
    dsimp [w]
    linarith
  have hw₁ : w ≤ a₁ := hwu.trans hu.2
  have htime : (N : ℝ) * H * b ≤ c.tau u - c.tau w := by
    have hh := c.time_le hg haw hwu hu.2
    have hl : K * ((N : ℝ) * H * b) ≤ u - w := by dsimp [w]; linarith
    exact (mul_le_mul_iff_of_pos_left hK).mp (hl.trans hh)
  let base := c.tau u - (N : ℝ) * H * b
  have hbase : c.tau w ≤ base := by dsimp [base]; linarith
  have hex : ∀ k : ℕ, k ≤ N → ∃ a ∈ Icc w u, c.tau a = base + (k : ℝ) * H * b := by
    intro k hk
    apply intermediate_value_Icc hwu (c.continuous_tau.mono (Icc_subset_Icc haw hu.2))
    constructor
    · dsimp [base]
      have hn : 0 ≤ (k : ℝ) * H * b := by positivity
      linarith
    · have hn : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hH.le) hb.le
      dsimp [base]
      linarith
  let A (k : ℕ) := if hk : k ≤ N then Classical.choose (hex k hk) else u
  have hs (k : ℕ) (hk : k ≤ N) :
      A k ∈ Icc w u ∧ c.tau (A k) = base + (k : ℝ) * H * b := by
    dsimp only [A]
    rw [dite_eq_left hk]
    exact Classical.choose_spec (hex k hk)
  have hs' (k : ℕ) (hk : k ≤ N) : A k ∈ Icc a₀ a₁ :=
    ⟨haw.trans (hs k hk).1.1, (hs k hk).1.2.trans hu.2⟩
  have hAN : A N = u := by
    apply le_antisymm (hs N le_rfl).1.2
    by_contra hnot
    have hh := c.clock_strict hg (hs' N le_rfl) hu (lt_of_not_ge hnot)
    have he := (hs N le_rfl).2
    dsimp [base] at he
    linarith
  let cost := C₁ * b * (D * eps) ^ 2
  have hcost : 0 ≤ cost := by dsimp [cost]; positivity
  have hstep (k : ℕ) (hk : k < N) :
      decayCylinderEnergy S c (A (k + 1)) ≤ rho * decayCylinderEnergy S c (A k) + cost := by
    have hkn : k + 1 ≤ N := by omega
    have hk₀ := hs k hk.le
    have hk₁ := hs (k + 1) hkn
    have htau : c.tau (A (k + 1)) - c.tau (A k) = H * b := by
      rw [hk₀.2, hk₁.2, Nat.cast_add, Nat.cast_one]
      ring
    have horder : A k ≤ A (k + 1) := by
      by_contra hnot
      have hh := c.clock_strict hg (hs' (k + 1) hkn) (hs' k hk.le) (lt_of_not_ge hnot)
      nlinarith [mul_pos hH hb]
    have hv := h26 eps b a₀ (A k) (A (k + 1))
      (c.restrict (hs' k hk.le).1 horder (hs' (k + 1) hkn).2)
      heps heps1 c.initial_le (hs' k hk.le).1
      (fun s v hp hs hsend hr => hext s v hp hs
        (hsend.trans (hs' (k + 1) hkn).2) hr) htail
      (by dsimp [w] at hk₀; linarith [hk₀.1.1]) (by exact htau.le)
    change eVariationOn (cylinderDatum S c) (Icc (A k) (A (k + 1))) ≤
      ENNReal.ofReal (D * eps) at hv
    have hvr : cylinderVariation S c (A k) (A (k + 1)) ≤ D * eps :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hD heps.le))
    have hh := h25.2.2.2.2 b a₀ a₁ c (A k) (A (k + 1))
      (hs' k hk.le).1 horder (hs' (k + 1) hkn).2 htau
    apply hh.trans
    dsimp [cost]
    gcongr
    exact ENNReal.toReal_nonneg
  let y : ℕ → ℝ := Nat.rec (decayCylinderEnergy S c (A 0)) (fun _ t => rho * t + cost)
  have hy : ∀ k, y (k + 1) = rho * y k + cost := fun _ => rfl
  have hAy : ∀ k, k ≤ N → decayCylinderEnergy S c (A k) ≤ y k := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      exact (hstep k (by omega)).trans (by
        rw [hy]
        have hh := mul_le_mul_of_nonneg_left (ih (by omega)) hrho.le
        linarith)
  have hbnd := affine_recurrence_le hrho.le hrho1 hcost (fun k => (hy k).le) N
  have henergy : decayCylinderEnergy S c u ≤
      (rho ^ N * C₀ + C₁ * D ^ 2 / (1 - rho) * eps ^ 2) * b := by
    calc
      _ = decayCylinderEnergy S c (A N) := by rw [hAN]
      _ ≤ y N := hAy N le_rfl
      _ ≤ rho ^ N * y 0 + cost / (1 - rho) := hbnd
      _ ≤ rho ^ N * (C₀ * b) + cost / (1 - rho) := by
        change rho ^ N * decayCylinderEnergy S c (A 0) + cost / (1 - rho) ≤ _
        have hh := mul_le_mul_of_nonneg_left (hE (A 0) (hs' 0 (Nat.zero_le N)))
          (pow_nonneg hrho.le N)
        linarith
      _ = _ := by dsimp [cost]; ring
  have hforcing := mul_le_mul_of_nonneg_right hsmall heps.le
  have hcoef : rho ^ N * C₀ + C₁ * D ^ 2 / (1 - rho) * eps ^ 2 ≤ eps / 8 := by
    nlinarith
  exact henergy.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoef hb.le])

end StandingFull

end AcExtensionPrinciple

end
