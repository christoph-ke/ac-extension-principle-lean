module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

/-!
# Positivity for the triangular Volterra equation

Continuous-kernel version of paper `e1a0fd5`, `equations.tex`
lines 1520–1530. No smallness assumption on the kernel is used.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter
open scoped Topology

/-- The triangular double-integral operator; paper `e1a0fd5`,
`eq:observability-volterra`, lines 1520–1530. -/
@[expose] noncomputable def triangleVolterra (P f : ℝ × ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ σ in t..s, ∫ z in t..σ, P (σ, z) * f (σ, z)

/-- One Volterra iteration gains a factorial denominator; paper `e1a0fd5`,
`equations.tex` lines 1520–1530. -/
theorem triangleVolterra_lower_step {P f : ℝ × ℝ → ℝ} {T p C s t : ℝ}
    (hP : Continuous P) (hf : Continuous f) (hT : 0 ≤ T) (hp : 0 ≤ p)
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ T) (n : ℕ)
    (hkernel : ∀ σ z, 0 ≤ z → z ≤ σ → σ ≤ T → 0 ≤ P (σ, z) ∧ P (σ, z) ≤ p)
    (hlower : ∀ σ z, 0 ≤ z → z ≤ σ → σ ≤ T → -C * σ ^ n ≤ f (σ, z)) :
    -(p * T * C) * (s ^ (n + 1) / (n + 1)) ≤ triangleVolterra P f s t := by
  have hprod : Continuous (fun q : ℝ × ℝ ↦ P q * f q) := hP.mul hf
  have hinner : Continuous (fun σ ↦ ∫ z in t..σ, P (σ, z) * f (σ, z)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hprod continuous_id
  have hpoint (σ : ℝ) (hσ : σ ∈ Icc t s) :
      -(p * T * C) * σ ^ n ≤ ∫ z in t..σ, P (σ, z) * f (σ, z) := by
    have hσ0 : 0 ≤ σ := ht.trans hσ.1
    have hσT : σ ≤ T := hσ.2.trans hs
    have hbound (z : ℝ) (hz : z ∈ Icc t σ) :
        -(p * C) * σ ^ n ≤ P (σ, z) * f (σ, z) := by
      have hk := hkernel σ z (ht.trans hz.1) hz.2 hσT
      have hl := hlower σ z (ht.trans hz.1) hz.2 hσT
      have hn : 0 ≤ C * σ ^ n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hl hk.1,
        mul_le_mul_of_nonneg_right hk.2 hn]
    have hi := intervalIntegral.integral_mono_on (μ := volume) hσ.1 intervalIntegrable_const
      ((hprod.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _) hbound
    rw [intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul] at hi
    simp only [Function.comp_def, id_eq] at hi
    have hlen : σ - t ≤ T := by linarith
    have hcσ : 0 ≤ p * C * σ ^ n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hlen hcσ]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hts
    ((continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _)
    (hinner.intervalIntegrable _ _) hpoint
  have hpow : (∫ σ in t..s, σ ^ n) ≤ ∫ σ in 0..s, σ ^ n := by
    apply intervalIntegral.integral_mono_interval ht hts le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
      exact pow_nonneg hσ.1.le n
    · exact (continuous_id.pow n).intervalIntegrable _ _
  have hs0 : 0 ≤ s := ht.trans hts
  have hpow0 : (∫ σ in 0..s, σ ^ n) = s ^ (n + 1) / (n + 1) := by
    rw [integral_pow]
    simp
  rw [hpow0] at hpow
  change (∫ σ in t..s, -(p * T * C) * σ ^ n) ≤ _ at hint
  rw [intervalIntegral.integral_const_mul] at hint
  dsimp [triangleVolterra]
  exact (mul_le_mul_of_nonpos_left hpow
    (neg_nonpos.mpr (mul_nonneg (mul_nonneg hp hT) hC))).trans hint

/-- Positive inhomogeneous data force the same lower bound on the solution;
paper `e1a0fd5`, `equations.tex` lines 1520–1530. Boundedness is required only
on the triangle. The proof iterates the Volterra estimate and lets the factorial
remainder tend to zero, as in the paper's Neumann argument. -/
theorem triangleVolterra_positive {P ψ g : ℝ × ℝ → ℝ} {T p c : ℝ}
    (hP : Continuous P) (hψ : Continuous ψ) (hT : 0 ≤ T) (hc : 0 < c)
    (hkernel : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → 0 ≤ P (s, t) ∧ P (s, t) ≤ p)
    (hbounded : ∃ B : ℝ, ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → |ψ (s, t)| ≤ B)
    (hg : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → c ≤ g (s, t))
    (heq : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T →
      ψ (s, t) = g (s, t) + triangleVolterra P ψ s t) :
    ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → c ≤ ψ (s, t) := by
  obtain ⟨B, hB⟩ := hbounded
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0 le_rfl le_rfl hT)
  have hp : 0 ≤ p := (hkernel 0 0 le_rfl le_rfl hT).1.trans
    (hkernel 0 0 le_rfl le_rfl hT).2
  have hiter (n : ℕ) : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T →
      c - (c + B) * (p * T) ^ n / n.factorial * s ^ n ≤ ψ (s, t) := by
    induction n with
    | zero =>
      intro s t ht hts hs
      simpa using (abs_le.mp (hB s t ht hts hs)).1
    | succ n ih =>
      intro s t ht hts hs
      let C := (c + B) * (p * T) ^ n / n.factorial
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hl : ∀ σ z, 0 ≤ z → z ≤ σ → σ ≤ T → -C * σ ^ n ≤ ψ (σ, z) := by
        intro σ z hz hzσ hσ
        have := ih σ z hz hzσ hσ
        dsimp [C]
        linarith
      have hv := triangleVolterra_lower_step hP hψ hT hp hC ht hts hs n hkernel hl
      have hg' := hg s t ht hts hs
      rw [heq s t ht hts hs]
      have hid : (p * T * C) * (s ^ (n + 1) / (n + 1)) =
          (c + B) * (p * T) ^ (n + 1) / (n + 1).factorial * s ^ (n + 1) := by
        dsimp [C]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp
        ring
      rw [neg_mul, hid] at hv
      linarith
  intro s t ht hts hs
  have hlim : Tendsto (fun n : ℕ ↦
      c - (c + B) * (p * T) ^ n / n.factorial * s ^ n) atTop (𝓝 c) := by
    have hl := ((Real.summable_pow_div_factorial (p * T * s)).tendsto_atTop_zero).const_mul (c + B)
    have he : (fun n : ℕ ↦ (c + B) * (p * T) ^ n / n.factorial * s ^ n) =
        (fun n : ℕ ↦ (c + B) * ((p * T * s) ^ n / n.factorial)) := by
      funext n
      rw [mul_pow]
      ring
    have hl' : Tendsto (fun n : ℕ ↦ (c + B) * (p * T) ^ n / n.factorial * s ^ n)
        atTop (𝓝 0) := by rw [he]; simpa using hl
    simpa using (tendsto_const_nhds (x := c)).sub hl'
  exact le_of_tendsto hlim (Eventually.of_forall (fun n ↦ hiter n s t ht hts hs))

end AcExtensionPrinciple

end
