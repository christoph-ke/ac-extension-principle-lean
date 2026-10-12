module

public import AcExtensionPrinciple.Observability.Volterra

/-!
# Factorial Volterra bounds

Norm computation for paper `e1a0fd5`, `equations.tex` lines 1520–1530.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Continuity of an integral with moving endpoints; paper `e1a0fd5`,
calculus input at `equations.tex` lines 1520–1530. -/
theorem continuous_moving_interval_integral {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {a b : X → ℝ} (hf : Continuous f.uncurry)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x ↦ ∫ z in a x..b x, f x z) := by
  have h0b := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hb
  have h0a := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf ha
  convert h0b.sub h0a using 1
  funext x
  have hc : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (a x)) (hc.intervalIntegrable (a x) (b x))
  change (∫ z in a x..b x, f x z) =
    (∫ z in 0..b x, f x z) - (∫ z in 0..a x, f x z)
  linarith

/-- The triangular operator preserves continuity; paper `e1a0fd5`,
`equations.tex` lines 1520–1530. -/
theorem continuous_triangleVolterra {P f : ℝ × ℝ → ℝ}
    (hP : Continuous P) (hf : Continuous f) :
    Continuous (fun q : ℝ × ℝ ↦ triangleVolterra P f q.1 q.2) := by
  apply continuous_moving_interval_integral _ continuous_snd continuous_fst
  apply continuous_moving_interval_integral _ continuous_fst.snd continuous_snd
  exact (hP.mul hf).comp (continuous_fst.snd.prodMk continuous_snd)

/-- Iterated triangular Volterra operator; paper `e1a0fd5`,
`equations.tex` lines 1520–1530. -/
@[expose] noncomputable def triangleVolterraIterate (P f : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => f
  | n + 1 => fun q ↦ triangleVolterra P (triangleVolterraIterate P f n) q.1 q.2

/-- Continuity of every iterate; paper `e1a0fd5`, `equations.tex` lines 1520–1530. -/
theorem continuous_triangleVolterraIterate {P f : ℝ × ℝ → ℝ}
    (hP : Continuous P) (hf : Continuous f) (n : ℕ) :
    Continuous (triangleVolterraIterate P f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact continuous_triangleVolterra hP ih

/-- The precise pointwise factorial estimate before taking the supremum;
paper `e1a0fd5`, `equations.tex` lines 1520–1530. -/
theorem triangleVolterraIterate_bound {P f : ℝ × ℝ → ℝ} {T p B : ℝ}
    (hP : Continuous P) (hf : Continuous f) (hT : 0 ≤ T) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hkernel : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → 0 ≤ P (s, t) ∧ P (s, t) ≤ p)
    (hbound : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → |f (s, t)| ≤ B) (n : ℕ) :
    ∀ s t, 0 ≤ t → t ≤ s → s ≤ T →
      |triangleVolterraIterate P f n (s, t)| ≤ B * (p * T) ^ n / n.factorial * s ^ n := by
  induction n with
  | zero => simpa [triangleVolterraIterate] using hbound
  | succ n ih =>
    intro s t ht hts hs
    let C : ℝ := B * (p * T) ^ n / n.factorial
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hcont := continuous_triangleVolterraIterate hP hf n
    have hlo : ∀ σ z, 0 ≤ z → z ≤ σ → σ ≤ T →
        -C * σ ^ n ≤ triangleVolterraIterate P f n (σ, z) := by
      intro σ z hz hzσ hσ
      simpa [C, neg_mul] using (abs_le.mp (ih σ z hz hzσ hσ)).1
    have hhi : ∀ σ z, 0 ≤ z → z ≤ σ → σ ≤ T →
        -C * σ ^ n ≤ -triangleVolterraIterate P f n (σ, z) := by
      intro σ z hz hzσ hσ
      have hh := (abs_le.mp (ih σ z hz hzσ hσ)).2
      dsimp [C]
      linarith
    have hl := triangleVolterra_lower_step hP hcont hT hp hC ht hts hs n hkernel hlo
    have hu := triangleVolterra_lower_step hP hcont.neg hT hp hC ht hts hs n hkernel hhi
    have hneg : triangleVolterra P (-triangleVolterraIterate P f n) s t =
        -triangleVolterra P (triangleVolterraIterate P f n) s t := by
      simp only [triangleVolterra, Pi.neg_apply, mul_neg, intervalIntegral.integral_neg]
    rw [hneg] at hu
    have hid : p * T * C * (s ^ (n + 1) / (n + 1)) =
        B * (p * T) ^ (n + 1) / (n + 1).factorial * s ^ (n + 1) := by
      dsimp [C]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
      ring
    rw [neg_mul, hid] at hl hu
    change |triangleVolterra P (triangleVolterraIterate P f n) s t| ≤ _
    exact abs_le.mpr ⟨hl, by linarith⟩

/-- The uniform bound is `B (T²Pmax)^n/n!`, exactly as printed; paper
`e1a0fd5`, `equations.tex` lines 1520–1530. -/
theorem triangleVolterraIterate_uniform_bound {P f : ℝ × ℝ → ℝ} {T p B s t : ℝ}
    (hP : Continuous P) (hf : Continuous f) (hT : 0 ≤ T) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hkernel : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → 0 ≤ P (s, t) ∧ P (s, t) ≤ p)
    (hbound : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → |f (s, t)| ≤ B)
    (n : ℕ) (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ T) :
    |triangleVolterraIterate P f n (s, t)| ≤ B * (T ^ 2 * p) ^ n / n.factorial := by
  have hh := triangleVolterraIterate_bound hP hf hT hp hB hkernel hbound n s t ht hts hs
  have hs0 : 0 ≤ s := ht.trans hts
  have hpow := pow_le_pow_left₀ hs0 hs n
  have hc : 0 ≤ B * (p * T) ^ n / n.factorial := by positivity
  calc
    _ ≤ B * (p * T) ^ n / n.factorial * s ^ n := hh
    _ ≤ B * (p * T) ^ n / n.factorial * T ^ n := mul_le_mul_of_nonneg_left hpow hc
    _ = _ := by
      rw [div_mul_eq_mul_div, mul_assoc, ← mul_pow]
      congr 2
      ring

/-- The factorial bound makes the Neumann series summable at every triangular
point without a smallness condition; paper `e1a0fd5`, `equations.tex` lines 1520–1530. -/
theorem triangleVolterra_neumann_summable {P f : ℝ × ℝ → ℝ} {T p B s t : ℝ}
    (hP : Continuous P) (hf : Continuous f) (hT : 0 ≤ T) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hkernel : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → 0 ≤ P (s, t) ∧ P (s, t) ≤ p)
    (hbound : ∀ s t, 0 ≤ t → t ≤ s → s ≤ T → |f (s, t)| ≤ B)
    (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ T) :
    Summable (fun n : ℕ ↦ triangleVolterraIterate P f n (s, t)) := by
  apply ((Real.summable_pow_div_factorial (T ^ 2 * p)).mul_left B).of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, mul_div_assoc] using
    triangleVolterraIterate_uniform_bound hP hf hT hp hB hkernel hbound n ht hts hs

end AcExtensionPrinciple

end
