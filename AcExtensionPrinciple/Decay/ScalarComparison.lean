module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Tactic

/-!
# Scalar damping comparison at AC regularity

Paper `e1a0fd5`, `equations.tex` lines 974–987,
`eq:incoming-normalized-damping` and `eq:incoming-scalar-comparison`.
The comparison is expressed using arbitrary finite majorants; this also covers
the usual supremum formulation whenever that supremum is finite.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- An AC function cannot cross an upper barrier when its derivative is nonpositive
above that barrier; paper `e1a0fd5`, `equations.tex` lines 979–980. -/
theorem ac_upper_barrier {Q : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hQ : AbsolutelyContinuousOnInterval Q a b)
    (ha : Q a ≤ M)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo a b → M < Q x → deriv Q x ≤ 0) : Q b ≤ M := by
  let F : ℝ → ℝ := fun x ↦ max (Q x - M) 0
  have hsub : AbsolutelyContinuousOnInterval (fun x ↦ Q x - M) a b :=
    hQ.sub ((LipschitzWith.const M).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hF : AbsolutelyContinuousOnInterval F a b :=
    (LipschitzWith.id.max_const 0).comp_absolutelyContinuousOnInterval hsub
  have hdF : ∀ᵐ x ∂volume, x ∈ Ioo a b → deriv F x ≤ 0 := by
    filter_upwards [hd] with x hx hxI
    have hxU : x ∈ uIcc a b := by simpa [uIcc_of_le hab] using Ioo_subset_Icc_self hxI
    have hcont : ContinuousAt Q x := hQ.continuousOn.continuousAt
      (by simpa [uIcc_of_le hab] using Icc_mem_nhds hxI.1 hxI.2)
    rcases lt_trichotomy (Q x) M with hlt | heq | hgt
    · have hevent : F =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with y hy
        exact max_eq_right (by linarith : Q y - M ≤ 0)
      rw [hevent.deriv_eq]
      simp
    · have hmin : IsLocalMin F x := by
        apply Filter.Eventually.of_forall
        intro y
        dsimp [F]
        rw [heq, sub_self, max_self]
        exact le_max_right _ _
      rw [hmin.deriv_eq_zero]
    · have hevent : F =ᶠ[𝓝 x] fun y ↦ Q y - M := by
        filter_upwards [hcont.eventually (lt_mem_nhds hgt)] with y hy
        exact max_eq_left (by linarith : 0 ≤ Q y - M)
      rw [hevent.deriv_eq, deriv_sub_const]
      exact hx hxI hgt
  have hint : (∫ x in a..b, deriv F x) ≤ 0 := by
    have hle : (∫ x in a..b, deriv F x) ≤ ∫ _x in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_ae_restrict hab hF.intervalIntegrable_deriv
        intervalIntegrable_const
      rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
        ae_restrict_iff' measurableSet_Ioo]
      exact hdF
    simpa using hle
  rw [hF.integral_deriv_eq_sub] at hint
  have hFa : F a = 0 := max_eq_right (by linarith : Q a - M ≤ 0)
  have hFb : Q b - M ≤ F b := le_max_left _ _
  linarith

/-- Damping confines `Q-L` to any finite majorant of the initial value and the
forcing. No continuity of φ is required, and even integrability of k is unused;
paper `e1a0fd5`, `equations.tex` lines 974–987 (`eq:incoming-scalar-comparison`). -/
theorem incoming_scalar_comparison_bound {Q phi k : ℝ → ℝ} {a b L M : ℝ}
    (hab : a ≤ b) (hQ : AbsolutelyContinuousOnInterval Q a b)
    (ha : |Q a - L| ≤ M) (hphi : ∀ x ∈ Icc a b, |phi x - L| ≤ M)
    (hk : ∀ᵐ x ∂volume, x ∈ Ioo a b → 0 ≤ k x)
    (hode : ∀ᵐ x ∂volume, x ∈ Ioo a b → deriv Q x = -k x * (Q x - phi x)) :
    |Q b - L| ≤ M := by
  have hup : Q b ≤ L + M := by
    apply ac_upper_barrier hab hQ (by linarith [(abs_le.mp ha).2])
    filter_upwards [hk, hode] with x hxk hxd hxI hxQ
    rw [hxd hxI]
    have hphiU := (abs_le.mp (hphi x (Ioo_subset_Icc_self hxI))).2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hxk hxI)) (by linarith)
  have hlow : -Q b ≤ -L + M := by
    apply ac_upper_barrier hab hQ.neg (by
      change -Q a ≤ -L + M
      linarith [(abs_le.mp ha).1])
    filter_upwards [hk, hode] with x hxk hxd hxI hxQ
    change -L + M < -Q x at hxQ
    rw [deriv.neg, hxd hxI]
    have hphiL := (abs_le.mp (hphi x (Ioo_subset_Icc_self hxI))).1
    have hprod := mul_nonneg (hxk hxI) (show 0 ≤ phi x - Q x by linarith)
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The usual finite supremum comparison, represented by the least-upper-bound
property rather than an unsafe real supremum of an unbounded set;
paper `e1a0fd5`, `equations.tex` lines 979–987. -/
theorem incoming_scalar_comparison {Q phi k : ℝ → ℝ} {a b L S : ℝ}
    (hab : a ≤ b) (hQ : AbsolutelyContinuousOnInterval Q a b)
    (hS : IsLUB ((fun x ↦ |phi x - L|) '' Icc a b) S)
    (hk : ∀ᵐ x ∂volume, x ∈ Ioo a b → 0 ≤ k x)
    (hode : ∀ᵐ x ∂volume, x ∈ Ioo a b → deriv Q x = -k x * (Q x - phi x)) :
    |Q b - L| ≤ max (|Q a - L|) S := by
  apply incoming_scalar_comparison_bound hab hQ (le_max_left _ _)
  · intro x hx
    exact (hS.1 ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  · exact hk
  · exact hode

end AcExtensionPrinciple

end
