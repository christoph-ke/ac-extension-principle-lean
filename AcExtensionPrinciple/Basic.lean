module

public import Mathlib

/-! Smoke test: the shared Mathlib is importable. -/

example : (2 : ℝ) + 2 = 4 := by norm_num
