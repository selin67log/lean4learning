import Mathlib
import Mathlib.Algebra.Polynomial.Basic

open Polynomial

example (x : ℝ) : (x^3 - x^2 - 16*x - 20)/(x - 5) = x^2 + 4*x + 4 := by
  sorry

example (x : ℝ) : (x^4 - 5*x^3)/(x - 5) = x^3 := by
  sorry

---partial fractions---

example (x : ℝ) : (2*x - 8)/((x - 6)*(x - 7)) = (-4)/(x - 6) + 6/(x + 7) := by
  sorry

---since you need a partial fraction for each exponent from one up---

example (x : ℝ) : (11*x + 8)/(x + 1)^2 = 11/(x + 1) + (-3)/(x + 1)^2 := by
  sorry

example (x : ℝ) : (3*x + 5)/((x - 1)*(x + 2)) = (8/3)/(x + 1) + (1/3)/(x + 2) := by
  sorry

example (x : ℝ) : 3/((x - 1)*(x - 2)) = (-3)/(x - 1) + 3/(x - 2) := by
  sorry

example (x : ℝ) : (8*x^2 + 12*x - 20) / ((x + 3) * (x^2 + x + 2)) = := by
  sorry


