/-
Copyright (c) 2026 Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zohar Komargodski
-/
module

public import KAM.Fourier.Derivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exponential sums over `ℤⁿ`

For `x > 0` the weight `e^{-x|k|₁}` is a product over coordinates, so its sum over `ℤⁿ` is the
`n`-th power of the one-dimensional sum `∑_{m ∈ ℤ} e^{-x|m|} = (1 + e^{-x}) / (1 - e^{-x})`,
which is `coth(x/2)`, and `coth(x/2) ≤ 1 + 2/x` (blueprint `bp:p1:exp-sums` (b)). Part (a) of
that lemma is `KAM.Fourier.rpow_mul_exp_neg_le`.
-/

public section

noncomputable section

namespace KAM.Fourier

theorem exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The one-dimensional sum `∑_{m ∈ ℤ} e^{-x|m|} = (1 + e^{-x}) / (1 - e^{-x})`. -/
theorem hasSum_exp_neg_mul_abs_int {x : ℝ} (hx : 0 < x) :
    HasSum (fun m : ℤ => Real.exp (-x * |(m : ℝ)|))
      ((1 + Real.exp (-x)) / (1 - Real.exp (-x))) := by
  have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := exp_neg_lt_one hx
  have hpos : HasSum (fun n : ℕ => Real.exp (-x * |((n : ℤ) : ℝ)|)) (1 - Real.exp (-x))⁻¹ := by
    convert hasSum_geometric_of_lt_one hr0 hr1 using 1
    funext n
    rw [Int.cast_natCast, Nat.abs_cast, ← Real.exp_nat_mul]
    ring_nf
  have hneg : HasSum (fun n : ℕ => Real.exp (-x * |((-((n : ℤ) + 1) : ℤ) : ℝ)|))
      (Real.exp (-x) * (1 - Real.exp (-x))⁻¹) := by
    convert (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-x)) using 1
    funext n
    have habs : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [habs, ← pow_succ', ← Real.exp_nat_mul]
    push_cast
    ring_nf
  convert HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => Real.exp (-x * |(m : ℝ)|)) hpos hneg
    using 1
  rw [div_eq_mul_inv]
  ring

/-- `(1 + e^{-x}) / (1 - e^{-x}) = coth(x/2)`. -/
theorem one_add_exp_neg_div_eq_coth {x : ℝ} (hx : 0 < x) :
    (1 + Real.exp (-x)) / (1 - Real.exp (-x)) = Real.cosh (x / 2) / Real.sinh (x / 2) := by
  have hab : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hx2 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have hlt : Real.exp (-(x / 2)) < Real.exp (x / 2) := Real.exp_lt_exp.mpr (by linarith)
  have hden : 1 - Real.exp (-x) ≠ 0 := by
    have : Real.exp (-x) < 1 := exp_neg_lt_one hx
    linarith
  have hs : (Real.exp (x / 2) - Real.exp (-(x / 2))) / 2 ≠ 0 :=
    div_ne_zero (sub_pos.mpr hlt).ne' two_ne_zero
  rw [Real.cosh_eq, Real.sinh_eq, div_eq_div_iff hden hs, hx2]
  linear_combination Real.exp (-(x / 2)) * hab

/-- `coth(x/2) ≤ 1 + 2/x`. -/
theorem one_add_exp_neg_div_le {x : ℝ} (hx : 0 < x) :
    (1 + Real.exp (-x)) / (1 - Real.exp (-x)) ≤ 1 + 2 / x := by
  have hr := Real.exp_pos (-x)
  have hr1 : Real.exp (-x) < 1 := exp_neg_lt_one hx
  have hexp : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have key : Real.exp (-x) * x ≤ 1 - Real.exp (-x) := by
    nlinarith [mul_le_mul_of_nonneg_left hexp hr.le]
  have h2 : 2 * Real.exp (-x) ≤ 2 * (1 - Real.exp (-x)) / x := by
    rw [le_div_iff₀ hx]
    nlinarith
  rw [div_le_iff₀ (by linarith),
    show (1 + 2 / x) * (1 - Real.exp (-x)) = (1 - Real.exp (-x)) + 2 * (1 - Real.exp (-x)) / x by
      ring]
  linarith

theorem modeSize_cons {n : ℕ} (m : ℤ) (k : Fin n → ℤ) :
    modeSize (Fin.cons m k : Fin (n + 1) → ℤ) = |(m : ℝ)| + modeSize k := by
  simp [modeSize, Fin.sum_univ_succ]

/-- **Exponential sums over `ℤⁿ`** (blueprint `bp:p1:exp-sums` (b)):
`∑_{k ∈ ℤⁿ} e^{-x|k|₁} = ((1 + e^{-x}) / (1 - e^{-x}))ⁿ = coth(x/2)ⁿ`. -/
theorem hasSum_exp_neg_mul_modeSize {x : ℝ} (hx : 0 < x) :
    ∀ n : ℕ, HasSum (fun k : Fin n → ℤ => Real.exp (-x * modeSize k))
      (((1 + Real.exp (-x)) / (1 - Real.exp (-x))) ^ n)
  | 0 => by
    simp [modeSize]
  | n + 1 => by
    have ih := hasSum_exp_neg_mul_modeSize hx n
    have h1 := hasSum_exp_neg_mul_abs_int hx
    have hprod := h1.mul ih (h1.summable.mul_of_nonneg ih.summable
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
    let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun k => (k 0, Fin.tail k)
        left_inv := fun p => by simp
        right_inv := fun k => by simp }
    rw [pow_succ']
    refine e.hasSum_iff.mp ?_
    convert hprod using 1
    funext p
    show Real.exp (-x * modeSize (Fin.cons p.1 p.2 : Fin (n + 1) → ℤ)) = _
    rw [modeSize_cons, mul_add, Real.exp_add]

/-- The sum of `e^{-x|k|₁}` over `ℤⁿ` in the form `coth(x/2)ⁿ`. -/
theorem tsum_exp_neg_mul_modeSize {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∑' k : Fin n → ℤ, Real.exp (-x * modeSize k) = (Real.cosh (x / 2) / Real.sinh (x / 2)) ^ n := by
  rw [(hasSum_exp_neg_mul_modeSize hx n).tsum_eq, one_add_exp_neg_div_eq_coth hx]

end KAM.Fourier
