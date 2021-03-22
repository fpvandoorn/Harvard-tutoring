import analysis.special_functions.trigonometric
import analysis.special_functions.integrals
import analysis.calculus.lhopital

open set real topological_space measure_theory
open_locale real topological_space big_operators ennreal

/-
# Analysis in Lean
-/

example : deriv (λ x : ℝ, x^2) 2 = 4 := by norm_num

example (x : ℝ) : deriv cos x = - sin x := by simp

example (x : ℝ) : 
  deriv (λ x, 2 * cos (cos x + 3) + 3) x = 
  2 * (sin (cos x + 3) * sin x) := 
by simp



example : ∫ x : ℝ in 0..2, x ^ 3 = 4 := by norm_num

example : ∫ x in 0..π, sin x / 2 = 1 := by norm_num

example (x : ℝ) : ∫ t in 0..x, 2 * cos t = 2 * sin x := by simp


/-
Definitions in calculus:
* Derivatives
* Iterated derivatives
* Analytic functions
* Integration

1-dimensional calculus:
* Fundamental theorem of calculus
* L'Hôpital's rule
* Intermediate value theorem

Results in multivariable calculus:
* Implicit function theorem
* Inverse function theorem
* Lagrange multipliers
* The mean value theorem (vector-valued on a convex set)

Various inequalities:
* AM-GM inequality
* Hölder's inequality
* Minkowski inequality
* Jensen's inequality
-/

/- ## Differentiation -/

/- We want to define the derivative in a general setting. -/
#check @deriv

/-
Let `E` and `F` be normed spaces over `𝕜`.
The Fréchet derivative of a map `f : E → F` 
at a point `x : E` is the continuous linear map `A : E → F`
if `∥f y - f x - A (y - x)∥ / ∥ y - x ∥ ⟶ 0` as `y ⟶ x`.

In other words:
`f y = f x + A (y - x) + o (y - x)`.
-/
#check @has_fderiv_at

#check @has_fderiv_at_iff_tendsto

#check @has_fderiv_at.unique

/- We can also consider the derivative of `f` within a set `s` at the point `x`. -/
#check @has_fderiv_within_at

#check @has_fderiv_within_at_iff_tendsto

#check @unique_diff_within_at.eq


/- `fderiv 𝕜 f x` is *the* Fréchet derivative of `f` at `x`. -/
#check @fderiv


/- If `E = 𝕜`, then all these definitions simplify by applying the linear map to `(1 : 𝕜)`, and then the derivative is just an element in `F`. -/
#check @deriv


open filter
/- As an example, here are the statements of the mean value theorem and one version of l'Hôpital's rule for functions `ℝ → ℝ` 
`Icc a b` is `[a, b]`
`Ico a b` is `[a, b)` -/
#check exists_has_deriv_at_eq_slope
#check @has_deriv_at.lhopital_zero_nhds


/-
Integrals are defined in terms of the *Bochner integral*, 
which is a generalization of the *Lebesgue integral* for Banach spaces.
-/

#check measurable_space

/- A measure on a measurable space is a countably additive function into `ℝ≥0∞`/`[0,∞]` -/
#check measure_theory.measure

example {X : Type*} [measurable_space X] (μ : measure X) : 
  μ ∅ = 0 := by simp
example {X : Type*} [measure_space X] : 
  volume (∅ : set X) = 0 := by simp

/- We can define the Lebesgue integral for nonnegative functions. -/
#check @simple_func.lintegral
#check @lintegral

example {X : Type*} [measurable_space X] (μ : measure X) 
  {f g : X → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ  :=
lintegral_add hf hg

/- `f` is `μ`-integrable if `f` is measurable and `∫ x, ∥ f ∥ ∂μ < ∞` -/
#check @has_finite_integral
#check @integrable

/- The L¹ functions are the integrable functions modulo a.e.-equality. -/
#check measure.ae
#check @Lp

/- Now we can define the Bochner integral for simple L¹ functions. Since the simple L¹ functions are dense in all L¹ functions, we can continuously extend it. -/
#check @simple_func.integral
#check @L1.integral


variables {E : Type*} [normed_group E]
  [second_countable_topology E] [complete_space E] 
  [normed_space ℝ E] [measurable_space E] [borel_space E] [second_countable_topology E]

example {X : Type*} [measurable_space X] 
  (μ : measure X) (A : set X) (f : X → E) : 
 ∫ x in A, f x ∂μ = ∫ x, f x ∂(μ.restrict A) := 
by refl

-- (μ.restrict A)(B) = μ (A ∩ B)

/- The interval integral `∫ x in a..b, f x ∂μ` is defined to be the integral on `(a,b]` if `a ≤ b`. 
-/
#check @interval_integral.integral_of_le
#check @interval_integral.integral_symm


/- Here are parts 1 & 2 of the fundamental theorem of calculus. -/
#check @interval_integral.deriv_integral_right
#check @interval_integral.integral_eq_sub_of_has_deriv_at

