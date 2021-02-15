import tactic.omega
import data.real.basic
import data.real.sqrt
import data.nat.prime
import data.nat.factorial


/- Dealing with numbers:

  ℕ    natural numbers
  ℤ    integers
  ℚ    rational numbers
  ℝ    real numbers
  ℂ    complex numbers

Tactics:

  norm_num, linarith, ring, norm_cast, field_simp, omega

Also see LFTCM 2020 lecture:

  https://www.youtube.com/watch?v=iEs2U_kzYy4

-/

example : 2 + 3 = 5 := rfl
example : 1 + 2 + 3 = 6 := by refl
example : 2 + 3 = 5 := begin
  refl
end

example : 2000000 + 3000000 = 5000000 := by norm_num






example : 2 * 3 = 6 := rfl




example : 2 - 3 = 0 := rfl      -- "Totalization" of a partial function (subtraction : ℕ × ℕ → ℕ)
example : 2 / 3 = 0 := rfl






example : (2 : ℤ) - 3 = -1 := rfl
example : (2 : ℚ) - 3 = -1 := rfl
example : (2 : ℝ) - 3 = -1 := by norm_num

#print notation -
#check @has_sub.sub

#check (show has_sub ℤ, by apply_instance)
#check int.has_sub









example : nat.prime 65537 := by norm_num
example : ¬ nat.prime 65538 := by norm_num
example : nat.factorial 6 = 720 := by norm_num




-- `omega` can prove theorems in the language (ℕ, 0, 1, +, <).

example (i j n : ℕ) (h₁ : i ≤ j) (h₂ : j < n) : i + (j - i + 1) + (n - 1 - j) = n :=
begin
  omega,
  -- alternatively: prove equality of integers,
  -- using tools like `norm_cast` & `ring`
end






open real

example (r : ℝ) (hr : r*r + r - 1 = 0) (rpos : r > 0) : r = (sqrt 5 - 1) / 2 :=
begin
  have : (r - (sqrt 5 - 1) / 2) * (r - (- sqrt 5 - 1) / 2) = r*r + r - 1,
  { ring,
    norm_num,
    ring, },
  rw hr at this,
  rw mul_eq_zero at this,
  cases this with h h,
  { linarith,
},
  sorry
end

example (x : ℝ) (hx : x ≠ 0) : x / x^2 = 1 / x :=
begin
  -- field_simp,
  ring,
end



/- Exercises: From Lean for the Curious Mathematician 2020.
See https://leanprover-community.github.io/lftcm2020/exercises.html
This lecture: tuesday/numbers.lean
-/
