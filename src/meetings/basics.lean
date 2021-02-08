import data.real.basic
import data.nat.prime
/-
Assuming you have Lean installed, you can follow along this by entering in the terminal:
```
leanproject get fpvandoorn/Harvard-tutoring
code Harvard-tutoring
```
and then open `src/meetings/basics.lean` (use `ctrl + P` and type `basics` to find this file).

### Agenda
- Lean and type theory
- Logic in Lean
- Some useful tactics

There will be no new mathematical content, but we will just learn how to communicate your intentions to Lean
-/

example : 1 + 1 = 2 :=
begin
  sorry
end

example (n m : ℕ) : n + m = m + n :=
by sorry









/-
* Lean is based on type theory
* Every object in type theory is called a "term" and has a unique type
* Lean's type checker checks whether the things you write make sense
* Write `#check` to see the type of terms
-/
variables (n m : ℕ)

#check 1










/- The function `x ↦ f(x)` is written as `λ x, f x` -/

#check λ n, n + 5








/-
* In set theory ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ.
* In type theory everything has a unique type,
  but there are canonical maps `ℕ → ℤ → ℚ → ℝ → ℂ`.
* These are "coercions": Lean applies them silently.
* You can enforce that a term `t` has type `T` by writing `(t : T)`.
  This may apply a coercion
-/

#check (1 : ℤ)








/-
  A statement `P` is also a type, a term `h : P` is a proof of `P`.
  Proof checking is a special case of type checking.
-/
#check 1 + 1 = 2

#check (by reflexivity : 1 + 1 = 2)



/- On the right is the goal view, the *local context* contains *hypotheses*.
After the `⊢` is the *goal* or *target* -/
lemma modus_ponens : ∀ P Q : Prop, (P → Q) ∧ P → Q :=
begin
  sorry
end

/-
A cheatsheet:

→       if ... then       `intro`, `intros`     `apply`, `specialize`,
                                                  `have h₃ := h₁ h₂`
∀       for all           `intro`, `intros`     `apply`, `specialize`,
                                                  `have h₂ := h₁ t`
∃       there exists      `use`                 `cases`
¬       not               `intro`, `intros`     `apply`, `contradiction`
∧       and               `split`               `cases`
↔       if and only if    `split`               `cases`
∨       or                `left` / `right`      `cases`
false   contradiction                           `contradiction`, `ex_falso`
true    this is trivial!  `trivial`
-/


variables (a b c d : ℝ)
variables (h₁ : a ≤ b)
variables (h₂ : c ≤ d)

#check add_le_add h₁ h₂





def has_upper_bound (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

variables (f g : ℝ → ℝ)
theorem fn_ub_add (hfa : has_upper_bound f a) (hgb : has_upper_bound g b) :
  has_upper_bound (λ x, f x + g x) (a + b) :=
begin
  sorry
end






def has_an_upper_bound (f : ℝ → ℝ) : Prop := ∃ a : ℝ, has_upper_bound f a

example (ubf : has_an_upper_bound f) (ubg : has_an_upper_bound g) :
  has_an_upper_bound (λ x, f x + g x) :=
begin
  sorry
end






example (h : ∀ a, ∃ x, f x > a) : ¬ has_an_upper_bound f :=
begin
  sorry
end


example (x y : ℝ) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  sorry
end


/- You can use `library_search` to find a lemma in the library.
It solves goals that can  -/
example (x y : ℝ) : x < abs y → x < y ∨ x < -y :=
begin
  sorry
end





/-! Some useful tactics -/

/- `simp` generally simplifies expressions.
It guarantees that the resulting expression is equivalent to the original one. -/
example (k l : ℕ) (x : ℝ) (h : x + k ≤ x + l) : 5 * k ≤ 5 * l :=
sorry

/- `norm_num` deals with numerical calculations -/
example : 1234 < 5678 ∧ nat.prime 7 ∧ (4 : ℝ) ^ 4 / 5 ^ 4 > 1 / 3 :=
sorry

/- `ring` deals with calculations in rings -/
example (x y z : ℝ) : x * (y + z ^ 2) = z * x * z + x * y :=
sorry

/- `linarith` can chain inequalities -/
example (x y z : ℝ) (h1 : 2 * x ≤ 2 * y) (h2 : y ≤ z) : x < z + 7 :=
sorry


/- For exercises, run `leanproject get tutorials` in the terminal, and open the project using `code tutorials`.
You can solve the exercises about logic.
(The files that start with `02_`, `03_` and `04_`).
If you want, you can start with `00_` that shows some Lean tactics or
`01_` to do equational reasoning (similar to the Natural Number Game) -/