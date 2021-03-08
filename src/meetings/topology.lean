import tactic
import analysis.special_functions.trigonometric
/-

# Topology in Lean

In this and the next meetings we will discuss how to do various areas of math in mathlib.
We will start with topology.
-/
noncomputable theory
open set topological_space filter
open_locale topological_space filter big_operators classical




#check @topological_space

example {X} {g : set (set X)} : topological_space X :=
{ is_open :=
  ⋂ (t : topological_space X) (h : ∀ s ∈ g, t.is_open s),
  { s | t.is_open s },
  is_open_univ := _,
  is_open_inter := _,
  is_open_sUnion := _ }

#check @topological_space.generate_open
/-
There is a Galois insertion between sets and topological spaces.
As in last week, this gives topological spaces the structure of a complete lattice.
However, in mathlib the order is given by *reverse* inclusion.
So e.g. `⊥` is the discrete topology and `⊤` is the indiscrete topology.
-/
#check @topological_space.complete_lattice



/-- The topology on `X × Y` is the coarsest topology
  that makes both projections continuous. -/
example {X Y : Type*} [t₁ : topological_space X]
  [t₂ : topological_space Y] : topological_space (X × Y) :=
induced prod.fst t₁ ⊓ induced prod.snd t₂




#check @continuous
#check @is_open_compl_iff
example {X Y : Type*} [topological_space X] [topological_space Y] (f : X → Y) :
  continuous f ↔ ∀ C : set Y, is_closed C → is_closed (f ⁻¹' C) :=
begin
  rw [continuous_def],
  split,
  {
    intros h C hC, rw [← is_open_compl_iff] at hC ⊢, rw [← preimage_compl], apply h, assumption,
  },
  sorry
end

example {f : ℝ → ℝ} (hf : continuous f) :
  continuous (λ x, x * f (x ^ 2 + 37)) :=
by continuity








class my_metric_space (α : Type*) :=
(dist : α → α → ℝ)
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)


/- Every metric space (as defined in mathlib) is a topological space. -/

example {X : Type} [metric_space X] (U : set X) :
  is_open U ↔ ∀ x ∈ U, ∃ ε > 0, metric.ball x ε ⊆ U :=
metric.is_open_iff

/-
The above is not quite the definition in Lean.

Suppose that `X` and `Y` are metric spaces,
we can define the topology on `X × Y` in two ways:
* the product topology of `X` and `Y`
* the topology given by the metric space `X × Y`.

These are provably the same, but not exactly the same.

To avoid this distinction,
we add the correct topological space as a field

-/

class my_metric_space2 (α : Type*) :=
(dist : α → α → ℝ)
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(topology : topological_space α)
(topology_opens : ∀ U : set α, is_open U ↔ ∀ x ∈ U, ∃ ε > 0, { y | dist x y < ε } ⊆ U)

instance my_metric_space2.topological_space {X : Type*}
  [my_metric_space2 X] : topological_space X :=
my_metric_space2.topology

example {X Y : Type*} [my_metric_space2 X] [my_metric_space2 Y] :
  my_metric_space2 (X × Y) :=
{ dist := sorry,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry,
  topology := prod.topological_space,
  topology_opens := sorry }

#print uniform_space

/- You can now define the product metric space
  where the `topology` field is the product topology. -/

/- This is still not quite the definition of metric space in mathlib,
  which is defined in terms of *uniform spaces*,
  but I won't get into that now -/




/-! ## Limits -/

/-
  We want to define multiple limits:
  * As x ⟶ a, then f(x) ⟶ b
  * As n ⟶ ∞, then a(n) ⟶ b⁻
  * As x ⟶ a⁺ (x ≠ a), then f(x) ⟶ - ∞

  If we want all combinations of a, a⁺, a⁻, ± ∞,
  possibly with the added condition that x ≠ a.
  We could even take some crazier limits, like constraining `x` to be rational.



  Even worse is the composition of limits:
  * If
    - as x ⟶ a, then f(x) ⟶ b
    - as y ⟶ b, then g(y) ⟶ c
    then
    - as x ⟶ a, then g(f(x)) ⟶ c


  For a uniform way of dealing with limits we use filters.
-/

#print filter

/- The neighborhood filter `𝓝 a` -/
#check @mem_nhds_sets_iff

/- The filter `at_top` (at ∞) -/
#check @mem_at_top_sets

/- The principal filter `𝓟 A = { B | A ⊆ B } `-/
#check @mem_principal_sets

/-
  Now we can define the limit
  * As x ⟶ a, then f(x) ⟶ b
  as follows
-/



definition simple_limit {X Y} [topological_space X]
  [topological_space Y] (f : X → Y) (a : X) (b : Y) : Prop :=
∀ V ∈ 𝓝 b, f ⁻¹' V ∈ 𝓝 a



/- In full generality, the limit is defined as follows.
  Filters are ordered by *reverse* inclusion. -/
def my_tendsto {X Y} (f : X → Y) (l₁ : filter X) (l₂ : filter Y) :=
l₁.map f ≤ l₂




lemma tendsto.comp {X Y Z} {f : X → Y} {g : Y → Z}
  {x : filter X} {y : filter Y} {z : filter Z}
  (hg : tendsto g y z) (hf : tendsto f x y) :
  tendsto (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg



/-
Here are some propositions:
* For `N` large enough, `P(N)`
* For `y` close enough to `z`, `P(y)`
* For almost every `y`, `P(y)`

These are all examples of `{x | P(x)} ∈ F`
for some filter `F`. Notation: `∀ᶠ x in F, P(x)`
-/

example {X} [topological_space X] (P : X → Prop) (y : X) :
  (∀ᶠ x in 𝓝 y, P x) ↔
  ∃ (U : set X), (∀ x ∈ U, P x) ∧ is_open U ∧ y ∈ U :=
eventually_nhds_iff

/- We can formulate topological properties
in terms of filters -/

#check @t2_iff_nhds
#print t2_space
#check @ne_bot_iff
#check @empty_in_sets_eq_bot

#print is_compact

#check @cluster_pt_iff

#check @compact_iff_finite_subcover


#check @complete_space

#print instances locally_compact_space

/- Heine-Borel -/
#check @metric.compact_iff_closed_bounded
/- ℝⁿ is "proper" -/
example (n : ℕ) : proper_space (fin n → ℝ) :=
by apply_instance


/- We can use limits to define infinite sums.
  Note: the default sum for mathlib only exists for
  absolutely convergent sequences, but has some nice properties,
  like invariance under reordering. -/

variables {I X : Type*} [topological_space X] [add_comm_group X]
  [topological_add_group X]

def my_has_sum (f : I → X) (a : X) : Prop :=
tendsto (λ A : finset I, ∑ b in A, f b) at_top (𝓝 a)

/- We can pick a value for the sum.
 This is only well-behaved if X is a T₂-space. -/
def my_tsum (f : I → X) :=
if h : ∃ a, my_has_sum f a then classical.some h else 0


example [t2_space X] (f : I → X) {a₁ a₂ : X} :
  my_has_sum f a₁ → my_has_sum f a₂ → a₁ = a₂ :=
tendsto_nhds_unique


example [t2_space X] (f : ℕ → X) :
  tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
tendsto_sum_nat_add f

