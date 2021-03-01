import data.rat.basic
import tactic

/-
In this file we will build "the algebraic hierarchy",
the classes of groups, rings, fields, modules etc.

To get the exercises, run:
```
leanproject get fpvandoorn/Harvard-tutoring
cp -r Harvard-tutoring/src/exercises/ Harvard-tutoring/src/my_exercises
code Harvard-tutoring
```
For this week, the exercises are in the files `my_exercises/algebraic_hierarchy.lean` and `my_exercises/order.lean`.

Also this week, think about a project you would like to formalize in Lean for the remaining weeks, and discuss it during your weekly meeting with your tutor.
-/


/-
## Notation typeclasses

We have notation typeclasses which are just there to provide notation.

If you write `[has_mul G]` then `G` will have a multiplication called `*` (satisfying no axioms).

Similarly `[has_one G]` gives you `(1 : G)`
and `[has_inv G]` gives you a map `(λ g, g⁻¹ : G → G)`
-/

#print has_mul

example {G : Type} [has_mul G] (g h : G) : g * h = h * g :=
sorry -- this is false

/-
## Groups
-/
-- `extends` is used to extend other classes
class my_group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

/-
Advantages of this approach: axioms look lovely.

Disadvantage: what if I want the group law to be `+`? I have embedded `has_mul`
in the definition.
-/








class my_add_group (G : Type) extends has_add G, has_zero G, has_neg G :=
(add_assoc : ∀ (a b c : G), a + b + c = a + (b + c))
(zero_add : ∀ (a : G), 0 + a = a)
(add_left_neg : ∀ (a : G), -a + a = 0)

attribute [to_additive] my_group

/-
Lean's solution: develop a `to_additive` metaprogram which translates all theorems about
`group`s (with group law `*`) to theorems about `add_group`s (with group law `+`).
-/

#print my_group.one_mul

namespace my_group

#print one_mul

/-
We can now prove more theorems about `my_group`, such as the following:

`mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c`
`mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y`
`mul_one (a : G) : a * 1 = a`
`mul_right_inv (a : G) : a * a⁻¹ = 1`
-/

@[to_additive] lemma mul_left_cancel {G : Type} [my_group G] (a b c : G)
  (Habac : a * b = a * c) : b = c :=
calc b = 1 * b         : by rw one_mul
   ... = (a⁻¹ * a) * b : by rw mul_left_inv
   ... = a⁻¹ * (a * b) : by rw mul_assoc
   ... = a⁻¹ * (a * c) : by sorry
   ... = (a⁻¹ * a) * c : by sorry
   ... = 1 * c         : by sorry
   ... = c             : by sorry

#check @my_group.mul_left_cancel
#check @my_add_group.add_left_cancel

variables (x y : ℚ)

example : x * y + y = y * (x + 1) :=
by { rw mul_comm, ring }

#check @mul_eq_of_eq_inv_mul

-- Abstract example of the power of classes: we can define products of groups with instances

attribute [simp] mul_assoc one_mul mul_left_inv

instance (G : Type) [my_group G] (H : Type) [my_group H] : my_group (G × H) :=
{ mul := λ gh gh', (gh.1 * gh'.1, gh.2 * gh'.2),
  one := (1, 1),
  inv := λ gh, (gh.1⁻¹, gh.2⁻¹),
  mul_assoc := by { intros a b c, cases c, cases b, cases a, dsimp at *, simp at * },
  one_mul := by tidy,
  mul_left_inv := by tidy }

-- the type class inference system now knows that products of groups are groups

example (G H K : Type) [my_group G] [my_group H] [my_group K] : my_group (G × H × K) :=
by { apply_instance }

end my_group

-- let's make a group of order two.

-- First the elements {+1, -1}
inductive mu2
| p1 : mu2
| m1 : mu2

namespace mu2

/- two preliminary facts -/
-- 1) give an algorithm to decide equality
attribute [derive decidable_eq] mu2

-- 2) prove it is finite
instance : fintype mu2 :=
⟨⟨[mu2.p1, mu2.m1], dec_trivial⟩, λ x, by { cases x; exact dec_trivial, }⟩

-- Define multiplication by doing all cases
def mul : mu2 → mu2 → mu2
| p1 p1 := p1
| p1 m1 := m1
| m1 p1 := m1
| m1 m1 := p1

-- now let's make it a group
instance : my_group mu2 :=
begin
  refine { mul := mu2.mul, one := p1, inv := id, .. },
  all_goals {exact dec_trivial},
end

end mu2

-- Now let's build rings and modules and stuff (via monoids and add_comm_groups)

-- a monoid is a group without inverses
class my_monoid (M : Type) extends has_mul M, has_one M :=
(mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c))
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

#print monoid

-- rings are additive abelian groups and multiplicative monoids,
-- with distributivity
class my_ring (R : Type) extends my_monoid R, add_comm_group R :=
(mul_add : ∀ (a b c : R), a * (b + c) = a * b + a * c)
(add_mul : ∀ (a b c : R), (a + b) * c = a * c + b * c)

-- for commutative rings, add commutativity of multiplication
class my_comm_ring (R : Type) extends my_ring R :=
(mul_comm : ∀ a b : R, a * b = b * a)

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class my_has_scalar (R : Type) (M : Type) := (smul : R → M → M)

infixr ` • `:73 := my_has_scalar.smul

-- modules over a ring
class my_module (R : Type) [my_ring R] (M : Type) [add_comm_group M]
extends my_has_scalar R M :=
(smul_add : ∀(r : R) (x y : M), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x)
(one_smul : ∀ x : M, (1 : R) • x = x)

-- for fields we let ⁻¹ be defined on the entire field, and demand 0⁻¹ = 0
-- and that a⁻¹ * a = 1 for non-zero a. This is merely for convenience;
-- one can easily check that it's mathematically equivalent to the usual
-- definition of a field.
class my_field (K : Type) extends my_comm_ring K, has_inv K :=
(zero_ne_one : (0 : K) ≠ 1)
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

-- the type of vector spaces
def my_vector_space (K : Type) [my_field K] (V : Type) [add_comm_group V] := my_module K V

/-
Let's check that we can make the rational numbers into a field.
(easy because all the work is done in the import)
-/
instance : my_field ℚ :=
{ mul := (*),
  one := 1,
  mul_assoc := rat.mul_assoc,
  one_mul := rat.one_mul,
  mul_one := rat.mul_one,
  add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_assoc := rat.add_assoc,
  zero_add := rat.zero_add,
  add_zero := rat.add_zero,
  add_left_neg := rat.add_left_neg,
  add_comm := rat.add_comm,
  mul_add := rat.mul_add,
  add_mul := rat.add_mul,
  mul_comm := rat.mul_comm,
  inv := has_inv.inv,
  zero_ne_one := rat.zero_ne_one,
  mul_inv_cancel := rat.mul_inv_cancel,
  inv_zero := inv_zero
  }


/- Some tactics that will help: -/

example {G : Type} [group G] (a b c d : G) :
 ((a * b)⁻¹ * a * 1⁻¹⁻¹⁻¹ * b * b⁻¹ * 1 * c)⁻¹ =
 (c⁻¹⁻¹ * (d * d⁻¹ * 1⁻¹⁻¹) * c⁻¹ * c⁻¹⁻¹⁻¹ * b)⁻¹⁻¹ :=
by simp

example {G : Type} [add_comm_group G] (a b : G) : (a + b) - ((b + a) + a) = -a :=
by abel -- rewriting in abelian groups

example {R : Type} [comm_ring R] (a b : R) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
by ring -- rewriting in commutative rings

example {F : Type} [field F] (a b : F) (h : a ≠ 0) : (a + b) / a = 1 + b / a :=
by field_simp -- rewriting fractions in fields



/-
# Orders

We also have an "order hierarchy".

It starts with partially ordered sets, and then goes on to lattices.

We will motivate it using subgroups.
-/

open set

-- The type of subgroups of a group G is called `subgroup G` in Lean.
-- It already has a lattice structure in Lean.

-- So let's just redo the entire theory and call it `my_subgroup G`.

/-- The type of subgroups of a group `G`. -/
structure my_subgroup (G : Type) [group G] :=
-- A subgroup of G is a sub*set* of G, called `carrier`
(carrier : set G)
-- and then axioms saying it's closed under the group structure (i.e. *, 1, ⁻¹)
(mul_mem {a b : G} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)
(one_mem : (1 : G) ∈ carrier)
(inv_mem {a : G} : a ∈ carrier → a⁻¹ ∈ carrier)

namespace my_subgroup

/-
Note in particular that we have a function `my_subgroup.carrier : my_subgroup G → set G`,
sending a subgroup of `G` to the underlying subset (`set G` is the type of subsets of G).
-/

-- Let G be a group, let H,J,K be subgroups of G, and let a,b,c be elements of G.
variables {G : Type} [group G] (H J K : my_subgroup G) (a b c : G)

/- ## Extensionality -/

lemma carrier_injective (H J : my_subgroup G) (h : H.carrier = J.carrier) : H = J :=
begin
  cases H, cases J, simp * at *,
end

-- Now let's prove that two subgroups are equal iff they have the same elements.
-- This is the most useful "extensionality lemma" so we tag it `@[ext]`.
@[ext] theorem ext {H J : my_subgroup G} (h : ∀ (x : G), x ∈ H.carrier ↔ x ∈ J.carrier) :
  H = J :=
begin
  apply carrier_injective, ext, apply h,
end

-- We also want the `iff` version of this.
theorem ext_iff {H J : my_subgroup G} : H = J ↔ ∀ (x : G), x ∈ H.carrier ↔ x ∈ J.carrier :=
begin
  sorry
end


/-
## Partial orders

-/
-- We define `H ≤ J` to mean `H.carrier ⊆ J.carrier`
-- "tidy" is a one-size-fits-all tactic which solves certain kinds of "follow your nose" goals.
instance : partial_order (my_subgroup G) :=
{ le := λ H J, H.carrier ⊆ J.carrier,
  le_refl := by tidy,
  le_trans := by tidy,
  le_antisymm := by tidy }

-- We can give a second construction using `partial_order.lift`:
example : partial_order (my_subgroup G) :=
partial_order.lift my_subgroup.carrier carrier_injective

example {H J : my_subgroup G} (h : H < J) : H ≤ J := h.le

/-
## From partial orders to lattices.

We can now show that `my_subgroup G` is a semilattice with finite meets (binary meets and a top element).
-/
def top : my_subgroup G :=
{ carrier := set.univ,
  mul_mem := begin
    sorry
  end,
  one_mem := begin
    sorry
  end,
  inv_mem := begin
    sorry
  end }

-- Add the `⊤` notation (typed with `\top`) for this subgroup:
instance : has_top (my_subgroup G) := ⟨top⟩

#check (⊤ : my_subgroup G)

/-- "Theorem" : intersection of two my_subgroups is a my_subgroup -/
definition inf (H K : my_subgroup G) : my_subgroup G :=
{ carrier := H.carrier ∩ K.carrier,
  mul_mem := begin
    sorry
  end,
  one_mem := begin
    sorry
  end,
  inv_mem := begin
    sorry
  end }

-- Add the `⊓` notation (type with `\inf`) for the intersection (inf) of two subgroups:
instance : has_inf (my_subgroup G) := ⟨inf⟩

-- We now check the four axioms for a semilattice_inf_top.

lemma le_top (H : my_subgroup G) : H ≤ ⊤ :=
begin
  sorry
end

lemma inf_le_left (H K : my_subgroup G) : H ⊓ K ≤ H :=
begin
  sorry
end

lemma inf_le_right (H K : my_subgroup G) : H ⊓ K ≤ K :=
begin
  sorry
end

lemma le_inf (H J K : my_subgroup G) (h1 : H ≤ J) (h2 : H ≤ K) : H ≤ J ⊓ K :=
begin
  sorry
end

-- Now we're ready to make the instance.
instance : semilattice_inf_top (my_subgroup G) :=
{ top := top,
  le_top := le_top,
  inf := inf,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf := le_inf,
  .. my_subgroup.partial_order }

/-
## Complete lattices
Let's now show that subgroups form a complete lattice. This has arbitrary `Inf` and `Sup`s.
First we show we can form arbitrary intersections.
-/

def Inf (S : set (my_subgroup G)) : my_subgroup G :=
{ carrier := ⋂ K ∈ S, (K : my_subgroup G).carrier,
  mul_mem :=  begin
    intros a b ha hb, simp at *, intros K hK, apply my_subgroup.mul_mem, tidy
  end,
  one_mem := begin
    sorry
  end,
  inv_mem := begin
    sorry
  end }

-- We now equip `my_subgroup G` with an Inf. The notation is `⨅`, or `\Inf`.
instance : has_Inf (my_subgroup G) := ⟨Inf⟩

instance : complete_lattice (my_subgroup G) := complete_lattice_of_Inf _ begin
  sorry
end


/-
## Galois connections

A Galois conection is a pair of adjoint functors between two
partially ordered sets, considered as categories whose hom sets Hom(H,J) have
size 1 if H ≤ J and size 0 otherwise. In other words, a Galois
connection between two partial orders α and β is a pair of monotone functions
`l : α → β` and `u : β → α` such that `∀ (a : α) (b : β), l a ≤ b ↔ a ≤ u b`.

There is an example coming from Galois theory (between subfields and subgroups),
and an example coming from classical algebraic geometry (between affine
varieties and ideals); note that in both cases you have to use the opposite
partial order on one side to make everything covariant.

The examples we want to keep in mind here are:
1) α = subsets of G, β = subgroups of G, l = "subgroup generated by", u = `carrier`
2) X : Type, α := set (set X), β := topologies on X,
  l = topology generated by a collection of open sets, u = the open sets regarded as subsets.

As you can imagine, there are a bunch of abstract theorems with simple proofs
proved for Galois connections. You can see them by `#check galois_connection`,
jumping to the definition, and reading the next 150 lines of the mathlib file
after the definition. Examples of theorems you might recognise from contexts
where you have seen this before:

lemma le_u_l (a : α) : a ≤ u (l a) := ...

lemma l_u_le (b : β) : l (u b) ≤ b := ...

lemma u_l_u_eq_u : u ∘ l ∘ u = u := ...

lemma l_u_l_eq_l : l ∘ u ∘ l = l := ...

# Galois insertions

A particularly cool kind of Galois connection is a Galois insertion, which
is a Galois connection such that `l ∘ u = id`. This is true for both
the examples we're keeping in mind (the subgroup of `G` generated
by a subgroup is the same subgroup; the topology on `X` generated by a
topology is the same topology).

Our new goal: let's make subgroups of a group into a complete lattice,
using the fact that `carrier` is part of a Galois insertion.

-/



-- The adjoint functor to the `carrier` functor is the `span` functor
-- from subsets to my_subgroups. Here we will CHEAT by using `Inf` to
-- define `span`. We could have built `span` directly with
-- an inductive definition.
def span (S : set G) : my_subgroup G := Inf {H : my_subgroup G | S ⊆ H.carrier}

-- Here are some theorems about it.
lemma monotone_carrier : monotone (my_subgroup.carrier : my_subgroup G → set G) :=
begin
  sorry
end

lemma monotone_span : monotone (span : set G → my_subgroup G) :=
begin
  sorry
end

lemma subset_span (S : set G) : S ≤ (span S).carrier :=
begin
  sorry
end

lemma span_my_subgroup (H : my_subgroup G) : span H.carrier = H :=
begin
  sorry
end

-- We have proved all the things we need to show that `span` and `carrier`
-- form a Galois insertion, using `galois_insertion.monotone_intro`.
def gi_my_subgroup : galois_insertion (span : set G → my_subgroup G) (my_subgroup.carrier : my_subgroup G → set G) :=
galois_insertion.monotone_intro monotone_carrier monotone_span subset_span span_my_subgroup

-- Note that `set G` is already a complete lattice:
example : complete_lattice (set G) := by apply_instance

-- and now `my_subgroup G` can also be made into a complete lattice, by
-- a theorem about Galois insertions. Again, I don't use `instance`
-- because we already made the instance above.

example : complete_lattice (my_subgroup G) :=
galois_insertion.lift_complete_lattice gi_my_subgroup

end my_subgroup
