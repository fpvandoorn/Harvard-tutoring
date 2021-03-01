/-
# Orders

Groups, rings, fields, modules etc are in the "algebra hierarchy".

Metric and topological spaces are in the "topology hierarchy".

The other important hierarchy is the "order hierarchy".

It starts with partially ordered sets, and then goes on to lattices.

Because I like algebra, let's demonstrate the order hierarchy by
making an algebraic type, namely the type of subgroups of a group G,
and then working up the order hierarchy with it. Subgroups of a group
are ordered by inclusion, and this is where we shall start. We will
then define infs and sups, and bot and top, and go on from there.

-/
import tactic

-- We will be using all of the theory of subsets of a type
-- without further comment (e.g. `inter_subset_left A B : A ∩ B ⊆ A`)
-- so let's open the `set` namespace.

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
sending a subgroup of `G` to the underlying subset (`set G` is the type
of subsets of G).
-/

-- Let G be a group, let H,J,K be subgroups of G, and let a,b,c be elements of G.
variables {G : Type} [group G] (H J K : my_subgroup G) (a b c : G)

/- # Extensionality

One of the first things you should consider proving about a newly-defined
type is an extensionality lemma: a sensible criterion to check that
two terms are equal. When are two subgroups of `G` equal? A subgroup
is defined by four things: a subset, and three proofs. But two proofs
of a proposition `P` are equal by definition in Lean, so two subgroups
of `G` are equal iff their underlying subsets are equal, which is
true iff their underlying subsets have the same elements. Let's give
names to these basic results because they'll show up everywhere.

Let's start by showing that two subgroups are equal if their
underlying subsets are equal. This is precisely the statement that
`∀ H J : my_subgroup G, H.carrier = J.carrier → H = J`, and a good name
for this would be `carrier_injective`. We adopt the Lean tradition
of putting as many things to the left of the `:` as we can; it
doesn't change the statement of the theorem.
-/

lemma carrier_injective (H J : my_subgroup G) (h : H.carrier = J.carrier) : H = J :=
begin
  -- take H and J apart
  cases H, cases J,
  -- and note that they are the same set, and then a bunch of proofs
  -- which are equal by definition, so it's obvious
  simp * at *,
end

-- Now let's prove that two subgroups are equal iff they have the same elements.
-- This is the most useful "extensionality lemma" so we tag it `@[ext]`.
@[ext] theorem ext {H J : my_subgroup G} (h : ∀ (x : G), x ∈ H.carrier ↔ x ∈ J.carrier) :
  H = J :=
begin
  -- it suffices to prove the subsets are equal
  apply carrier_injective,
  -- Now let's use extensionality for subsets
  ext x,
  exact h x,
end

-- We also want the `iff` version of this.
theorem ext_iff {H J : my_subgroup G} : H = J ↔ ∀ (x : G), x ∈ H.carrier ↔ x ∈ J.carrier :=
begin
  sorry
end

/-

## Partial orders

-/

-- These are familiar to most mathematicians. We will put a partial order
-- structure on `my_subgroup G`. In other words, we will create a term of
-- type `partial_order (my_subgroup G)`.

-- Let's define `H ≤ J` to mean `H.carrier ⊆ J.carrier`, using the `has_le` notation typeclass
instance : has_le (my_subgroup G) := ⟨λ H J, H.carrier ⊆ J.carrier⟩

-- "tidy" is a one-size-fits-all tactic which solves certain kinds of "follow your nose" goals.
instance : partial_order (my_subgroup G) :=
{ le := (≤),
  le_refl := by tidy,
  le_trans := by tidy,
  le_antisymm := by tidy }

/- Here is a second proof. If X → Y is injective, and Y is partially ordered,
then X inherits a partial order. This construction (it's not a theorem, because
it involves data) is called `partial_order.lift`. Applying it to the injection
`my_subgroup.carrier` and the fact that Lean already knows that `set G` is partially
ordered, turns into this second construction,  (which I won't call an `instance`
because if I did then I would have committed the sin of making two terms of
type `partial_order (my_subgroup G)`, and `partial_order (my_subgroup G)` is a class so
should have at most one instance):
-/

-- partial_order.lift is the function which pulls a partial order back along an injection.
example : partial_order (my_subgroup G) := partial_order.lift my_subgroup.carrier carrier_injective

/- Note that we magically just inherited `<` notatation, because
   `#check partial_order` tells you that `partial_order` extends `preorder`,
   which extends `has_lt`, which is a notation typeclass. In other words,
   `#check (H < J)` makes sense, and is a `Prop`. In fact `H < J` is
  defined to mean `H ≤ J ∧ ¬ (J ≤ H)`.

# From partial orders to lattices.

Let's now prove that `my_subgroup G` is a `semilattice_inf_top`. This is a class
which extends `partial_order` -- it is a partial order equipped with a top element,
and a function `inf : my_subgroup G → my_subgroup G → my_subgroup G` (called "inf" or "meet"
  or "greatest lower bound", satisfying some axioms. In our case, `top`
  will be the subgroup `G` of `G` (or more precisely `univ`), and `inf` will
  just be intersection. The work we need to do is to check that these are
  subgroups, and to prove the axioms for a `semilattice_inf_top`, which
  we'll come to later.

First let's define `top` -- the biggest subgroup. The underlying carrier
is `univ : set G`, i.e. the subset `G` of `G`. I'll leave it to you to prove
that the subgroup axioms hold!

The useful piece of interface for `univ` you'll need is `mem_univ g : g ∈ univ`.

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

-- Now `#check (⊤ : my_subgroup G)` works

/-
  We'll now prove the theorem that the intersection of
  two subgroups is a subgroup. This is a *definition* in Lean,
  indeed it is a construction which given two subgroups `H` and `K` of `G`
  produces a third subgroup `H ⊓ K` (Lean's notation for `inf H K`).

  The part of the interface for `∩` you'll need is that `a ∈ B ∩ C` is
  definitionally equal to `a ∈ B ∧ a ∈ C`, so you can use `split`
  if you have a goal `⊢ a ∈ B ∩ C`, and you can use `cases h` if you
  have a hypothesis `h : a ∈ B ∩ C`. Don't forget `mul_mem H`, `one_mem H`
  and `inv_mem H`, the axioms for `H` if `H : my_subgroup G`.
-/

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
-- They are called `le_top`, `inf_le_left`, `inf_le_right` and `le_inf`.
-- You might be able to guess the statementss of the axioms
-- from their names.

lemma le_top (H : my_subgroup G) : H ≤ ⊤ :=
begin
  sorry
end

lemma inf_le_left (H K : my_subgroup G) : H ⊓ K ≤ H :=
begin
  -- by definition this says `H.carrier ∩ K.carrier ⊆ H.carrier`
  change H.carrier ∩ K.carrier ⊆ H.carrier,
  -- now try `library_search`, to find that this is called `inter_subset_left
  apply inter_subset_left,
end

lemma inf_le_right (H K : my_subgroup G) : H ⊓ K ≤ K :=
begin
  sorry
end

-- Can you use `library_search`, or other methods, to find the name of the
-- statement that if `A B C : set G` then `A ⊆ B → A ⊆ C → A ⊆ (B ∩ C)`?
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
  .. my_subgroup.partial_order } -- don't forget to inlude the partial order

/- The logic behind `semilattice_inf_top` is that it is the simplest class
which is closed under all finite "meet"s. The meet of 0 subgroups
is `top`, the meet of one subgroup is the subgroup, the meet of two
subgroups is their inf, and for three or more you proceed by induction.

We could now go on to make a `semilattice_sup_bot` structure, and then
a lattice structure. But let's jump straight to the strongest type
in the order hierarchy -- a `complete_lattice`. This has arbitrary `Inf` and `Sup`s.

So let's first note that we can do better than finite intersections -- we can take
arbitrary intersections! Let's now define the `Inf` of an arbitrary
set of subgroups of `G`.

The part of the interface for sets you'll need to know here is that if `S` is a
set of subsets of `G`, then `⋂₀ S` is notation for their intersection, and
to work with it you'll need to know
`set.mem_sInter : g ∈ ⋂₀ S ↔ ∀ (U : set G), U ∈ S → g ∈ U`.
-/

def Inf (S : set (my_subgroup G)) : my_subgroup G :=
{ carrier := Inf (my_subgroup.carrier '' S),
  mul_mem :=  begin
    sorry
  end,
  one_mem := begin
    sorry
  end,
  inv_mem := begin
    sorry
  end }

-- We now equip `my_subgroup G` with an Inf. I think the notation is `⨅`, or `\Inf`,
-- but I find it hard to use, and `#print notation ⨅` returns garbage.
instance : has_Inf (my_subgroup G) := ⟨Inf⟩

/- # Complete lattices

Let's jump straight from `semilattice_inf_bot` to `complete_lattice`.
A complete lattice has arbitrary Infs and arbitrary Sups, and satisfies
some other axioms which you can probably imagine. Our next goal
is to make `my_subgroup G` into a complete lattice. We will do it in two ways.
The first way is to show that if our `Inf` satisfies
`(∀ (S : set (my_subgroup G)), is_glb S (Inf S))` then we can build a complete
lattice from this, using `complete_lattice_of_Inf`.
-/

instance : complete_lattice (my_subgroup G) := complete_lattice_of_Inf _ begin
-- ⊢ ∀ (s : set (my_subgroup G)), is_glb s (has_Inf.Inf s)
--  See if you can figure out what this says, and how to prove it.
-- You might find the function `is_glb.of_image` useful.
  sorry
end

/- Now let me show you another way to do this.

# Galois connections

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

example : complete_lattice (my_subgroup G) := galois_insertion.lift_complete_lattice gi_my_subgroup

end my_subgroup

-- Because Alex defined the topology generated by a collection of subsets
-- yesterday, I'll show you how you can use Galois insertions to prove
-- that if `X : Type` then the type of topological space structures on `X`
-- is a complete lattice. We use the topology generated by a collection
-- of subsets, which is a functor adjoint to the forgetful functor.

-- We start by literally copying some stuff from Alex' talk.

open set

@[ext]
class topological_space (X : Type) :=
  (is_open : set X → Prop) -- why set X → Prop not set (set X)? former plays
                           -- nicer with typeclasses later
  (univ_mem : is_open univ)
  (union : ∀ (B : set (set X)) (h : ∀ b ∈ B, is_open b), is_open (⋃₀ B))
  (inter : ∀ (A B : set X) (hA : is_open A) (hB : is_open B), is_open (A ∩ B))

namespace topological_space

def forget {X : Type} : topological_space X → set (set X) := @is_open X

/-- The open sets of the least topology containing a collection of basic sets. -/
inductive generated_open (X : Type) (g : set (set X)) : set X → Prop
| basic  : ∀ s ∈ g, generated_open s
| univ   : generated_open univ
| inter  : ∀s t, generated_open s → generated_open t → generated_open (s ∩ t)
| sUnion : ∀k, (∀ s ∈  k, generated_open s) → generated_open (⋃₀ k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from {X : Type} (g : set (set X)) : topological_space X :=
{ is_open   := generated_open X g,
  univ_mem  := sorry,
  inter     := sorry,
  union     := sorry }

-- Recall that `topological_space X` is the type of topological space structures
-- on `X`. Our Galois insertion will use the adjoint functors
-- `generate_from` and `is_open`.

-- We'd better start by giving the collection of topological space structures on X
-- a partial order:

instance (X : Type) : partial_order (topological_space X) :=
partial_order.lift (forget)
begin
  -- need to show that a top space is determined by its open sets
  intros τ₁ τ₂ h,
  cases τ₁, cases τ₂,
  simp [forget, *] at *,
end


-- Exercise (LONG): First, show that we have a Galois insertion.

lemma monotone_is_open {X : Type} :
  monotone (forget : topological_space X → set (set X)) :=
begin
  sorry
end

lemma monotone_span {X : Type} :
  monotone (generate_from : set (set X) → topological_space X) :=
begin
  sorry
end

lemma subset_forget {X : Type} (Us : set (set X)) :
  Us ≤ forget (generate_from Us) :=
begin
  sorry
end

lemma generate_forget {X : Type} (τ : topological_space X) :
  generate_from (forget τ) = τ :=
begin
  sorry
end

def gi_top (X : Type) :
  galois_insertion (generate_from : set (set X) → topological_space X)
    (forget : topological_space X → set (set X)) :=
galois_insertion.monotone_intro monotone_is_open monotone_span subset_forget generate_forget

/-
Then deduce that the type of topological space structures on X
is a complete lattice, i.e. that there is a good definition of
arbitrary Infs and Sups of topological space structures on a type, and
they satisfy all the correct properties of Infs and Sups. In
other words,
-/

example (X : Type) : complete_lattice (topological_space X) :=
  galois_insertion.lift_complete_lattice (gi_top X)

end topological_space
