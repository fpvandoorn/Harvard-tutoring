import algebra.group
import data.complex.module
import group_theory.subgroup
import group_theory.quotient_group
import linear_algebra.basic
import linear_algebra.finite_dimensional
import linear_algebra.matrix

import data.zmod.basic





-- Abstract algebra: groups, rings, fields, etc.


-- 1. GROUPS
-- We already saw the definition of a group in an earlier lecture.

#check group







-- But there's more to group theory than just groups! For example:



-- group homomorphisms...

variables {G H : Type*} [group G] [group H]

#check monoid_hom G H
#check G →* H

variables (f : G →* H)
#check (f : G → H)

section
variables (g : G)
#check f g
end

#check f.map_one
#check f.map_mul
#check f.map_inv

variables {K : Type*} [group K] (f' : H →* K)
#check f'.comp f
#check (monoid_hom.id G : G →* G)





-- subgroups & quotients...

#check subgroup G

variables (N : subgroup G)
#check (N : set G)

section
variables (g : G)
#check (g ∈ N)
end

#check N.inv_mem'

#check N.mul_mem
#check N.inv_mem

#check N.normal



section
open subgroup quotient_group

variables [normal N]

#check (1 : quotient_group.quotient N)
#check (mk' N : G →* quotient_group.quotient N)   -- g ↦ [g] ∈ G/N.

end




-- group actions...

variables {X : Type*} [mul_action G X]
variables (g : G) (x : X)
#check g • x                    -- • = \bu

variables {Y : Type*} [mul_action G Y]
#check X →[G] Y






-- and a bunch more, including:
-- * constructions of groups
--     (free groups, free abelian groups, symmetric groups, dihedral groups, ...)
-- * theorems from an undergrad abstract algebra course
--     (Lagrange's theorem, Sylow's theorems)






-- THEN, the same pattern for rings (& also Lie algebras):
-- ring homomorphisms (→+*), subrings, ideals & their quotients, modules,
-- and a fair bit of commutative algebra.
-- This is basically parallel to the story for groups.

/-
File organization: Roughly,

* `algebra/` = basic "universal algebra" stuff about groups, rings etc.
  e.g. group homomorphisms.

* `group_theory/`, `ring_theory/`, `linear_algebra/`, ... = more subject-specific.

-/


-- 2. Let's focus on the setting of LINEAR ALGEBRA.


variables {k : Type*} [field k]

variables (V : Type*) [add_comm_group V] [vector_space k V]
variables (W : Type*) [add_comm_group W] [vector_space k W]

section

variables (v₁ v₂ : V)
#check v₁ + v₂

end

#check V →ₗ[k] W

#check (show vector_space k (V →ₗ[k] W), by apply_instance)
#check (show ring (V →ₗ[k] V), by apply_instance)






-- Constructing vector spaces

#check (show vector_space k (fin 37 → k), by apply_instance)


variables {α : Type*} [fintype α]
#check (show vector_space k (α → k), by apply_instance)


variables {β : Type*}
#check (show vector_space k (β → k), by apply_instance)
#check (show vector_space k (β →₀ k), by apply_instance)




-- Dimension
open finite_dimensional

example : finite_dimensional k (fin 37 → k) :=
by apply_instance


#check vector_space.dim
example : findim k (fin 37 → k) = 37 :=
by simp


example : findim ℝ ℂ = 2 :=
complex.findim_real_complex

-- notation `dim` := findim ℝ



-- Maps between finite-dimensional vector spaces are equivalent to MATRICES.
-- In mathlib, matrices are indexed by arbitrary finite types, not just by `fin n`.
-- A matrix `A : matrix m n k` is really just a function `A : m → n → k`.

variables {m n l : Type*} [fintype m] [fintype n] [fintype l]

#check matrix m n k
#check (show vector_space k (matrix m n k), by apply_instance)

variables (A A' : matrix m n k) (B : matrix l m k)
#check A + A'
#check B.mul A    -- BA


-- Matrix notation
example : fin 3 → ℝ := ![1, 2, -3]

example : matrix (fin 2) (fin 2) ℝ := ![
  ![0, -1],
  ![1, 0]
]


--open_locale classical
--noncomputable theory

variables [decidable_eq n]

-- Equivalence between matrices and linear maps
example : matrix m n k ≃ₗ[k] ((n → k) →ₗ[k] (m → k)) :=
matrix.to_lin'

/-
If F : k^n → k^m is a linear map then the (i,j) entry of the corresponding matrix
is the i component (i.e. value on (i : m)) of F applied to the standard basis vector e_j...
but we need decidable equality on the type of j to define e_j = [ 0 ... 0 1 0 ... 0 ]ᵗ.
-/


section
def foo : fact (nat.prime 37) := show (nat.prime 37), by norm_num
local attribute [instance] foo

#check (show field (zmod 37), by apply_instance)
end
