import geometry.manifold.instances.sphere

/-
Manifolds.

A "manifold" in mathlib means any structure on a topological space M
consisting of local charts modeled on a space H (`charted_space H M`)
for which the transition functions are required to belong to some class.

Including:
* real and complex manifolds, possibly infinite-dimensional
* Cʳ manifolds for 0 ≤ r ≤ ∞
* manifolds with boundary/corners

More potential examples:
* PL manifolds (over any ordered field)
* oriented manifolds
* symplectic manifolds (via Darboux's theorem)

Non-examples:
* A Riemannian manifold is a manifold with extra structure
  (an inner product on the tangent bundle).
* Likewise, a Lie group is a manifold with a compatible group structure.
* A scheme is not a manifold (no fixed model space).

In math we usually require a manifold to be second countable and Hausdorff.
These conditions are not part of the mathlib definition, but can be added
as required.
-/


/-
An outline of the manifold library:

1. Charted spaces:
   the local model, and the data of a manifold (in a broad sense).
-/

#check @local_homeomorph
#check @charted_space

/-
2. Structure groupoids:
   conditions on the transition maps (e.g., smoothness).
-/

#check @structure_groupoid
#check @has_groupoid
#check @structomorph

/-
3. Models with corners:
   the Cʳ structure groupoids for Euclidean manifolds.
-/

#check @model_with_corners
#check @times_cont_diff_groupoid

/-
4. Smooth maps and diffeomorphisms.
-/

#check @times_cont_mdiff
#check @smooth

/-
5. Example: the sphere
-/

#check @metric.sphere.smooth_manifold_with_corners
