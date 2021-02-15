import data.set.basic
import data.real.basic

/-
Also see LFTCM 2020 lecture:

  https://www.youtube.com/watch?v=qlJrCtYiEkI
-/

/- Sets versus Types

Lean distinguishes different notions of "set" and "containment"
which are often treated as the same in informal mathematics.

Lean            math
====            ====
X : Type        X is a set (e.g., a metric space or a vector space)
s : set X       s is a subset of X (e.g., an open ball)
x : X           x is an element/point of X
x ∈ s           x belongs to s
t ⊆ s           t is contained in s

-/

-- A `set α` is specified by its membership predicate:
-- for each element of α, we need to say whether it is in the set.

def myset (α : Type*) := α → Prop

-- Example: Unit interval [0, 1] as a subset of ℝ

-- def unit_interval : set ℝ := λ r, 0 ≤ r ∧ r ≤ 1
def unit_interval : set ℝ := {r : ℝ | 0 ≤ r ∧ r ≤ 1}

-- #check @set.mem_def

example : (1/2 : ℝ) ∈ unit_interval :=
begin
  unfold unit_interval,
  norm_num,
end

example : (2 : ℝ) ∉ unit_interval :=
begin
  unfold unit_interval,
  norm_num,
end












/- Operations on sets

  s ∩ t        set.inter s t
  s ∪ t        set.union s t
  s \ t        set.diff s t
  sᶜ           set.compl s
  ∅            set.empty
               set.univ
  s.prod t     set.prod s t

-/

variables {α β : Type*}

def myinter (s t : set α) : set α := {x | x ∈ s ∧ x ∈ t}

def myuniv : set α := {x | true}

def myprod (s : set α) (t : set β) : set (α × β) :=
{p : α × β | p.fst ∈ s ∧ p.snd ∈ t}




/- Set extensionality

Two sets `s t : set α` are equal if and only if they have the same members,
that is, `∀ x, x ∈ s ↔ x ∈ t`.

The `ext` tactic will automatically apply extensionality theorems like this one.

-/

example (s t : set α) : s ∩ t = t ∩ s := begin
  ext,
  finish,
end

lemma set.ne_empty_iff_exists_mem (s : set α) : s ≠ ∅ ↔ ∃ x, x ∈ s := begin
  sorry
end





/- Set containment: s ⊆ t -/
def mysubset (s t : set α) : Prop := ∀ x, x ∈ s → x ∈ t


/- Let's prove commutativity of ∩ again, using `set.subset.antisymm` this time. -/

lemma inter_comm_subset (s t : set α) : s ∩ t ⊆ t ∩ s := sorry

example (s t : set α) : s ∩ t = t ∩ s := begin
  apply set.subset.antisymm;
    apply inter_comm_subset,
end




/- Exercises: From Lean for the Curious Mathematician 2020.
See https://leanprover-community.github.io/lftcm2020/exercises.html
This lecture: tuesday/sets.lean
-/


/- Bonus exercises -/

#check @set.range

def diag (α : Type*) : set (α × α) := {p : α × α | p.fst = p.snd}

example : diag α = set.range (λ x, (x, x)) := begin
  sorry
end

example (s t : set α) : s.prod t ∩ diag α ≠ ∅ ↔ s ∩ t ≠ ∅ :=
begin
  sorry
end
