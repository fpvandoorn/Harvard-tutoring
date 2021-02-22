import data.real.basic
import data.nat.prime

/- Structures and classes.

Corresponding LFTCM lectures:
* https://www.youtube.com/watch?v=xYenPIeX6MY
* https://www.youtube.com/watch?v=1W_fyjaaY0M
-/



/- The `structure` command introduces a new type (or proposition)
which is built up from existing types.
Let's start with a basic example of a structure. -/

structure complex : Type :=
(re : ℝ)
(im : ℝ)






variables (w : complex)

/- Field projections. -/
#check w.re
#check w.im

/- The "dot notation" above is short for: -/
#check complex.re w
#check complex.im w



/- Constructing values. These four lines below are exactly equivalent.
By default, the constructor of a structure is named `mk`. -/
#check complex.mk 1 2
#check (⟨1, 2⟩ : complex)
#check ({ re := 1, im := 2 } : complex)
#check { complex . re := 1, im := 2 }

/-
`{ re := ..., im := ... }` is "record constructor syntax"
and ⟨..., ...⟩ is "anonymous constructor syntax.
When the expected type is known, we can omit it from the notation.
-/

#check (show complex, from ⟨1, 2⟩)
#check (show complex, from { re := 1, im := 2 })








/- The "dot notation" is not specific to fields of structures;
it works with any qualified name (= name in a namespace).
If the type of `x` is of the form `T a1 ... an`,
then `x.y` is interpreted as `T.y x`. -/

variables (n : nat)
#check nat.prime n
#check n.prime






/- Let's add a complex conjugation function,
and prove that taking the conjugate twice is the identity. -/

def complex.conj (z : complex) : complex :=
{ re := z.re, im := - z.im }    -- or ⟨z.re, - z.im⟩

lemma complex.conj_conj (z : complex) : z.conj.conj = z :=
begin
  sorry
end




/-
Above, we manipulated the equation `z.conj.conj = z` into a form
equating two record constructor applications.
Another strategy is to reason about the two components separately.
For this we use an "extensionality" lemma:
two complex numbers are equal if they are built from the same components.
We can automatically derive this lemma using the `ext` attribute.
-/


attribute [ext] complex    -- or add `@[ext]` before `structure complex`

#check @complex.ext


/-
This strategy pairs well with lemmas which describe the components of `z.conj`.
(These can also be automatically generated using the `simps` attribute.)
-/

lemma complex.conj_re (z : complex) : z.conj.re = z.re := rfl
lemma complex.conj_im (z : complex) : z.conj.im = - z.im := rfl


example (z : complex) : z.conj.conj = z :=
begin
  sorry
end





/- Let's now look at some more interesting examples of structures. -/

structure Prime : Type :=
(val : ℕ)
(is_prime : nat.prime val)

/-
`Prime` is a type whose values correspond to the prime numbers.
A value of type `Prime` is a natural number `val`
together with a "proof" that the number `val` is prime;
or in more ordinary language, a natural number `val` such that `val` is prime.

Combining data and properties like this is sometimes called "bundling".
For example, we could call an argument `(p : Prime)` a "bundled prime number"
to distinguish it from two arguments `(p : ℕ) (hp : nat.prime p)`.
(In general "bundling" is a relative notion, and there might be
more than two possible levels of bundled-ness.)
-/

variables (p : Prime)

#check p.val
#check p.is_prime

/-
In order to construct a value of type `Prime`,
we have to provide a proof of primality.
-/
#check show Prime, from ⟨5, by norm_num⟩




/-
This example generalizes to any type and predicate on that type (or subset of that type).
-/

#check @subtype

def Prime2 : Type := { p : ℕ // p.prime }    -- or `subtype nat.prime`

-- compare:
def primes : set ℕ := { p : ℕ | p.prime }


variables (q : Prime2)

#check q.val
#check q.property




/- Other basic structures: -/
#check and

#check @prod






/-
Another important kind of "data with properties" are algebraic structures.
-/

structure monoid_structure (α : Type) : Type :=
(one : α)
(mul : α → α → α)
(mul_one : ∀ x, mul x one = x)
(one_mul : ∀ x, mul one x = x)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))



def nat_mul_monoid : monoid_structure ℕ :=
sorry


def int_mul_monoid : monoid_structure ℤ :=
sorry




#eval nat_mul_monoid.mul 2 3

#eval int_mul_monoid.mul (-1) 5





/-
Recall that the dot notation is another way to write:
-/

#eval monoid_structure.mul nat_mul_monoid 2 3

#eval monoid_structure.mul int_mul_monoid (-1) 5




namespace monoid_structure

/- Example function defined in terms of a `monoid_structure`:
power x^n of an element x of a monoid. -/
def pow {α : Type} (m : monoid_structure α) (x : α) : ℕ → α
| 0 := m.one
| (n+1) := m.mul (pow n) x

#eval nat_mul_monoid.pow 2 5

-- a^(m+n) = a^m * a^n
lemma pow_add {α : Type} (M : monoid_structure α) (a : α) (m n : ℕ) :
  M.pow a (m + n) = M.mul (M.pow a m) (M.pow a n) :=
begin
  induction n with n IH,
  { symmetry,
    apply M.mul_one },
  { calc M.pow a (m + (n + 1))
        = M.pow a ((m + n) + 1)                   : rfl
    ... = M.mul (M.pow a (m + n)) a               : rfl
    ... = M.mul (M.mul (M.pow a m) (M.pow a n)) a : by rw IH
    ... = M.mul (M.pow a m) (M.mul (M.pow a n) a) : by rw M.mul_assoc
    ... = M.mul (M.pow a m) (M.pow a (n+1))       : rfl }
end

end monoid_structure            -- end namespace




-- To use this lemma, we need to pass the `monoid_structure` explicitly.
#check nat_mul_monoid.pow_add 2 3 5






/-
We would like Lean to automatically know
to use `nat_mul_monoid` when it needs a `monoid_structure ℕ`,
and `int_mul_monoid` when it needs a `monoid_structure ℤ`.
This is what the type class system is for.
Lean maintains a database of "instances" for each "type class",
and it searches this database when it needs to infer
an argument which is passed in square brackets.
-/

/- `class` is the same as `structure`,
except it also makes the structure a type class. -/
class my_monoid (α : Type) : Type :=
(one : α)
(mul : α → α → α)
(mul_one : ∀ x, mul x one = x)
(one_mul : ∀ x, mul one x = x)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))

/- Register instances with the type class system
so they are available to instance search. -/
instance : my_monoid ℕ :=
{ one := 1,
  mul := nat.mul,
  mul_one := nat.mul_one,
  one_mul := nat.one_mul,
  mul_assoc := nat.mul_assoc }

instance : my_monoid ℤ :=
{ one := 1,
  mul := int.mul,
  mul_one := int.mul_one,
  one_mul := int.one_mul,
  mul_assoc := int.mul_assoc }


/- The monoid structure is now an argument passed in square brackets. -/
#check @monoid_structure.mul

#check @my_monoid.mul


/- This means we don't write the argument explicitly.
Instead, Lean will search its database for a matching instance. -/
#eval my_monoid.mul 2 3
#eval my_monoid.mul (-1 : ℤ) 5




namespace my_monoid

/- Square brackets tell Lean that the argument will be supplied by instance search.
It is then also available for other functions, like `mul`. -/
def pow {α : Type} [my_monoid α] (x : α) : ℕ → α
| 0 := one
| (n+1) := mul (pow n) x


/- Same as original `pow_add`, but now all explicit references
to the monoid structure are gone. -/
lemma pow_add {α : Type} [my_monoid α] (a : α) (m n : ℕ) :
  pow a (m + n) = mul (pow a m) (pow a n) :=
begin
  induction n with n IH,
  { symmetry,
    apply mul_one },
  { calc pow a (m + (n + 1))
        = pow a ((m + n) + 1)             : rfl
    ... = mul (pow a (m + n)) a           : rfl
    ... = mul (mul (pow a m) (pow a n)) a : by rw IH
    ... = mul (pow a m) (mul (pow a n) a) : by rw mul_assoc
    ... = mul (pow a m) (pow a (n+1))     : rfl }
end

end my_monoid                   -- end namespace




-- No longer need to explicitly pass the monoid structure.
#check my_monoid.pow_add 2 3 5


-- By adding notation, we could get a type like the actual lemma `pow_add`.
#check @my_monoid.pow_add

#check @pow_add




/-
Exercises:
LFTCM exercises (https://leanprover-community.github.io/lftcm2020/exercises.html)
file `wednesday/structures.lean`.
I especially recommend solving Exercises 1 and 2 from that file
and checking your answers with one of the instructors.
-/
