import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02

/-
# Algebraic structures

Objectives :

- Recognize concrete instances of structures. (e.g. ℤ, ℚ and ℝ are all ordered rings.)
- Support for generic notation
  (When we write `*`, Lean should figure out which multiplication we mean on its own)
- Possibility to extend algebraic structure. (A commutative ring is still a ring.)
-/

example : 2 * 3 ≤ (2 : ℝ) * 4 := by apply mul_le_mul <;> norm_num

/-
`α` is a parameter; we are defining a group structure on `α`.

We use a definition with minimal proof obligation. (`mul_inv_cancel` is "missing".)
-/
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

/-
Mathlib's definition of a group.
-/
#check Group
#print Group

structure Grp₁ where
  α : Type*
  str : Group₁ α

section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)
#print Equiv

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)


/- Example of **coercion**. -/
example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

#check ((f : α ≃ β).trans (g : β ≃ γ) : α ≃ γ)
/- Reverse order as function composition. -/
example : (f.trans g : α → γ) = g ∘ f :=
  rfl

end

example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl

def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

/- This is in Mathlib. -/
#check Equiv.Perm.permGroup


/- There is a difference between `Group` and `AddGroup`.
The names of the fields link to the notation we use;
it is also important when it comes to extend these structures.
-/

structure AddGroup₁ (α : Type*) where
  (add : α → α → α)
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point := ⟨- a.x, - a.y, - a.z⟩

def zero : Point := ⟨0,0,0⟩

theorem zero_def : zero = ⟨0,0,0⟩ := rfl

def addGroupPoint : AddGroup₁ Point where
  add := add
  zero := zero
  neg := neg
  add_assoc x y z := by simp [add, add_assoc]
  add_zero x := by simp [add, zero]
  zero_add := by simp [add, zero]
  neg_add_cancel x := by
    simp only [add, neg, neg_add_cancel, zero]

end Point

/-
We now know :
- How to define algebraic structures
- How to define instances of them.

Let's now try to associate notation.
-/

section
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

end

/-
Whereas an annotation `(grp : Group G)` tells Lean that it
should expect to be given that argument explicitly.

The annotation `{grp : Group G}` tells Lean that it should try
to figure it out from contextual cues in the expression.

The annotation `[grp : Group G]` tells Lean that the
corresponding argument should be synthesized using
**type class inference**.
Usually we can omit the `grp` for these.
-/

/-
To use the type class inference we register the structure as a **class** instead.
We can then use the `instance` keyword to register particular instances.
-/

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

#check Group₁.mul
#check Group₂.mul

instance ExampleInstanceUsingGroup₂ {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

/- Using our `Group₂` instance on `Perm`-/
example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f := by
  rfl

end

instance : Add Point where add := Point.add

section
/- Defining notation for a specific algebraic structure. -/
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

/- We can do this for all groups! -/
instance (priority := high) hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance (priority := high) hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance (priority := high) hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end
