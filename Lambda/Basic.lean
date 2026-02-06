import Mathlib.Tactic

inductive Lambda
| bvar : ℕ → Lambda
| fvar : ℕ → Lambda
| abs : Lambda → Lambda
| app : Lambda → Lambda → Lambda
deriving DecidableEq, Repr

abbrev Λ' := Lambda

prefix:100 "λ " => Lambda.abs
prefix:100 "°" => Lambda.bvar

def Lambda.toString : Λ' → String
  | bvar n => s!"°{n.repr}"
  | fvar n => n.repr
  | abs e => s!"λ {e.toString}"
  | app e₁ e₂ =>
    match e₁, e₂ with
    | abs _, _ => s!"(({e₁.toString}) {e₂.toString})"
    | _, _ => s!"({e₁.toString} {e₂.toString})"

instance : ToString Λ' := ⟨Lambda.toString⟩

instance : Repr Λ' where
  reprPrec M _ := M.toString.toFormat

instance : Coe Nat Λ' := ⟨λ n => Lambda.fvar n⟩

instance (n : Nat) : OfNat Lambda n := ⟨Lambda.fvar n⟩

namespace Lambda

@[simp]
def fv : Λ' → Finset ℕ
| bvar _ => ∅
| fvar x => {x}
| app N₁ N₂ => (fv N₁) ∪ (fv N₂)
| abs N => fv N

@[simp]
def fresh (x : ℕ) (N : Λ') := x ∉ fv N

notation x "♯" N => fresh x N

@[simp]
def subst (v : Λ') (x : ℕ) (e : Λ') :=
  match v with
  | bvar n    => °n
  | fvar y    => if x = y then e else y
  | abs N     => λ (N.subst x e)
  | app N₁ N₂ => app (N₁.subst x e) (N₂.subst x e)

notation t "[" x " := " s "]" => subst t x s

/--
  Open term `v` at index `k` with term `u`.
  That is, replace bound variable `°k` with term `u`.
-/
@[simp]
def opening (v : Λ') (k : ℕ) (u : Λ') :=
  match v with
  | bvar n => if n = k then u else °n
  | fvar y => y
  | app N₁ N₂ => app (N₁.opening k u) (N₂.opening k u)
  | abs N => λ (N.opening (k + 1) u)

notation t "{" k " ⇒ " u "}" => opening t k u

@[simp]
def open₀ t u := t{0 ⇒ u}

infixl:70 " ↑ " => open₀

/--
  Close term `v` at index `k` with variable `x`.
  That is, replace free variable `x` with bound variable `°k`.
-/
@[simp]
def closing (v : Λ') (k x : ℕ) : Λ' :=
  match v with
  | bvar n => °n
  | fvar y => if x = y then °k else y
  | app N₁ N₂ => app (N₁.closing k x) (N₂.closing k x)
  | abs N => λ (N.closing (k + 1) x)

notation t "{" k " ⇐ " x "}" => closing t k x

@[simp]
def close₀ t x := t{0 ⇐ x}

infixl:70 " ↓ " => close₀

@[simp]
def unshift (N : Λ') (c d : ℕ) : Λ' :=
  match N with
  | bvar n => °n
  | fvar x => if x < c then x else x - d
  | app N₁ N₂ => (N₁.unshift c d).app (N₂.unshift c d)
  | abs N => λ (N.unshift c d)

@[simp]
def rename (N : Λ') (π : ℕ → ℕ) :=
  match N with
  | bvar n => °n
  | fvar x => fvar $ π x
  | app N₁ N₂ => (N₁.rename π).app (N₂.rename π)
  | abs N => λ (N.rename π)

end Lambda
