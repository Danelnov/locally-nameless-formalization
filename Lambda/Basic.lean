import Mathlib.Tactic

inductive Lambda
| bvar : ℕ → Lambda
| fvar : ℕ → Lambda
| abs : Lambda → Lambda
| app : Lambda → Lambda → Lambda
deriving DecidableEq, Repr

abbrev Λ := Lambda

prefix:100 "λ " => Lambda.abs
prefix:100 "°" => Lambda.bvar

def Lambda.toString : Λ → String
  | bvar n => s!"°{n.repr}"
  | fvar n => n.repr
  | abs e => s!"λ {e.toString}"
  | app e₁ e₂ =>
    match e₁, e₂ with
    | abs _, _ => s!"(({e₁.toString}) {e₂.toString})"
    | _, _ => s!"({e₁.toString} {e₂.toString})"

instance : ToString Λ := ⟨Lambda.toString⟩

instance : Repr Λ where
  reprPrec M _ := M.toString.toFormat

instance : Coe Nat Λ := ⟨λ n => Lambda.fvar n⟩

instance (n : Nat) : OfNat Lambda n := ⟨Lambda.fvar n⟩

namespace Lambda

@[simp]
def fv : Λ → Finset ℕ
| bvar _ => ∅
| fvar x => {x}
| app N₁ N₂ => (fv N₁) ∪ (fv N₂)
| abs N => fv N

@[simp]
def fresh (x : ℕ) (N : Λ) := x ∉ fv N

notation x "♯" N => fresh x N

@[simp]
def subst (v : Λ) (x : ℕ) (e : Λ) :=
  match v with
  | bvar n    => °n
  | fvar y    => if x = y then e else y
  | abs N     => λ (N.subst x e)
  | app N₁ N₂ => app (N₁.subst x e) (N₂.subst x e)

notation t "[" x " := " s "]" => subst t x s

@[simp]
def opening (v : Λ) (k : ℕ) (u : Λ) :=
  match v with
  | bvar n => if n = k then u else °n
  | fvar y => y
  | app N₁ N₂ => app (N₁.opening k u) (N₂.opening k u)
  | abs N => λ (N.opening (k + 1) u)

notation t "{" k " ⇒ " u "}" => opening t k u

@[simp]
def open₀ t u := t{0 ⇒ u}

infixl:70 " ↑ " => open₀

@[simp]
def closing (v : Λ) (k x : ℕ) : Lambda :=
  match v with
  | bvar n    => °n
  | fvar y    => if x = y then °k else y
  | app N₁ N₂ => app (N₁.closing k x) (N₂.closing k x)
  | abs N     => abs (N.closing (k + 1) x)

notation t "{" k " ⇐ "  x "}" => closing t k x

@[simp]
def close₀ t x := t{0 ⇐ x}

infixl:70 " ↓ " => close₀

end Lambda

inductive Lc : Λ → Prop
| lc_var {x : ℕ} : Lc x
| lc_app {N₁ N₂} : Lc N₁ → Lc N₂ → Lc (N₁.app N₂)
| lc_abs {N} :
  ∀ L : Finset ℕ, (∀ x : ℕ, x ∉ L → Lc (N ↑ x)) → Lc (λ N)

@[simp]
def body (N : Λ) := ∃ (L : Finset ℕ), ∀ x, x ∉ L → Lc (N ↑ x)

inductive Beta : Λ → Λ → Prop
| basis {M N : Λ} : Beta ((λ M).app N) (M.open₀ N)
| appr {M M' N : Λ}  : Beta M M' → Beta (M.app N) (M'.app N)
| appl {M M' N : Λ} : Beta M M' → Beta (N.app M) (N.app M')
| abs {M M' : Λ} : Beta M M' → Beta (λ M) (λ M')

infixl:65 " →β " => Beta

inductive BetaP : Λ → Λ → Prop
| refl {M} : BetaP M M
| abs {M M'} : BetaP M M' → BetaP (λ M) (λ M')
| app {M M' N N'} : BetaP M M' → BetaP N N' → BetaP (M.app N) (M'.app N')
| subst {M M' N N'} : BetaP M M' → BetaP N N' → BetaP ((λ M).app N) (M'.open₀ N')

infixl:65 " ⇉ " => BetaP

@[refl]
theorem BetaP_rfl {M : Λ} : M ⇉ M := BetaP.refl
