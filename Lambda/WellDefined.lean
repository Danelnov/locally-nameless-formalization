import Lambda.Basic
import Lambda.LocalClosed
import Mathlib.Tactic

open Lc
open Lambda

def LambdaLC := { N : Λ' // Lc N }

abbrev Λ := LambdaLC

def LambdaLC.toString : Λ → String := fun ⟨M, _⟩ => Lambda.toString M

instance : ToString Λ := ⟨LambdaLC.toString⟩

instance : Repr Λ where
  reprPrec M _ := M.toString.toFormat

instance : Coe Nat Λ := ⟨fun n => ⟨Lambda.fvar n, lc_var⟩⟩
instance : Coe Λ Λ' := ⟨fun M => M.1⟩

instance (n : Nat) : OfNat LambdaLC n := ⟨⟨Lambda.fvar n, lc_var⟩⟩

namespace LambdaLC

def app (N M : Λ) : Λ := ⟨N.1.app M.1, app_lc N.2 M.2⟩
def abs (N : Λ) : Λ := ⟨(λ (N.1 ↓ 0)).unshift 1 1, lc_unshift (abs_lc N.2)⟩

prefix:100 "λ " => LambdaLC.abs

def subst (N : Λ) (x : ℕ) (M : Λ) : Λ := ⟨N.1[x := M.1], subst_lc N.2 M.2⟩

notation t "[" x " := " s "]" => LambdaLC.subst t x s

theorem rec
  {motive : Λ → Prop}
  (var : (x : ℕ) → motive x)
  (app : (N₁ N₂ : Λ) → motive N₁ → motive N₂ → motive (N₁.app N₂))
  (abs : (N : Λ) → motive N → motive (λ N))
  (N : Λ)
    : motive N
  := by
  have ⟨N', h⟩ := N
  induction h with
  | lc_var => apply var
  | lc_app _ _ ih1 ih2 => apply app _ _ ih1 ih2
  | lc_abs M L h ih =>
    sorry

inductive BetaP : Λ → Λ → Prop
| var {x : ℕ} : BetaP x x
| app {N₁ N₂ M₁ M₂} :
  BetaP N₁ N₂ → BetaP M₁ M₂ → BetaP (N₁.app M₁) (N₂.app M₂)
| abs (N M) :
  BetaP N M → BetaP (λ N) (λ M)
| reduce (N₁ N₂ M₁ M₂ : Λ) :
  BetaP N₁ N₂ → BetaP M₁ M₂ → BetaP ((N₁.abs).app M₁) (N₂[0 := M₂])

example {M : Λ} : BetaP M M := by
  have ⟨M, h⟩ := M
  induction M with
  | bvar => cases h
  | fvar x =>  apply BetaP.var
  | app N₁ N₂ ih1 ih2 =>
    cases h
    simp_all
    apply BetaP.app ih1 ih2
  | abs N ih =>

    sorry




end LambdaLC
