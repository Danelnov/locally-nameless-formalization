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

instance (n : Nat) : OfNat LambdaLC n := ⟨⟨Lambda.fvar n, lc_var⟩⟩

namespace LambdaLC

def app (N M : Λ) : Λ := ⟨N.1.app M.1, app_lc N.2 M.2⟩
def abs (N : Λ) : Λ := ⟨λ (N.1 ↓ 0), abs_lc N.2⟩

prefix:100 "λ " => LambdaLC.abs

def subst (N : Λ) (x : ℕ) (M : Λ) : Λ := ⟨N.1[x := M.1], subst_lc N.2 M.2⟩

notation t "[" x " := " s "]" => LambdaLC.subst t x s

end LambdaLC

open LambdaLC

def x : Λ := 0
def y : Λ := 1
def z : Λ := 2

def L : Λ := (λ y.app (x.app x))[1 := 0]
def Y : Λ := λ (L.app L)

#eval Y
