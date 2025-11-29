import Mathlib.Tactic
import Lambda.Basic
import Lambda.Properties

open Lambda

inductive Lc : Λ' → Prop
| lc_var {x : ℕ} : Lc x
| lc_app {N₁ N₂} : Lc N₁ → Lc N₂ → Lc (N₁.app N₂)
| lc_abs (N) :
  ∀ L : Finset ℕ, (∀ x ∉ L, Lc (N ↑ x)) → Lc (λ N)

@[simp]
def body (N : Λ') : Prop := ∃ L : Finset ℕ, ∀ x ∉ L, Lc (N ↑ x)

namespace Lc

lemma lc_abs_iff_body (N : Λ') : Lc (λ N) ↔ body N := by
  constructor <;> simp_all
  . intro h
    cases h; expose_names; exists L
  . intro L h
    apply Lc.lc_abs
    assumption

@[simp]
lemma open_rec_lc {M N : Λ'} {k : ℕ} : Lc M → M{k ⇒ N} = M := by
  intro h
  induction h generalizing k with
  | lc_abs _ L h ih =>
    simp_all
    have ⟨x, hx⟩ := Infinite.exists_notMem_finset L
    apply opening_lc_lemma
    exact Ne.symm (Nat.zero_ne_add_one k)
    apply ih
    assumption
  | _ => simp_all

lemma subst_open {M N L : Λ'} {x k : ℕ} :
  Lc L → M{k ⇒ N}[x := L] = M[x := L]{k ⇒ N[x := L]} := by
  intro h
  induction M generalizing k with
  | bvar => simp; split; rfl; simp
  | fvar => simp_all; split <;> simp_all
  | _ => simp_all

lemma subst_open_var {x y : ℕ} {N M : Λ'} :
    Lc M → x ≠ y → (N[x := M]) ↑ y = (N ↑ y)[x := M] := by
  intros
  simp; rw [subst_open]
  aesop; assumption

section LcConservation

variable {M N : Λ'}

lemma opening_lc {N : Λ'} {k : ℕ} : Lc M → Lc (M{k ⇒ N}) := by aesop

@[aesop safe]
lemma open₀_lc {N : Λ'} : Lc M → Lc (M ↑ N) := by simp; aesop

@[aesop safe]
lemma app_lc : Lc M → Lc N → Lc (M.app N) := by
  intro hm hn; apply lc_app <;> assumption

lemma subst_lc {x : ℕ} : Lc M → Lc N → Lc (M[x := N]) := by
  intro hm hn
  induction hm with
  | lc_var =>
    simp; split; assumption; apply lc_var
  | lc_app =>
    simp; apply lc_app <;> aesop
  | lc_abs M L h ih =>
    simp [lc_abs_iff_body]
    use L ∪ {x}
    intro y hy
    rw [← open₀, subst_open_var hn (by aesop)]
    apply ih
    aesop

@[simp]
lemma subst_as_close_open {x k z : ℕ} : Lc N → N{k ⇐ x}{k ⇒ z} = N[x := z] := by
  intro hn
  induction hn generalizing k with
  | lc_var => simp; split <;> simp
  | lc_app => simp_all
  | lc_abs N L h ih =>
    simp
    have ⟨y, hy⟩ :=
      let N₁ := N{k + 1 ⇐ x}{k + 1 ⇒ z}
      let N₂ := N[x := z]
      Infinite.exists_notMem_finset (L ∪ {x} ∪ N.fv ∪ N₁.fv ∪ N₂.fv)
    simp at hy
    have := @ih y hy.2.1 (k + 1)
    rw [
      open₀, ← open_close_var (by aesop) (by aesop) (by aesop),
      ← open₀, ← open₀, ← subst_open_var lc_var (by aesop)
    ] at this
    apply @open₀_injective y <;> simp
    . exact hy.2.2.2.1
    . exact hy.2.2.2.2
    exact this

lemma abs_lc : Lc M → Lc (λ (M ↓ 0)) := by
  intro h
  apply lc_abs
  intros
  simp_all
  apply subst_lc
  assumption
  exact lc_var
  use {1}
  aesop

end LcConservation
end Lc
