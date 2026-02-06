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

lemma not_lc_bvar (n : ℕ) : ¬ Lc (°n) := by
  intro h; cases h

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

section UnshiftProperties

variable (L : Finset ℕ) (c d : ℕ)
@[simp]
private def unshift_nat (x : ℕ) := if x < c then x else x - d

private lemma exists_unshift_preimage_of_not_mem : ∃ S : Finset ℕ, ∀ y ∉ S, ∃ x ∉ L, y = unshift_nat c d x := by
  exists (L.image (unshift_nat c d .)) ∪ (Finset.Ico c (c + d))
  intro y hy
  simp at hy
  cases hy
  expose_names
  . by_cases h_lt : y < c
    -- y < c
    . exists y
      constructor
      -- y ∉ L
      . intro y_in_L
        apply left y y_in_L
        simp; intro; omega
      . simp; intro; omega
    -- y >= c
    . exists (y + d)
      have yd_lt : ¬ (y + d < c) := by omega
      constructor
      -- y - d ∉ L
      . intro yd_in_L
        apply left (y + d) yd_in_L
        simp; intro; omega
      . simp; intro; omega

end UnshiftProperties

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
    simp
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

lemma lc_unshift {c d : ℕ} {M : Λ'} : Lc M → Lc (unshift M c d) := by
  intro hm
  induction hm with
  | lc_var =>
    simp; split_ifs <;> exact lc_var
  | lc_app => simp; apply lc_app <;> aesop
  | lc_abs N L h ih =>
    simp [lc_abs_iff_body]
    simp_all
    have ⟨S, hs⟩ := exists_unshift_preimage_of_not_mem L c d
    use S
    intro y hy
    have ⟨x, ⟨xinnotL, yeq⟩⟩ := hs y hy
    have h : fvar y = (unshift (fvar x) c d) := by
      repeat (first | simp_all | split)
    have := ih x xinnotL
    rw [open_unshift, ← h] at this
    assumption

lemma lc_rename:
    Lc M ↔ ∀ π : ℕ → ℕ, Lc (M.rename π) := by
  constructor
  . intro hm π
    induction hm generalizing π with
    | lc_var => simp; constructor
    | lc_app => simp; constructor <;> aesop
    | lc_abs M L h ih =>
      simp [lc_abs_iff_body]
      use L ∪ M.fv
      intro x hx
      simp at hx
      have := ih x hx.1 (ρ π x)
      simp_all
  . intro h
    have := h id
    simp_all

end LcConservation

@[simp]
private def σ (x y : ℕ) (z : ℕ) : ℕ :=
  if z = x then y
  else if z = y then x
  else z

@[simp]
private lemma sigma_rename_lema {x y : ℕ} {N : Λ'} :
    y ∉ fv N → x ∉ fv N → N.rename (σ x y) = N := by
  intro hy hx
  induction N
  all_goals repeat (first | simp_all | split | omega)

lemma lc_abs_iff_exists_nfv_open_var {N : Λ'} : Lc (λ N) ↔ ∃ x ∉ fv N, Lc (N ↑ x) := by
  constructor
  . intro h
    cases h
    expose_names
    have ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ (fv N))
    simp at hx
    use x
    constructor
    . exact hx.2
    . exact h x hx.1
  . rintro ⟨x, ⟨xnfv, h⟩⟩
    simp [lc_abs_iff_body]
    use (N.fv ∪ {x})
    rintro y hy
    simp at hy
    rw [lc_rename] at h
    have := h (σ x y)
    simp_all




end Lc
