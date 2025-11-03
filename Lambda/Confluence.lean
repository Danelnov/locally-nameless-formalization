import Lambda.Properties
import Lambda.Basic
import Mathlib.Tactic

open Lambda

lemma para_subst' {M N N' : Λ} {x : ℕ} : N ⇉ N' → M[x := N] ⇉ M[x := N'] := by
  intro h₁
  induction M with
  | bvar => simp; rfl
  | fvar => simp; split; assumption; rfl
  | app => simp; apply BetaP.app <;> assumption
  | abs => simp; apply BetaP.abs; assumption

lemma para_subst {M M' N N' : Λ} {x : ℕ}
  : Lc N' → M ⇉ M' → N ⇉ N' → M[x := N] ⇉ M'[x := N'] := by
  intro lcn' hm hn
  induction hm with
  | refl => exact para_subst' hn
  | app => simp; apply BetaP.app <;> assumption
  | abs => simp; apply BetaP.abs; assumption
  | subst =>
    simp; rw [subst_open lcn', ← open₀]; apply BetaP.subst <;> aesop

lemma para_open' {M N N'} {k : ℕ} : N ⇉ N' → M{k ⇒ N} ⇉ M{k ⇒ N'} := by
  intro h
  have ⟨x, hx⟩ := exists_notFree_var M
  rw [subst_opening x hx]
  nth_rw 2 [subst_opening x hx]
  apply para_subst'; assumption

lemma para_open2' {M N N'} {k : ℕ} : Lc M → N ⇉ N' → N{k ⇒ M} ⇉ N'{k ⇒ M} := by
  intro hm h
  induction h generalizing k with
  | refl => rfl
  | abs h ih =>
    simp_all; apply BetaP.abs; simp_all
  | app h₁ h₂ ih₁ ih₂ =>
    simp; apply BetaP.app <;> simp_all
  | subst h₁ h₂ ih₁ ih₂ =>
    sorry


lemma para_notFree_cong {M M' : Λ} {x : ℕ} : (x ♯ M) → M ⇉ M' → (x ♯ M') := by
  simp; intro hx hm
  induction hm with
  | subst =>
    simp_all; apply notFree_open_conservation <;> assumption
  | _ => simp_all

lemma para_open {M M' N N' : Λ} {k : ℕ} :
  M ⇉ M' → N ⇉ N' → M{k ⇒ N} ⇉ M'{k ⇒ N'} := by
  intro hm hn
  obtain ⟨x, hxm⟩ := exists_notFree_var M
  have hxm' := para_notFree_cong hxm hm
  rw [subst_opening x hxm]
  rw [subst_opening x hxm']
  apply para_subst
  all_goals sorry
