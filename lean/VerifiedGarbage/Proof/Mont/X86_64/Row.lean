import VerifiedGarbage.Proof.Mont.X86_64.Words
import Mathlib.Tactic.Tauto

/-!
# Montgomery arithmetic on x86-64: rows of multiply-accumulate steps

`mulSteps ts d` adds `rcx · [d]` (as many words as `ts`) to the words `ts`,
with the carry word `rbp` in and out (`mulSteps_ok`), by induction over the
words, from X25519's multiply-accumulate step.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono mulStep_ok)

/-- Registers the arithmetic can use for words: distinct, and none of `rax`,
`rcx`, `rdx`, `rbp` and `rdi`. -/
def Fresh (ts : List Reg) : Prop :=
  ts.Nodup ∧ ∀ t ∈ ts, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rbp ∧ t ≠ .rdi

theorem Fresh.tail {t : Reg} {ts : List Reg} (h : Fresh (t :: ts)) : Fresh ts :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem Fresh.head {t : Reg} {ts : List Reg} (h : Fresh (t :: ts)) :
    t ∉ ts ∧ t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rbp ∧ t ≠ .rdi :=
  ⟨(List.nodup_cons.mp h.1).1, h.2 t (List.mem_cons_self ..)⟩

/-- Closes `∀ r ∈ rs, r ∈ rs'` for literal lists of registers and variables. -/
macro "sub_regs" : tactic => `(tactic| (intro q hq; simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, List.not_mem_nil, or_false] at hq ⊢; grind))

theorem mulStep_eq (t c ai : Reg) (src : Src) :
    mulStep t c ai src = Impl.X25519.X86_64.mulStep t c ai src := rfl

/-- A row: `ts + 2^(64 |ts|) rbp = ts + rbp + rcx · [d]`. -/
theorem mulSteps_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {d : Nat},
    Scr s base size → d + 8 * ts.length ≤ size → Fresh ts →
    WP isa (.block (mulSteps ts d)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
        regsVal s ts + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rbp :: .rax :: .rdx :: ts) s s'
  | [], s, _, _, _, _, _ => WP.block_nil ⟨by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, d, hs, hd, hf => by
    obtain ⟨htn, hta, htc, htd, htb, hti⟩ := hf.head
    rw [mulSteps, mulStep_eq, WP.block_append_iff]
    refine WP.mono (mulStep_ok s (readSrc_sc hs (d := d) (by simp at hd; omega)) hta htd
      (by decide) (by decide) (by decide) htb) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simp [Ne.symm hti])
    refine WP.mono (mulSteps_ok ts hs₁ (d := d + 8) (by simp at hd; omega) hf.tail)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have g₂ : ∀ r, r ∉ Reg.rbp :: Reg.rax :: Reg.rdx :: ts → s₂.gpr r = s₁.gpr r := k₂.1
    have g₁ : ∀ r, r ∉ [t, Reg.rbp, Reg.rax, Reg.rdx] → s₁.gpr r = s.gpr r := k₁.1
    have ht₂ : s₂.gpr t = s₁.gpr t := g₂ t (by simp [htn, htb, hta, htd])
    have hc₁ : s₁.gpr .rcx = s.gpr .rcx := g₁ .rcx (by simp [Ne.symm htc])
    have hR₁ : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => g₁ q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => htn (h ▸ hq), this.2.2.2.1, this.1, this.2.2.1⟩)
    rw [k₁.2.1] at e₂
    refine ⟨?_, ?_⟩
    · rw [hR₁, hc₁] at e₂
      simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht₂]
      have h1 : (s.gpr .rcx).toNat * ((word s.mem base d).toNat + 2 ^ 64 * wordsVal s.mem base (d + 8)
          ts.length) = (s.gpr .rcx).toNat * (word s.mem base d).toNat +
          2 ^ 64 * ((s.gpr .rcx).toNat * wordsVal s.mem base (d + 8) ts.length) := by
        rw [Nat.mul_add, Nat.mul_left_comm]
      have h2 : 2 ^ 64 * 2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat =
          2 ^ 64 * (2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat) := Nat.mul_assoc _ _ _
      rw [h1, h2]
      have := readSrc_sc hs (d := d) (by simp at hd; omega)
      omega
    · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

end VG.Proof.Mont.X86_64
