import VerifiedGarbage.Proof.Poly1305.X86.Safe

/-!
# Poly1305 on x86 (32-bit): the parts of `blocks` and `finalize`, whatever the values

Untrusted: everything here is checked by Lean. Absorbing a block and the final
reduction run whatever the values (`Safe`), and compute what `Absorb.lean`
and `Reduce.lean` say where the numbers are within their bounds.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

/-- The registers `absorb` writes, and the words of the state it stores. -/
abbrev aRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]
abbrev hS : List Nat := [0, 1, 2, 3, 4, 21, 22, 23, 24]

/-- The value of the block at `bp`, from its four words, and `pad · 2¹²⁸`. -/
abbrev blkv (m : Mem) (bp : BitVec 32) (pad : Nat) : Nat :=
  wv m bp 0 + 2 ^ 32 * wv m bp 4 + 2 ^ 64 * wv m bp 8 + 2 ^ 96 * wv m bp 12 + 2 ^ 128 * pad

theorem absorb_okList (pad : BitVec 32) : okList true aRegs hS false (absorb pad) = true := rfl

/-- Absorbing the block at `esi`: it runs, and where `C` gives the bounds,
the new `h` is congruent to `(h + m + pad · 2¹²⁸) r` modulo `p`. -/
theorem absorbFull_ok {st : BitVec 32} {s : State} (hc : Ctx st s) (hb : BlkIn s)
    (hd : ∀ k < 4, (sub (s.gpr .esi) (4 * k) 4).Disjoint (sR st)) (pad : BitVec 32)
    (hpad : pad.toNat ≤ 1) {C : Prop} {r0 q1 q2 q3 : Nat}
    (hC : C → Coefs (words s.mem st) r0 q1 q2 q3 ∧ words s.mem st 4 ≤ 4) :
    WP isa (.block (absorb pad)) s fun s' => Safe st aRegs hS s s' ∧ (C → words s'.mem st 4 ≤ 4 ∧
      hw5 (words s'.mem st) % P =
        ((hw5 (words s.mem st) + blkv s.mem (s.gpr .esi) pad.toNat) * rval r0 q1 q2 q3) % P) := by
  refine WP.cond (okList_ok ⟨by decide, by decide⟩ _ false s (absorb_okList pad) hc (fun _ => hb)
    (fun h => absurd h (by decide))) fun hC' => ?_
  obtain ⟨hco, h4⟩ := hC hC'
  refine WP.mono (absorb_ok ⟨hc, words_ok _ _, rfl, fun k hk => hb (4 * k) (by omega), hd⟩ hco h4 pad
    hpad) fun s' ⟨g, A, _, _, hv, hg4⟩ => ?_
  have e : ∀ k < 32, words s'.mem st k = g k := fun k hk => A.words k hk
  simp only [hw5, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
  exact ⟨hg4, hv⟩

/-- The registers `reduce` writes. -/
abbrev rRegs : List Reg := [.eax, .ecx, .edx, .ebp]

theorem reduce_okList : okList false rRegs hS false reduce = true := by decide

/-- The final reduction: it runs, and where `h4 ≤ 4`, it leaves `h mod p`. -/
theorem reduceFull_ok {st : BitVec 32} {s : State} (hc : Ctx st s) :
    WP isa (.block reduce) s fun s' => Safe st rRegs hS s s' ∧ (words s.mem st 4 ≤ 4 →
      hw5 (words s'.mem st) = hw5 (words s.mem st) % P ∧ words s'.mem st 4 < 4) := by
  refine WP.cond (okList_ok ⟨by decide, by decide⟩ _ false s reduce_okList hc (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))) fun h4 => ?_
  refine WP.mono (reduce_ok hc (words_ok _ _) h4) fun s' ⟨g, A, _, _, hv, hg4⟩ => ?_
  have e : ∀ k < 32, words s'.mem st k = g k := fun k hk => A.words k hk
  simp only [hw5, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
  exact ⟨hv, hg4⟩

theorem restore_eq : restore = [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 100)),
    .mov .esi (.mem (at_ .eax 104)), .mov .edi (.mem (at_ .eax 108)), .mov .ebp (.mem (at_ .eax 112))] :=
  rfl

/-- Restoring the callee-saved registers from the state. -/
theorem restore_ok {st : BitVec 32} {s : State} (hc : Ctx st s) :
    WP isa (.block restore) s fun s' =>
      v s' .ebx = words s.mem st 25 ∧ v s' .esi = words s.mem st 26 ∧ v s' .edi = words s.mem st 27 ∧
      v s' .ebp = words s.mem st 28 ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem := by
  rw [restore_eq]
  refine wp_mov fun s₁ u₁ _ => ?_
  have e₁ : s₁.gpr .eax = st := by rw [u₁.gpr, hc.edi]
  have c₁ : Ctx st s₁ := hc.keep (u₁.other _ (by decide)) u₁.wr
  refine wp_movm (a := addr st (4 * 25)) (by rw [ea_at, e₁]) (c₁.inRW (by omega) (by omega))
    fun s₂ u₂ _ => ?_
  have e₂ : s₂.gpr .eax = st := by rw [u₂.other .eax (by decide), e₁]
  refine wp_movm (a := addr st (4 * 26)) (by rw [ea_at, e₂])
    (by rw [u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)) fun s₃ u₃ _ => ?_
  have e₃ : s₃.gpr .eax = st := by rw [u₃.other .eax (by decide), e₂]
  refine wp_movm (a := addr st (4 * 27)) (by rw [ea_at, e₃])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)) fun s₄ u₄ _ => ?_
  have e₄ : s₄.gpr .eax = st := by rw [u₄.other .eax (by decide), e₃]
  have r₄ : InRegions (s₄.rd ++ s₄.wr) (addr st (4 * 28)) 4 := by
    rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)
  refine wp_movm (a := addr st (4 * 28)) (by rw [ea_at, e₄]) r₄
    fun s₅ u₅ _ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [v, words, wv, wd]
    rw [u₅.other .ebx (by decide), u₄.other .ebx (by decide), u₃.other .ebx (by decide), u₂.gpr, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₅.other .esi (by decide), u₄.other .esi (by decide), u₃.gpr, u₂.mem, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₅.other .edi (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.other .esp (by decide), u₄.other .esp (by decide), u₃.other .esp (by decide),
      u₂.other .esp (by decide), u₁.other .esp (by decide)]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.Poly1305.X86
