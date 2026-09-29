import VerifiedGarbage.Proof.Poly1305.X86.Safe

/-!
# Poly1305 on x86 (32-bit): the parts of each function, whatever the values

Untrusted: everything here is checked by Lean. Absorbing a block and the final
reduction run whatever the values (`Safe`), and compute what `Absorb.lean`
and `Reduce.lean` say where the numbers are within their bounds.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

/-- The registers `absorb` writes, and the words of the state it stores. -/
abbrev aRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]
abbrev hS : List Nat := [0, 1, 2, 3, 4, 25, 26, 27, 28]

/-- The value of the block at `bp`, from its four words, and `pad · 2¹²⁸`. -/
abbrev blkv (m : Mem) (bp : BitVec 32) (pad : Nat) : Nat :=
  wv m bp 0 + 2 ^ 32 * wv m bp 4 + 2 ^ 64 * wv m bp 8 + 2 ^ 96 * wv m bp 12 + 2 ^ 128 * pad

theorem absorb_okList (pad : BitVec 32) : okList true aRegs hS false (absorb pad) = true := rfl

theorem absorbBuf_okList (pad : BitVec 32) : okList false aRegs hS false (absorbAt .edi 56 pad) = true :=
  rfl

/-- Absorbing the block at `b + d` (at `bp`, outside the state or in its
buffer): it runs, and where `C` gives the bounds, the new `h` is congruent to
`(h + m + pad · 2¹²⁸) r` modulo `p`. -/
theorem absorbAtFull_ok {st bp : BitVec 32} {s : State} (hc : Ctx st s) {b : Reg} {d : Nat} {blk : Bool}
    {pad : BitVec 32} (hok : okList blk aRegs hS false (absorbAt b d pad) = true)
    (hb : blk = true → BlkIn s) (hbase : b ≠ .eax)
    (hea : ∀ k < 4, addr (s.gpr b) (d + 4 * k) = addr bp (4 * k))
    (hrd : ∀ k < 4, InRegions (s.rd ++ s.wr) (addr bp (4 * k)) 4)
    (hd : ∀ k < 4, (sub bp (4 * k) 4).Disjoint (sR st) ∨ addr bp (4 * k) = addr st (4 * (14 + k)))
    (hpad : pad.toNat ≤ 1) {C : Prop} {r0 q1 q2 q3 : Nat}
    (hC : C → Coefs (words s.mem st) r0 q1 q2 q3 ∧ words s.mem st 4 ≤ 4) :
    WP isa (.block (absorbAt b d pad)) s fun s' => Safe st aRegs hS s s' ∧ (C → words s'.mem st 4 ≤ 4 ∧
      hw5 (words s'.mem st) % P = ((hw5 (words s.mem st) + blkv s.mem bp pad.toNat) * rval r0 q1 q2 q3) % P) := by
  refine WP.cond (okList_ok ⟨by decide, by decide⟩ _ false s hok hc hb
    (fun h => absurd h (by decide))) fun hC' => ?_
  obtain ⟨hco, h4⟩ := hC hC'
  refine WP.mono (absorb_ok ⟨hc, words_ok _ _, hbase, hea, hrd, hd⟩ hco h4 pad hpad)
    fun s' ⟨g, A, _, _, hv, hg4⟩ => ?_
  have e : ∀ k < 32, words s'.mem st k = g k := fun k hk => A.words k hk
  simp only [hw5, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
  exact ⟨hg4, hv⟩

/-- Absorbing the block at `esi`, outside the state. -/
theorem absorbFull_ok {st : BitVec 32} {s : State} (hc : Ctx st s) (hb : BlkIn s)
    (hd : ∀ k < 4, (sub (s.gpr .esi) (4 * k) 4).Disjoint (sR st)) (pad : BitVec 32)
    (hpad : pad.toNat ≤ 1) {C : Prop} {r0 q1 q2 q3 : Nat}
    (hC : C → Coefs (words s.mem st) r0 q1 q2 q3 ∧ words s.mem st 4 ≤ 4) :
    WP isa (.block (absorb pad)) s fun s' => Safe st aRegs hS s s' ∧ (C → words s'.mem st 4 ≤ 4 ∧
      hw5 (words s'.mem st) % P =
        ((hw5 (words s.mem st) + blkv s.mem (s.gpr .esi) pad.toNat) * rval r0 q1 q2 q3) % P) :=
  absorbAtFull_ok hc (absorb_okList pad) (fun _ => hb) (by decide) (fun k _ => by rw [Nat.zero_add])
    (fun k _ => hb (4 * k) (by omega)) (fun k hk => .inl (hd k hk)) hpad hC

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

theorem restore_eq : restore = [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 116)),
    .mov .esi (.mem (at_ .eax 120)), .mov .edi (.mem (at_ .eax 124)), .mov .ebp (.mem (at_ .eax 20)),
    .mov .ecx (.imm 0), .store (at_ .eax 20) .ecx] :=
  rfl

/-- Restoring the callee-saved registers from the state, and zeroing the word
that held `ebp`. -/
theorem restore_ok {st : BitVec 32} {s : State} (hc : Ctx st s) :
    WP isa (.block restore) s fun s' =>
      v s' .ebx = words s.mem st 29 ∧ v s' .esi = words s.mem st 30 ∧ v s' .edi = words s.mem st 31 ∧
      v s' .ebp = words s.mem st 5 ∧ s'.gpr .esp = s.gpr .esp ∧
      After st s s' (upd (words s.mem st) 5 0) [.eax, .ebx, .ecx, .esi, .edi, .ebp] := by
  have hfit := hc.fit
  rw [restore_eq]
  refine wp_mov fun s₁ u₁ _ => ?_
  have e₁ : s₁.gpr .eax = st := by rw [u₁.gpr, hc.edi]
  have c₁ : Ctx st s₁ := hc.keep (u₁.other _ (by decide)) u₁.wr
  refine wp_movm (a := addr st (4 * 29)) (by rw [ea_at, e₁]) (c₁.inRW (by omega) (by omega))
    fun s₂ u₂ _ => ?_
  have e₂ : s₂.gpr .eax = st := by rw [u₂.other .eax (by decide), e₁]
  refine wp_movm (a := addr st (4 * 30)) (by rw [ea_at, e₂])
    (by rw [u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)) fun s₃ u₃ _ => ?_
  have e₃ : s₃.gpr .eax = st := by rw [u₃.other .eax (by decide), e₂]
  refine wp_movm (a := addr st (4 * 31)) (by rw [ea_at, e₃])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)) fun s₄ u₄ _ => ?_
  have e₄ : s₄.gpr .eax = st := by rw [u₄.other .eax (by decide), e₃]
  have r₄ : InRegions (s₄.rd ++ s₄.wr) (addr st (4 * 5)) 4 := by
    rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)
  refine wp_movm (a := addr st (4 * 5)) (by rw [ea_at, e₄]) r₄ fun s₅ u₅ _ => ?_
  refine wp_movi fun s₆ u₆ _ => ?_
  have e₆ : s₆.gpr .eax = st := by rw [u₆.other .eax (by decide), u₅.other .eax (by decide), e₄]
  have w₆ : sR st ∈ s₆.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.wr
  refine wp_store (a := addr st (4 * 5)) (by rw [ea_at, e₆]) ⟨_, w₆, sR_contains hfit (by omega) (by omega)⟩
    fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩⟩
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .ebx (by decide), u₅.other .ebx (by decide), u₄.other .ebx (by decide),
      u₃.other .ebx (by decide), u₂.gpr, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .esi (by decide), u₅.other .esi (by decide), u₄.other .esi (by decide), u₃.gpr,
      u₂.mem, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .edi (by decide), u₅.other .edi (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .ebp (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.gpr, u₆.other .esp (by decide), u₅.other .esp (by decide), u₄.other .esp (by decide),
      u₃.other .esp (by decide), u₂.other .esp (by decide), u₁.other .esp (by decide)]
  · rw [u₇.mem, u₆.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact (words_ok s.mem st).write hfit (j := 5) (by omega) 0
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact frame_write (Frame.refl _ _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.gpr, u₆.other r hr.2.2.1, u₅.other r hr.2.2.2.2.2, u₄.other r hr.2.2.2.2.1,
      u₃.other r hr.2.2.2.1, u₂.other r hr.2.1, u₁.other r hr.1]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.Poly1305.X86
