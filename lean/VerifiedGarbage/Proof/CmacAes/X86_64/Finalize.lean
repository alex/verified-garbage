import VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_finalize`, the last block

Untrusted: everything here is checked by Lean. The steps that form the
counter block `C ⊕ Mₙ` in the scratch buffer before the call.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64

/-! ## XORing two blocks, a word at a time -/

/-- The memory after storing at `c` the XOR of the blocks at `p` and `q`,
a word at a time. -/
def xor2Mem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)

theorem xor2Mem_frame (m : Mem) (c p q : Addr) : Frame [⟨c, 16⟩] m (xor2Mem m c p q) := frame_store2 _ _ _

theorem xor2Mem_bytes (m : Mem) {c p q : Addr}
    (hp : (⟨c, 8⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 8⟩)
    (hq : (⟨c, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    Spec.Aes.bytesAt (xor2Mem m c p q) c 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  have g : Frame [⟨c, 8⟩] m (m.writeW c (m.readW p 64 ^^^ m.readW q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [xor2Mem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.symm) (by decide),
    g.readW (r := ⟨q + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hq.symm) (by decide)]
  exact Proof.Cmac.xor_words m p q

theorem xor_comm (x y : List Byte) : Spec.Cmac.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## Copying the last bytes -/

/-- The copy loop's body. -/
abbrev copyBody : List Instr :=
  [.movzx8 .rax lastByte, .store8 padByte .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .r8)]

theorem copyStep_ok (s : State) {P C : Addr} {i L : Nat} (hc : s.gpr .rcx = P)
    (h9 : s.gpr .r9 + BitVec.ofNat 64 2048 = C) (hi : s.gpr .r10 = BitVec.ofNat 64 i)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (C + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 i) (s.mem (P + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.gpr .rcx + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 i := by
    rw [hc, hi, BitVec.mul_one]; simp
  have ea₂ : s.gpr .r9 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (cOff : Int) = C + BitVec.ofNat 64 i := by
    rw [hi, BitVec.mul_one, ← h9, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]
    rfl
  refine ⟨_, by
    simp (config := {decide := true}) only [copyBody, lastByte, padByte, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      ea₁, ea₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, h8]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · rfl
  · rfl

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

open VG.WriteBytes in
theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Aes.bytesAt m p (i + 1) = Spec.Aes.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Aes.bytesAt, List.range_succ]

open VG.WriteBytes in
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 16) (hc : s.gpr .rcx = P)
    (h9 : s.gpr .r9 + BitVec.ofNat 64 2048 = C) (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 16, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (0 : BitVec 32)) :=
    ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, r10₁, by simp [Spec.Aes.bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  have tc : t.gpr .rcx = P := by rw [g _ (by decide) (by decide), hc]
  have t9 : t.gpr .r9 + BitVec.ofNat 64 2048 = C := by rw [g _ (by decide) (by decide), h9]
  have t8 : t.gpr .r8 = BitVec.ofNat 64 L := by rw [g _ (by decide) (by decide), h8]
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t tc t9 r10 t8
    (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ, writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i))
      (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = L
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The straight-line pieces -/

/-- Two words XORed from `[p]` and `[q]` into `[c]`, as `full`, `padK2` and
`finArgs` do. -/
theorem xor2_ok (s : State) (pb qb cb : Reg) (pd qd cd : Nat) {P Q C : Addr}
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hp8 : s.gpr pb + BitVec.ofNat 64 (pd + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq8 : s.gpr qb + BitVec.ofNat 64 (qd + 8) = Q + BitVec.ofNat 64 8)
    (hc : s.gpr cb + BitVec.ofNat 64 cd = C) (hc8 : s.gpr cb + BitVec.ofNat 64 (cd + 8) = C + BitVec.ofNat 64 8)
    (hrax : pb ≠ .rax ∧ qb ≠ .rax ∧ cb ≠ .rax)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ pb pd)), .alu .xor .rax (.mem (at_ qb qd)), .store (at_ cb cd) .rax,
        .mov .rax (.mem (at_ pb (pd + 8))), .alu .xor .rax (.mem (at_ qb (qd + 8))), .store (at_ cb (cd + 8)) .rax]
        s = some s' ∧
      s'.mem = xor2Mem s.mem C P Q ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h₁, h₂, h₃⟩ := hrax
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      h₁, h₂, h₃, ite_true, ite_false, hp, hp8, hq, hq8, hc, hc8, rp, rp8, rq, rq8, wc, wc8]
    rfl, ?_⟩
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro r hr; simp [gpr_setReg, hr]

theorem cmp16_ok (s : State) {L : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : L ≤ 16) :
    ∃ s', runBlock isa [.alu .cmp .r8 (.imm 16)] s = some s' ∧ s'.zf = some (decide (L = 16)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]; rfl,
    ?_⟩
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [zf_arithFlags, h8, show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 from rfl,
    Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem :=
  (m.writeW c (BitVec.setWidth 64 (0 : BitVec 32))).writeW (c + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zero2_bytes (m : Mem) (c : Addr) : Spec.Aes.bytesAt (zero2 m c) c 16 = Spec.Cmac.zeros 16 := by
  rw [zero2, Proof.Cmac.bytesAt_store2, zero_le8, zeros_8_8]

theorem zero_ok (s : State) {C : Addr} {L : Nat} (hc : s.gpr .r9 + BitVec.ofNat 64 2048 = C)
    (hc8 : s.gpr .r9 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8) (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (hL : L < 2 ^ 64) (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.zf = some (decide (L = 0)) ∧ s'.mem = zero2 s.mem C ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [zero, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, hc, hc8, wc, wc8]
    rfl, ?_⟩
  refine ⟨?_, rfl, ?_, rfl, rfl⟩
  · rw [zf_arithFlags]
    simp only [h8, BitVec.and_self]
    rw [beq_zero hL]
  · intro r hr; simp [gpr_setReg, hr]

theorem pad_ok (s : State) {C : Addr} {L : Nat} (hc : s.gpr .r9 + s.gpr .r8 * BitVec.ofNat 64 1 +
      BitVec.ofInt 64 (cOff : Int) = C + BitVec.ofNat 64 L) (wc : InRegions s.wr (C + BitVec.ofNat 64 L) 1) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0x80), .store8 { base := .r9, index := some .r8, disp := cOff } .rax] s =
        some s' ∧ s'.mem = s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
      State.store8, State.ea, State.setReg32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hc, wc]
    rfl, ?_⟩
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro r hr; simp [gpr_setReg, hr]

theorem args_ok (s : State) {D : Addr} (hd : s.gpr .rdx = D)
    (wd : InRegions s.wr (D + BitVec.ofNat 64 0) 8) (wd8 : InRegions s.wr (D + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0), .store (at_ .rdx 0) .rax, .store (at_ .rdx 8) .rax,
        .mov .rcx (.reg .rdx), .mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 cOff)),
        .mov32 .r8 (.imm 1)] s = some s' ∧
      s'.mem = (s.mem.writeW (D + BitVec.ofNat 64 0) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
        (D + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      s'.gpr .rcx = D ∧ s'.gpr .rdx = s.gpr .r9 + BitVec.ofNat 64 2048 ∧ s'.gpr .r8 = 1 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, hd, wd, wd8]
    rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, h₁, h₂, h₃, h₄]

open VG.WriteBytes in
/-- The padded last block `Mₙ* ‖ 10ʲ`, from the bytes copied onto zeros. -/
theorem padded_bytes (m : Mem) (C : Addr) (xs : List Byte) (hL : xs.length < 16)
    (hz : Spec.Aes.bytesAt m C 16 = Spec.Cmac.zeros 16) :
    Spec.Aes.bytesAt ((writeBytes m C xs).writeW (C + BitVec.ofNat 64 xs.length) (0x80 : Byte)) C 16 =
      xs ++ [0x80] ++ Spec.Cmac.zeros (16 - xs.length - 1) := by
  refine Proof.Cmac.ext16 (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Cmac.zeros]; omega) fun k hk => ?_
  rw [Proof.Cmac.getD_bytesAt _ _ hk, writeW8_apply]
  have hz' : m (C + BitVec.ofNat 64 k) = 0 := by
    have := congrArg (fun l => l.getD k 0) hz
    rw [Proof.Cmac.getD_bytesAt _ _ hk] at this
    rw [this]; simp only [Spec.Cmac.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk,
      ite_true, Option.getD_some]
  have hsub : (C + BitVec.ofNat 64 k - C).toNat = k := Mem.sub_ofNat_toNat C (by omega)
  have heq : (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) ↔ k = xs.length := by
    constructor
    · intro h
      have := congrArg (fun a => (a - C).toNat) h
      simp only [Mem.sub_ofNat_toNat C (show k < 2 ^ 64 by omega),
        Mem.sub_ofNat_toNat C (show xs.length < 2 ^ 64 by omega)] at this
      exact this
    · intro h; rw [h]
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, h, ite_true]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, show ¬ k < xs.length by omega, hz']
    obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega),
      hj, List.singleton_append, List.getElem?_cons_succ, Spec.Cmac.zeros, List.getElem?_replicate]
    simp only [show j < 16 - xs.length - 1 by omega, ite_true, Option.getD_some]

end VG.Proof.CmacAes.X86_64
