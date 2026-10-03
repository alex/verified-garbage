import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys
import VerifiedGarbage.Proof.Cmac.Block

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize`, the last block

The steps that form the counter block `C ⊕ Mₙ` in the scratch buffer before
the call.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64

/-- The block XOR `full`, `padK2` and `finArgs` do: the words at `pb + pd` and
`qb + qd` XORed into `cb + cd`. -/
def xor2 (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.ldr .x .x9 pb pd, .ldr .x .x10 qb qd, .logic .eor .x .x9 .x9 .x10, .str .x .x9 cb cd,
   .ldr .x .x9 pb (pd + 8), .ldr .x .x10 qb (qd + 8), .logic .eor .x .x9 .x9 .x10, .str .x .x9 cb (cd + 8)]

theorem xor2_ok (s : State) (pb qb cb : Reg) (pd qd cd : Nat) {P Q C : Addr}
    (hpd : pd % 8 = 0 ∧ pd + 8 < 32768) (hqd : qd % 8 = 0 ∧ qd + 8 < 32768)
    (hcd : cd % 8 = 0 ∧ cd + 8 < 32768)
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hp8 : s.gpr pb + BitVec.ofNat 64 (pd + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq8 : s.gpr qb + BitVec.ofNat 64 (qd + 8) = Q + BitVec.ofNat 64 8)
    (hc : s.gpr cb + BitVec.ofNat 64 cd = C) (hc8 : s.gpr cb + BitVec.ofNat 64 (cd + 8) = C + BitVec.ofNat 64 8)
    (hr : pb ≠ .x9 ∧ pb ≠ .x10 ∧ qb ≠ .x9 ∧ qb ≠ .x10 ∧ cb ≠ .x9 ∧ cb ≠ .x10)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (xor2 pb qb cb pd qd cd) s = some s' ∧
      s'.mem = Proof.Cmac.xor2Mem s.mem C P Q ∧ (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
  refine ⟨_, by
    simp (config := {decide := true}) only [xor2, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      h₁, h₂, h₃, h₄, h₅, h₆, hpd.1, hqd.1, hcd.1, Nat.add_mod_right,
      show pd < 32768 by omega, show qd < 32768 by omega, show cd < 32768 by omega, hpd.2, hqd.2, hcd.2,
      hp, hp8, hq, hq8, hc, hc8, rp, rp8, rq, rq8, wc, wc8, and_self]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl⟩
  simp only [Proof.Cmac.xor2Mem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

theorem full_eq : full = xor2 .x3 .x0 .x5 0 240 2048 := rfl
theorem padK2_eq :
    padK2 = ([.movz .x .x9 0x80 0, .strb .x9 .x6 0] : List Instr) ++ xor2 .x5 .x0 .x5 2048 256 2048 := rfl
theorem finArgs_eq : finArgs = xor2 .x5 .x2 .x5 2048 0 2048 ++
    ([.movz .x .x9 0 0, .str .x .x9 .x2 0, .str .x .x9 .x2 8, .str .x .x19 .x5 2064, .str .x .x30 .x5 2072,
     mov .x19 .x5, mov .x3 .x2, .addImm .x .x2 .x5 cOff, .movz .x .x4 1 0] : List Instr) := rfl

theorem sub16_ok (s : State) {L : Nat} (h4 : s.gpr .x4 = BitVec.ofNat 64 L) (hL : L ≤ 16) :
    ∃ s', runBlock isa [.subImm .x .x9 .x4 16] s = some s' ∧
      isa.eval (.zero .x .x9) s' = some (decide (L = 16)) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
  show some (_ == 0) = _
  simp only [State.read, gpr_write_self, BitVec.setWidth_eq, h4]
  rw [Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]

theorem zero_ok (s : State) {C : Addr} (hc : s.gpr .x5 + BitVec.ofNat 64 2048 = C)
    (hc8 : s.gpr .x5 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.mem = Proof.Cmac.zero2 s.mem C ∧ s'.gpr .x6 = C ∧
      s'.gpr .x7 = s.gpr .x3 ∧ s'.gpr .x8 = s.gpr .x4 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [zero, cOff, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, wr_write,
      ite_true, ite_false, Option.bind_some, BitVec.setWidth_eq, hc, hc8, wc, wc8]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write, ← hc], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [mem_write, Proof.Cmac.zero2, Mem.writeW, BitVec.setWidth_eq, mz0]

/-- The copy loop's body. -/
abbrev copyBody : List Instr :=
  [.ldrb .x9 .x7 0, .strb .x9 .x6 0, .addImm .x .x7 .x7 1, .addImm .x .x6 .x6 1, .subImm .x .x8 .x8 1]

theorem byte_rt (b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [show 8 * 0 = 0 from rfl, BitVec.extractLsb'_eq_self, show BitVec.ofNat 64 0 = 0#64 from rfl,
    BitVec.add_zero] at this
  exact this

theorem copyStep_ok (s : State) {A B : Addr} (ha : s.gpr .x7 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x6 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) A 1) (w : InRegions s.wr B 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧ s'.mem = s.mem.writeW B (s.mem A) ∧
      s'.gpr .x7 = s.gpr .x7 + 1 ∧ s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyBody, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, r, w]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, byte_rt, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

open VG.WriteBytes in
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 16)
    (h7 : s.gpr .x7 = P) (h6 : s.gpr .x6 = C) (h8 : s.gpr .x8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 16, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P L) ∧
      s'.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block copyBody) (c := .nonzero .x .x8)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .x7 = P + BitVec.ofNat 64 i ∧
      t.gpr .x6 = C + BitVec.ofNat 64 i ∧ t.gpr .x8 = BitVec.ofNat 64 (L - i) ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h7]; simp, by rw [h6]; simp, by rw [h8, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x7', x6', x8', g', sp', rd', wr'⟩ := copyStep_ok t
    (A := P + BitVec.ofNat 64 i) (B := C + BitVec.ofNat 64 i) (by rw [x7, BitVec.add_zero])
    (by rw [x6, BitVec.add_zero]) (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega),
      hlen]
  have hb : L < 2 ^ 64 := by omega
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev : isa.eval (.nonzero .x .x8) t' = some !decide (L - (i + 1) = 0) := by
    show some (t'.read .x .x8 != 0) = _
    rw [State.read, x8'', BitVec.setWidth_eq, ofNat_ne_zero (by omega)]
  have gg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', x6, BitVec.add_assoc, succ_ofNat, he], gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x7', x7, BitVec.add_assoc, succ_ofNat], by rw [x6', x6, BitVec.add_assoc, succ_ofNat], x8'', hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

theorem pad_ok (s : State) {B : Addr} (hb : s.gpr .x6 + BitVec.ofNat 64 0 = B) (w : InRegions s.wr B 1) :
    ∃ s', runBlock isa [.movz .x .x9 0x80 0, .strb .x9 .x6 0] s = some s' ∧
      s'.mem = s.mem.writeW B (0x80 : Byte) ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.store, Size.bits, State.read, gpr_write, wr_write, ite_true, ite_false, Option.bind_some,
      hb, w]
    rfl, ?_⟩
  refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, Nat.reduceDiv, Nat.reduceMul]
  rfl

theorem args_ok (s : State) {D S : Addr} (hd : s.gpr .x2 = D) (hs : s.gpr .x5 = S)
    (wd : InRegions s.wr (D + BitVec.ofNat 64 0) 8) (wd8 : InRegions s.wr (D + BitVec.ofNat 64 8) 8)
    (ws₁ : InRegions s.wr (S + BitVec.ofNat 64 2064) 8) (ws₂ : InRegions s.wr (S + BitVec.ofNat 64 2072) 8) :
    ∃ s', runBlock isa [.movz .x .x9 0 0, .str .x .x9 .x2 0, .str .x .x9 .x2 8, .str .x .x19 .x5 2064,
        .str .x .x30 .x5 2072, mov .x19 .x5, mov .x3 .x2, .addImm .x .x2 .x5 cOff, .movz .x .x4 1 0] s = some s' ∧
      s'.mem = (((s.mem.writeW (D + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW (D + BitVec.ofNat 64 8)
        (0 : BitVec 64)).writeW (S + BitVec.ofNat 64 2064) (s.gpr .x19)).writeW (S + BitVec.ofNat 64 2072)
        (s.gpr .x30) ∧
      s'.gpr .x3 = D ∧ s'.gpr .x2 = S + BitVec.ofNat 64 2048 ∧ s'.gpr .x4 = 1 ∧ s'.gpr .x19 = S ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x9 → r ≠ .x19 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [cOff, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, wr_write, ite_true,
      ite_false, Option.bind_some, BitVec.setWidth_eq, hd, hs, wd, wd8, ws₁, ws₂]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], rfl, by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_write, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, mz0]

end VG.Proof.CmacAes.AArch64
