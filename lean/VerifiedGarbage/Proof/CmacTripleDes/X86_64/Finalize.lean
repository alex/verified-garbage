import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_finalize`, the last block

The steps that form the last block `Mₙ` (§6.2 step 4) in `rax`, as a
little-endian word: `Mₙ* ⊕ K1` for a complete last block, else `Mₙ*` copied a
byte at a time onto the zeroed slot 12, `0x80` after it, XORed with `K2`.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes VG.Proof.Cmac

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them) and the scratch buffer `S`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L : Nat) : Prop where
  rdi : s₀.gpr .rdi = W
  rsi : s₀.gpr .rsi = St
  rdx : s₀.gpr .rdx = P
  rcx : (s₀.gpr .rcx).toNat = L
  r8 : s₀.gpr .r8 = S
  rd : s₀.rd = [⟨W, 400⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 8⟩, ⟨S, 640⟩]
  key_st : (⟨W, 400⟩ : Region).Disjoint ⟨St, 8⟩
  key_scr : (⟨W, 400⟩ : Region).Disjoint ⟨S, 640⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 8⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 640⟩
  st_scr : (⟨St, 8⟩ : Region).Disjoint ⟨S, 640⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 8⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 640⟩
  key_wrap : W.toNat + 400 ≤ 2 ^ 64
  st_wrap : St.toNat + 8 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 640 ≤ 2 ^ 64
  len : L ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeX86_64.pre s₀) :
    FPre s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) (s₀.gpr .rcx).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- Slot 12, where a partial last block is formed. -/
abbrev slot12 (S : Addr) : Region := ⟨S + BitVec.ofNat 64 96, 8⟩

/-- What the branch on the length leaves: `Mₙ` in `rax`. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W
  r15 : s.gpr .r15 = S
  rbp : s.gpr .rbp = St
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [slot12 S] (savedMem s₀ S) s.mem
  blk : le8 (s.gpr .rax) = mn s₀.mem W P L

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : FPre s₀ W St P S L)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨S, 640⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨W, 400⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

end

theorem FPre.scrD {S : Addr} {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 640⟩ :=
  Offset.sub_base _ h

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem xor_comm (x y : List Byte) : Spec.Cmac.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## Copying the last bytes -/

/-- The copy loop's body. -/
abbrev copyBody : List Instr :=
  [.movzx8 .rax lastByte, .store8 padByte .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]

theorem copyStep_ok (s : State) {P C : Addr} {i L : Nat} (hd : s.gpr .rdx = P)
    (h15 : s.gpr .r15 + BitVec.ofNat 64 96 = C) (hi : s.gpr .r10 = BitVec.ofNat 64 i)
    (hc : s.gpr .rcx = BitVec.ofNat 64 L)
    (r : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (C + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 i) (s.mem (P + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.gpr .rdx + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 i := by
    rw [hd, hi, BitVec.mul_one]; simp
  have ea₂ : s.gpr .r15 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (96 : Int) = C + BitVec.ofNat 64 i := by
    rw [hi, BitVec.mul_one, ← h15, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]
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
  · simp [hi, hc]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · rfl
  · rfl

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Aes.bytesAt m p (i + 1) = Spec.Aes.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Aes.bytesAt, List.range_succ]

open VG.WriteBytes in
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 8) (hd : s.gpr .rdx = P)
    (h15 : s.gpr .r15 + BitVec.ofNat 64 96 = C) (hc : s.gpr .rcx = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩) :
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
  have td : t.gpr .rdx = P := by rw [g _ (by decide) (by decide), hd]
  have t15 : t.gpr .r15 + BitVec.ofNat 64 96 = C := by rw [g _ (by decide) (by decide), h15]
  have tc : t.gpr .rcx = BitVec.ofNat 64 L := by rw [g _ (by decide) (by decide), hc]
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t td t15 r10 tc
    (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ, writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i))
      (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = L
  · left
    refine ⟨by simp [X86_64.eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [X86_64.eval, hz, he], L - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The straight-line pieces -/

theorem pre1_ok (s : State) (hw : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) 8)
    {L : Nat} (hc : s.gpr .rcx = BitVec.ofNat 64 L) (hL : L ≤ 8) :
    ∃ s', runBlock isa (save .r8 ++ ([.mov .r15 (.reg .r8), .mov .r14 (.reg .rdi), .mov .rbp (.reg .rsi),
        .alu .cmp .rcx (.imm 8)] : List Instr)) s = some s' ∧
      s'.gpr .r15 = s.gpr .r8 ∧ s'.gpr .r14 = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧
      (∀ r, r ∉ [Reg.r14, .r15, .rbp] → s'.gpr r = s.gpr r) ∧ s'.zf = some (decide (L = 8)) ∧
      s'.mem = savedMem s (s.gpr .r8) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, g₁, m₁, rd₁, wr₁⟩ := save_ok s .r8 hw
  refine ⟨_, by
    rw [runBlock_append, h₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, g₁]
  · simp [gpr_setReg, g₁]
  · simp [gpr_setReg, g₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, g₁, hr.1, hr.2.1, hr.2.2]
  · rw [zf_arithFlags]
    simp only [gpr_setReg, reduceCtorEq, ite_false, g₁]
    rw [hc, show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  · simp [mem_setReg, mem_arithFlags, m₁, g₁]
  · simp [rd_setReg, rd_arithFlags, rd₁]
  · simp [wr_setReg, wr_arithFlags, wr₁]

/-- Two words XORed from `[pb + pd]` and `[qb + qd]` into `rax`. -/
theorem xor1_ok (s : State) (pb qb : Reg) (pd qd : Nat) {P Q : Addr}
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq' : qb ≠ .rax)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ pb pd)), .alu .xor .rax (.mem (at_ qb qd))] s = some s' ∧
      s'.gpr .rax = s.mem.readW P 64 ^^^ s.mem.readW Q 64 ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, hq', ite_true, ite_false, hp, hq, rp, rq]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, hr]

theorem zero_ok (s : State) {C : Addr} {L : Nat} (hc : s.gpr .r15 + BitVec.ofNat 64 96 = C)
    (hL : s.gpr .rcx = BitVec.ofNat 64 L) (hL' : L < 2 ^ 64) (wc : InRegions s.wr C 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.zf = some (decide (L = 0)) ∧
      s'.mem = s.mem.writeW C (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [zero, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, hc, wc]
    rfl, ?_⟩
  refine ⟨?_, rfl, ?_, rfl, rfl⟩
  · rw [zf_arithFlags]
    simp only [hL, BitVec.and_self]
    rw [ofNat_beq_zero hL']
  · intro r hr; simp [gpr_setReg, hr]

theorem pad_ok (s : State) {C K : Addr} {L : Nat}
    (hc : s.gpr .r15 + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofInt 64 (96 : Int) = C + BitVec.ofNat 64 L)
    (hc' : s.gpr .r15 + BitVec.ofNat 64 96 = C) (hk : s.gpr .rdi + BitVec.ofNat 64 392 = K)
    (wc : InRegions s.wr (C + BitVec.ofNat 64 L) 1) (rc : InRegions (s.rd ++ s.wr) C 8)
    (rk : InRegions (s.rd ++ s.wr) K 8) :
    ∃ s', runBlock isa padK2 s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte) ∧
      s'.gpr .rax = (s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte)).readW C 64 ^^^
        (s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte)).readW K 64 ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [padK2, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.load64, State.store8, State.ea, State.setReg32, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      hc, hc', hk, wc, rc, rk]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags]; rfl
  · simp [gpr_setReg]
  · simp [gpr_setReg, hr]

end VG.Proof.CmacTripleDes.X86_64
