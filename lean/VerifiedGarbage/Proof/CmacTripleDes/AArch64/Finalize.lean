import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# TDEA-CMAC on AArch64: `vg_cmac_triple_des_finalize`

Untrusted: everything here is checked by Lean. The steps that form the last
block `Mₙ` (§6.2 step 4) in `x5`, as a little-endian word (`BPost`):
`Mₙ* ⊕ K1` for a complete last block, else `Mₙ*` copied a byte at a time
onto the zeroed slot 6, `0x80` after it, XORed with `K2`. The function then
XORs in the chaining value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as
the state, the MAC (`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes VG.Proof.Cmac

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them) and the scratch buffer `S`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L : Nat) : Prop where
  x0 : s₀.gpr .x0 = W
  x1 : s₀.gpr .x1 = St
  x2 : s₀.gpr .x2 = P
  x3 : (s₀.gpr .x3).toNat = L
  x4 : s₀.gpr .x4 = S
  rd : s₀.rd = [⟨W, 400⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 8⟩, ⟨S, 640⟩]
  key_st : (⟨W, 400⟩ : Region).Disjoint ⟨St, 8⟩
  key_scr : (⟨W, 400⟩ : Region).Disjoint ⟨S, 640⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 8⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 640⟩
  st_scr : (⟨St, 8⟩ : Region).Disjoint ⟨S, 640⟩
  key_wrap : W.toNat + 400 ≤ 2 ^ 64
  st_wrap : St.toNat + 8 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 640 ≤ 2 ^ 64
  len : L ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeAArch64.pre s₀) :
    FPre s₀ (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x3).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- Slot 6, where a partial last block is formed. -/
abbrev slot6 (S : Addr) : Region := ⟨S + BitVec.ofNat 64 48, 8⟩

/-- What the branch on the length leaves: `Mₙ` in `x5`. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = W
  x15 : s.gpr .x15 = S
  x1 : s.gpr .x1 = St
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [slot6 S] s₀.mem s.mem
  blk : le8 (s.gpr .x5) = mn s₀.mem W P L

/-- What the first block leaves. -/
structure P1 (s₀ : State) (W St P S : Addr) (s : State) : Prop where
  x15 : s.gpr .x15 = S
  x14 : s.gpr .x14 = W
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = St
  x2 : s.gpr .x2 = P
  x3 : s.gpr .x3 = s₀.gpr .x3
  sp : s.sp = s₀.sp
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

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
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 8)
    (h7 : s.gpr .x7 = P) (h6 : s.gpr .x6 = C) (h8 : s.gpr .x8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩) :
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
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x8) (x := L - (i + 1)) (by omega) x8''
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

/-! ## The straight-line pieces -/

theorem pre1_ok (s : State) {L : Nat} (hc : s.gpr .x3 = BitVec.ofNat 64 L) (hL : L ≤ 8) :
    ∃ s', runBlock isa [mov .x14 .x0, mov .x15 .x4, .subImm .x .x9 .x3 8] s = some s' ∧
      s'.gpr .x14 = s.gpr .x0 ∧ s'.gpr .x15 = s.gpr .x4 ∧
      (∀ r, r ∉ [Reg.x9, .x14, .x15] → s'.gpr r = s.gpr r) ∧
      isa.eval (.zero .x .x9) s' = some (decide (L = 8)) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r hr => ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2]
  · show some (_ == 0) = _
    simp only [State.read, gpr_write_self, gpr_write_of_ne _ _ _ (show Reg.x3 ≠ .x15 by decide),
      gpr_write_of_ne _ _ _ (show Reg.x3 ≠ .x14 by decide), BitVec.setWidth_eq, hc]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]

/-- Two words XORed from `[pb + pd]` and `[qb + qd]` into `x5`. -/
theorem xor1_ok (s : State) (pb qb : Reg) (pd qd : Nat) {P Q : Addr}
    (hpd : pd % 8 = 0 ∧ pd < 32768) (hqd : qd % 8 = 0 ∧ qd < 32768)
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq' : qb ≠ .x5)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa [.ldr .x .x5 pb pd, .ldr .x .x6 qb qd, .logic .eor .x .x5 .x5 .x6] s = some s' ∧
      s'.gpr .x5 = s.mem.readW P 64 ^^^ s.mem.readW Q 64 ∧ (∀ r, r ≠ .x5 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr pb + BitVec.ofNat 64 pd) 64)
  have rq' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr qb + BitVec.ofNat 64 qd) 8 := by
    rw [gpr_write_of_ne _ _ _ hq', hq]; exact rq
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x hpd (by rw [hp]; exact rp), runStep_some, runBlock_cons, exec_ldr_x hqd rq',
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp (config := {decide := true}) only [s₁, State.read, gpr_write, mem_write, ite_true, ite_false,
      BitVec.setWidth_eq, hp, hq', hq]
  · simp [s₁, gpr_write, h₁, h₂]

theorem zero_ok (s : State) {C : Addr} (hc : s.gpr .x15 + BitVec.ofNat 64 48 = C) (wc : InRegions s.wr C 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.mem = s.mem.writeW C (0 : BitVec 64) ∧
      s'.gpr .x6 = C ∧ s'.gpr .x7 = s.gpr .x2 ∧ s'.gpr .x8 = s.gpr .x3 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [zero, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, wr_write,
      ite_true, ite_false, Option.bind_some, BitVec.setWidth_eq, hc, wc]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write, ← hc], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, BitVec.setWidth_eq]
  rfl

theorem pad_ok (s : State) {B C K : Addr} (hb : s.gpr .x6 + BitVec.ofNat 64 0 = B)
    (hc : s.gpr .x15 + BitVec.ofNat 64 48 = C) (hk : s.gpr .x0 + BitVec.ofNat 64 392 = K)
    (w : InRegions s.wr B 1) (rc : InRegions (s.rd ++ s.wr) C 8) (rk : InRegions (s.rd ++ s.wr) K 8) :
    ∃ s', runBlock isa padK2 s = some s' ∧
      s'.mem = s.mem.writeW B (0x80 : Byte) ∧
      s'.gpr .x5 = (s.mem.writeW B (0x80 : Byte)).readW C 64 ^^^ (s.mem.writeW B (0x80 : Byte)).readW K 64 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [padK2, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.store, State.load, Size.bits, Size.bytes, State.read, gpr_write, mem_write, rd_write, wr_write,
      ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, hb, hc, hk, w, rc, rk]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, Nat.reduceDiv, Nat.reduceMul]
    rfl
  · simp only [gpr_write, ite_true, BitVec.setWidth_eq, Mem.writeW, Mem.readW, Nat.reduceDiv,
      Nat.reduceMul]
    rfl

/-! ## The last block -/

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : FPre s₀ W St P S L)
include hp

theorem FPre.keyD {d n : Nat} (h : d + n ≤ 400) {r : Region} (hr : Region.Sub r ⟨S, 640⟩) :
    (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right hr

theorem full_wp (hL : L = 8) {s : State} (h : P1 s₀ W St P S s) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have kw := hp.key_wrap
  obtain ⟨s', run, ax, g, sp, m, rd, wr⟩ := xor1_ok s .x2 .x0 0 384 (P := P) (Q := W + BitVec.ofNat 64 384)
    (by decide) (by decide) (by rw [h.x2]; simp) (by rw [h.x0]) (by decide)
    (by rw [h.rd, h.wr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [h.rd, h.wr]; exact hp.inKey (d := 384) (n := 8) (by decide))
  refine WP.of_runBlock ⟨s', run, by rw [g _ (by decide) (by decide), h.x14],
    by rw [g _ (by decide) (by decide), h.x15], by rw [g _ (by decide) (by decide), h.x1], by rw [sp, h.sp],
    by rw [rd, h.rd], by rw [wr, h.wr], by rw [m, h.mem]; exact Frame.refl _ _, ?_⟩
  rw [ax, h.mem, le8_xor, le8_readW, le8_readW]
  simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
  exact xor_comm _ _

open VG.WriteBytes in
theorem partial_wp (hL : L < 8) {s : State} (h : P1 s₀ W St P S s) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have hcx : s.gpr .x3 = BitVec.ofNat 64 L := by
    rw [h.x3, ← hp.x3]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 48 = C := ⟨_, rfl⟩
  have hc : s.gpr .x15 + BitVec.ofNat 64 48 = C := by rw [h.x15, hC]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have sl : slot6 S = ⟨C, 8⟩ := by rw [← hC]
  -- Zero the slot.
  obtain ⟨s₁, run₁, mem₁, x6₁, x7₁, x8₁, g₁, sp₁, rd₁, wr₁⟩ := zero_ok s hc
    (by rw [h.wr, ← hC]; exact hp.inScr (d := 48) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  let m₁ := s₀.mem.writeW C (0 : BitVec 64)
  have zf : s₁.mem = m₁ := by rw [mem₁, h.mem]
  have fz : Frame [⟨C, 8⟩] s₀.mem m₁ :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have lastZ : Spec.Aes.bytesAt m₁ P L = Spec.Aes.bytesAt s₀.mem P L :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L) ∧
      s₂.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s₂.gpr r = s.gpr r) ∧
      s₂.sp = s₀.sp ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := eval_zero (s := s₁) (r := .x3) (x := L) (by omega) (by rw [g₁ _ (by decide) (by decide)
      (by decide) (by decide), hcx])
    by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [x6₁]; simp,
        fun r h₁ h₂ h₃ h₄ _ => g₁ r h₁ h₂ h₃ h₄, by rw [sp₁, h.sp], by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_ok s₁ (by omega) hL (by rw [x7₁, h.x2]) x6₁ (by rw [x8₁, hcx])
        (fun i hi => by rw [rd₁, wr₁, h.rd, h.wr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, h.wr, ← hC, Offset.add_add]; exact hp.inScr (d := 48 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], x6₂, fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₂ r h₂ h₃ h₄ h₅, g₁ r h₁ h₂ h₃ h₄],
        by rw [sp₂, sp₁, h.sp], by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr]⟩
  · obtain ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩ := h₂
    have x15₂ : s₂.gpr .x15 = S := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x15]
    have x0₂ : s₂.gpr .x0 = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x0]
    obtain ⟨s₃, run₃, m₃, ax₃, g₃, sp₃, rd₃, wr₃⟩ := pad_ok s₂ (B := C + BitVec.ofNat 64 L) (C := C)
      (K := W + BitVec.ofNat 64 392) (by rw [x6₂, BitVec.add_zero]) (by rw [x15₂, hC]) (by rw [x0₂])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 48 + L) (n := 1) (by omega))
      (by rw [rd₂, wr₂, ← hC]; exact wr_in (hp.inScr (d := 48) (n := 8) (by decide)))
      (by rw [rd₂, wr₂]; exact hp.inKey (d := 392) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .x5) (h₂ : r ≠ .x6) (h₃ : r ≠ .x7) (h₄ : r ≠ .x8) (h₅ : r ≠ .x9) :
        s₃.gpr r = s.gpr r := by rw [g₃ r h₁ h₂ h₅, g₂ r h₁ h₂ h₃ h₄ h₅]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fB : Frame [⟨C, 8⟩] m₁ (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 8) (by omega) (by decide))
    have fW : Frame [⟨C, 8⟩] (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have f₃ : Frame [⟨C, 8⟩] s₀.mem s₃.mem := (fz.trans fB).trans fW
    have kD : (⟨W + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint ⟨C, 8⟩ := by
      rw [← hC]; exact hp.keyD (by decide) (FPre.scrD (by decide))
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 392) 8 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 :=
      bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide)
    have pad : Spec.Aes.bytesAt s₃.mem C 8 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (8 - L - 1) := by
      have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
        rw [← le8_readW, Mem.readW_writeW_self64]; decide
      have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem P L) (by rw [hlen]; exact hL) hz
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x14],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x15],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x1],
      by rw [sp₃, sp₂], by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [sl]; exact f₃, ?_⟩
    rw [ax₃, ← m₃, le8_xor, le8_readW, le8_readW, pad, k2]
    simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 8 by omega, ite_false]
    exact xor_comm _ _

end

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L : Nat} (hp : FPre s₀ W St P S L) :
    WP isa finPre s₀ (BPost s₀ W St P S L) := by
  have hcx : s₀.gpr .x3 = BitVec.ofNat 64 L := by rw [← hp.x3]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, x14₁, x15₁, g₁, ev₁, sp₁, m₁, rd₁, wr₁⟩ := pre1_ok s₀ hcx hp.len
  have h1 : P1 s₀ W St P S s₁ := ⟨by rw [x15₁, hp.x4], by rw [x14₁, hp.x0],
    by rw [g₁ _ (by decide), hp.x0], by rw [g₁ _ (by decide), hp.x1], by rw [g₁ _ (by decide), hp.x2],
    g₁ _ (by decide), sp₁, m₁, rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL : L = 8
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => full_wp hp hL h1) (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h1)

/-! ## The whole function -/

theorem xorSt_ok (s : State) {St : Addr} (hb : s.gpr .x1 = St) (r : InRegions (s.rd ++ s.wr) St 8) :
    ∃ s', runBlock isa [.ldr .x .x6 .x1 0, .logic .eor .x .x5 .x5 .x6, .rev .x5 .x5] s = some s' ∧
      s'.gpr .x5 = byteRev64 (s.gpr .x5 ^^^ s.mem.readW St 64) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x (by decide) (by rw [add_ofNat_zero, hb]; exact r), runStep_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp (config := {decide := true}) only [State.read, gpr_write, ite_true, ite_false,
      BitVec.setWidth_eq, rev64_eq, add_ofNat_zero, hb]
  · simp [gpr_write, h₁, h₂]

theorem storeSt_ok (s : State) {St : Addr} (hb : s.gpr .x1 = St) (w : InRegions s.wr St 8) :
    ∃ s', runBlock isa [.rev .x5 .x5, .str .x .x5 .x1 0] s = some s' ∧
      s'.mem = s.mem.writeW St (byteRev64 (s.gpr .x5)) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x .x5 (rev64 (s.read .x .x5))
  have w' : InRegions s₁.wr (s₁.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero, gpr_write_of_ne _ _ _ (by decide), hb]; exact w
  refine ⟨_, by
    rw [runBlock_cons, exec_rev, runStep_some, runBlock_cons, exec_str_x (by decide) w', runStep_some,
      runBlock_nil], ?_⟩
  refine ⟨?_, rfl, rfl, rfl⟩
  simp (config := {decide := true}) only [s₁, mem_write, State.read, gpr_write, ite_true, ite_false,
    BitVec.setWidth_eq, rev64_eq, hb, add_ofNat_zero]

theorem finalize_wp {s₀ : State} (h0 : finalizeAArch64.pre s₀) :
    WP isa finalize s₀ fun s' => finalizeAArch64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .x0 = W at hp
  generalize hSt : s₀.gpr .x1 = St at hp
  generalize hP : s₀.gpr .x2 = P at hp
  generalize hS : s₀.gpr .x4 = S at hp
  generalize hL : (s₀.gpr .x3).toNat = L at hp
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have tw := hp.st_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 640⟩] := by rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₂, run₂, ax₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := xorSt_ok s₁ h₁.x1
    (by rw [rdwr₁]; exact in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have bp : BlockPre s₂ :=
    { sched := ⟨⟨W, 400⟩, by rw [rd₂, wr₂, h₁.rd, hp.rd]; simp, by rw [g₂ _ (by decide) (by decide), h₁.x14],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨S, 640⟩, by rw [wr₂, h₁.wr, hp.wr]; simp, by rw [g₂ _ (by decide) (by decide), h₁.x15],
        by show 48 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [g₂ _ (by decide) (by decide), g₂ _ (by decide) (by decide), h₁.x14, h₁.x15]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right
          (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₃ ⟨same₃, x14₃, ax₃⟩ => ?_)
  have x1₃ : s₃.gpr .x1 = St := by rw [same₃.keep .x1 (by simp [outer]), g₂ _ (by decide) (by decide), h₁.x1]
  obtain ⟨s₄, run₄, m₄, sp₄, rd₄, wr₄⟩ := storeSt_ok s₃ x1₃
    (by rw [same₃.wr, wr₂, h₁.wr, hp.wr]; exact in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  intro hk msg hml hne hst
  rw [hW, hSt, hP, hL] at *
  have keyD (r : Region) (hr : Region.Sub r ⟨S, 640⟩) : (⟨W, 384⟩ : Region).Disjoint r :=
    (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right hr
  have hS' : sch s₂ = Spec.TripleDes.scheduleAt s₀.mem W := by
    rw [sch, g₂ _ (by decide) (by decide), h₁.x14, m₂]
    exact scheduleAt_frame h₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact keyD _ (FPre.scrD (by decide))
  have hst₁ : le8 (s₁.mem.readW St 64) = Spec.Aes.bytesAt s₀.mem St 8 := by
    rw [le8_readW]
    exact bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (FPre.scrD (by decide))) (by decide)
  have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem W)
  have hk' : Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (ciphAt s₀.mem W) 8).1 ++ (Spec.Cmac.subkeys (ciphAt s₀.mem W) 8).2 := by
    rw [show W + BitVec.ofNat 64 392 = W + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add W 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s₄.mem St 8 = _
  rw [m₄, ← le8_readW, Mem.readW_writeW_self64, ax₃, ax₂, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, xor_comm]

/-- The stack pointer is unchanged. -/
theorem finalize_sp {s₀ s : State} {t : List Leak} (h : Exec isa finalize s₀ t s) : s.sp = s₀.sp := Exec.sp h

end VG.Proof.CmacTripleDes.AArch64
