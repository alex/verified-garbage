import VerifiedGarbage.Proof.Sha512.Arm.Stream.Update
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common

/-!
# Streaming SHA-512 on ARMv7: `finalize`

Untrusted: everything here is checked by Lean. The structure of the SHA-256
proof (`VG.Proof.MdStream.Arm.Finalize`), with `state` in `r0`,
`scratch` in `r3`, `out` in `r6`, the buffered bytes in `r4`, whether the
block is not the last in `r5`, and `count` saved in the scratch space (with
our caller's registers).
-/

namespace VG.Proof.Sha512.Arm.Stream.Finalize

open VG VG.Arm VG.Impl.Sha512.Arm.Stream
open VG.Impl.Sha512.Arm (lo hi)
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_and
  wp_orr wp_subs wp_cmp wp_rev wp_ldr wp_str wp_strb wp_ldrSp saveMem saveList_ok readW_writeW_save
  sub_offset frame_bytes bytesAt_getD eval_eq eval_ne ofNat_beq_zero sub_ofNat sub_beq)
open VG.Proof.Sha512.Arm (temps)
open VG.Proof.Sha512.Arm.Stream
open VG.Proof.Sha512.Arm.Stream.Update (addr_toNat shr7 cmp0)
open VG.Proof.Sha512.Stream
open VG.Spec.Sha512 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)
open VG.Proof.Sha512 (countArm)

/-! ## Words -/

/-- The big-endian bytes of a 64-bit word are those of its high half, then
those of its low half. -/
theorem wordBytes_split (x : BitVec 64) :
    wordBytes x = Spec.Sha256.wordBytes (hi x) ++ Spec.Sha256.wordBytes (lo x) := by
  simp only [Spec.Sha512.wordBytes, Spec.Sha256.wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq, and_true, hi, lo]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i hi
  all_goals simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  all_goals rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega

theorem writeW_rev (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev w) = writeBytes m a (Spec.Sha256.wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← VG.Proof.Sha256.X86_64.Stream.bswap32_bytes']; rfl

theorem lo_shr61 (x : BitVec 64) : lo (x >>> 61) = hi x >>> 29 := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hi_toNat]
  have := x.isLt
  omega

theorem hi_shr61 (x : BitVec 64) : hi (x >>> 61) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [hi_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
  have := x.isLt
  omega

theorem lo_shl3 (x : BitVec 64) : lo (x <<< 3) = lo x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat]
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, lo_toNat]
  omega

theorem hi_shl3 (x : BitVec 64) : hi (x <<< 3) = (hi x <<< 3) ||| (lo x >>> 29) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [hi, lo, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, hi', decide_true, Bool.true_and]
  by_cases h : i < 3
  · rw [decide_eq_true (by omega : 32 + i < 64), decide_eq_false (by omega : ¬ 32 + i < 3),
      decide_eq_true (by omega : 29 + i < 32), show 32 + i - 3 = 29 + i by omega]
    rw [decide_eq_true h, Nat.zero_add]
    simp only [Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or]
  · rw [decide_eq_true (by omega : 32 + i < 64), decide_eq_false (by omega : ¬ 32 + i < 3),
      decide_eq_true (by omega : i - 3 < 32), decide_eq_false (by omega : ¬ 29 + i < 32),
      show 32 + i - 3 = 32 + (i - 3) by omega]
    rw [decide_eq_false h]
    simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false]

/-! ## The precondition -/

/-- What the prologue stores in the scratch space: our caller's registers and
`count`. -/
def stored : List (Reg × Nat) := saved ++ [(.r2, 260), (.r3, 264)]

theorem stored_bound : ∀ p ∈ stored, 224 ≤ p.2 ∧ p.2 + 4 ≤ 268 := by decide

theorem saved_stored {p : Reg × Nat} (hp : p ∈ saved) : p ∈ stored := List.mem_append_left _ hp

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev cnt : Nat := (countArm s₀).toNat
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev stA : Addr := State.addr (st s₀)
abbrev outA : Addr := State.addr (out s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev stR : Region := ⟨stA s₀, 192⟩
abbrev outR : Region := ⟨outA s₀, 64⟩
abbrev scR : Region := ⟨scA s₀, 272⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩

/-- The messages the initial state represents, from the initial hash value
`iv`, of fewer than 2⁶⁴ bytes. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha512.Repr iv s₀.mem (stA s₀) m ∧ m.length < 2 ^ 64 ∧ countArm s₀ = BitVec.ofNat 64 m.length

/-- The caller's registers and `count` are stored in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ stored, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- The digest, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 64) n ++ List.replicate (128 - n) 0).getD t 0))
    (parseBlock fun t => (List.replicate 112 0 ++ lenBytes m).getD t 0)

/-- The digest, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (stateAt mem (stA s₀))
    (parseBlock fun t => (bytesAt mem (stA s₀ + 64) n ++ List.replicate (112 - n) 0 ++ lenBytes m).getD t 0)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, outR s₀, scR s₀]
  st_out : (stR s₀).Disjoint (outR s₀)
  st_scr : (stR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_out : (argR s₀).Disjoint (outR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 192 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 64 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 272 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Sha512.finalizeArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 128 = (s₀.gpr .r2).toNat % 128 := by
  simp only [cnt, countArm]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : HashValue} {m : List Byte} (h : R₀ s₀ iv m) :
    cnt s₀ % 128 = m.length % 128 := by
  rw [cnt, h.2.2, BitVec.toNat_ofNat]
  omega

theorem st_add (s₀ : State) (n : Nat) :
    stA s₀ + 64 + BitVec.ofNat 64 n = stA s₀ + BitVec.ofNat 64 (64 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  r6 : s.gpr .r6 = out s₀
  sp : s.sp = s₀.sp
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 112 + 16 * k
  r4 : s.gpr .r4 = BitVec.ofNat 32 n
  r5 : s.gpr .r5 = BitVec.ofNat 32 k
  hash : ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m = (stateAt s.mem (stA s₀)).toList.flatMap wordBytes

def keepRegs : List Reg := [.r0, .r3, .r6]

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ keepRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r0 := by rw [hg _ (by simp [keepRegs])]; exact h.r0
  r3 := by rw [hg _ (by simp [keepRegs])]; exact h.r3
  r6 := by rw [hg _ (by simp [keepRegs])]; exact h.r6
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.of_upd {s₀ : State} {s s' : State} (h : Common s₀ s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ keepRegs) : Common s₀ s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Common.of_flags {s₀ : State} {s s' : State} (h : Common s₀ s) (u : Fupd s s') : Common s₀ s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- Where the caller's registers and `count` are stored. -/
theorem stored_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ stored) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR s₀) :=
  sub_offset (by have := (stored_bound p hp).2; omega) (by have := (stored_bound p hp).2; omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 128) :
    Frame [stR s₀] s.mem (writeBytes s.mem (stA s₀ + 64 + BitVec.ofNat 64 n) xs) ∧
      Frame [stR s₀, scR s₀] s₀.mem (writeBytes s.mem (stA s₀ + 64 + BitVec.ofNat 64 n) xs) ∧
      Saved s₀ (writeBytes s.mem (stA s₀ + 64 + BitVec.ofNat 64 n) xs) := by
  have hf : Frame [stR s₀] s.mem (writeBytes s.mem (stA s₀ + 64 + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [st_add]
    exact contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (stored_sub hp')

/-- Byte `k` of the buffer, addressed as `[r0 + k, #64]`. -/
theorem buf_addr {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) :
    State.addr (st s₀ + BitVec.ofNat 32 k + BitVec.ofNat 32 64) = stA s₀ + 64 + BitVec.ofNat 64 k := by
  have := hp.st_fit
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), Nat.add_comm, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  rfl

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ .r5 :: keepRegs, s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  r12 : s.gpr .r12 = 0
  r4 : s.gpr .r4 = BitVec.ofNat 32 (n + j)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (stA s₀ + 64 + BitVec.ofNat 64 n) (List.replicate j 0)

/-- The zeroing loop's body. -/
def zeroBody : List Instr :=
  [.dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 64, .dp .add .r4 .r4 (.imm 1), .subs .r9 .r9 (.imm 1)]

theorem zero_step {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ 128) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block zeroBody) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.z = (BitVec.ofNat 32 (lim - n - (j + 1)) == 0) := by
  have hr0 : s.gpr .r0 = st s₀ := by rw [h.keep _ (by simp [keepRegs]), hC.r0]
  have hout : InRegions s.wr (stA s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [show stA s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = stA s₀ + BitVec.ofNat 64 (64 + n + j) by
      simp only [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  unfold zeroBody
  refine wp_add (op2_reg _ _) fun s₁ u₁ =>
    wp_strb (a := stA s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega) ?_
      (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr0, h.r4, buf_addr hp (by omega)]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ =>
    WP.block_nil ⟨⟨by omega, fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd],
    by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr], by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .r9 ∧ r ≠ .r4 ∧ r ≠ .r1 := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r12]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r9,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.r12, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [z₄, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r9,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 128) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s)
    (hz : s.z = decide (lim - n = 0)) :
    WP isa (.ite .eq (.block []) (.loop (.block zeroBody) .ne)) s (Zero s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) (by show VG.Arm.eval .eq s = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    have hz'' : isa.eval .ne s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.Arm.eval .ne s' = _
      rw [eval_ne, hz', ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz'', decide_eq_false fun h => h hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz'', decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The call of the compression function on the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r, r ∉ temps → r ≠ .lr → s'.gpr r = s.gpr r) →
      stateAt s'.mem (stA s₀) = compress (stateAt s.mem (stA s₀)) (blockAt s.mem (stA s₀ + 64)) → Q s') :
    WP isa compressAt s Q := by
  have hsc := hp.scr_fit
  have e64 : Region.Sub ⟨scA s₀, 224⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine compressBuf_ok hC.r0 hC.r3 hp.st_fit hp.scr_fit hp.st_scr (by simp [hC.wr, hp.wr])
    (by simp [hC.wr, hp.wr]) fun s' hrd hwr hg hsp hf hst => hQ s' ⟨hrd.trans hC.rd, hwr.trans hC.wr,
      by rw [hg _ (by decide) (by decide), hC.r0], by rw [hg _ (by decide) (by decide), hC.r3],
      by rw [hg _ (by decide) (by decide), hC.r6], hsp.trans hC.sp, hC.frame.trans (hf.sub fun r hr => ?_),
      fun p hp' => ?_⟩ hg hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, e64⟩
  · rw [← hC.saved p hp']
    refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hp.st_scr.symm.sub_left (stored_sub hp')
    · have := stored_bound p hp'
      intro a h₁ h₂; simp only [Region.Contains, scA] at h₁ h₂; bv_omega

/-! ## The message length -/

/-- The bytes `lenW` writes, from `count` in `r2:r3`. -/
def lenL (s₀ : State) : List Byte :=
  Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (s₀.gpr .r3 >>> 29) ++
    Spec.Sha256.wordBytes ((s₀.gpr .r3 <<< 3) ||| (s₀.gpr .r2 >>> 29)) ++ Spec.Sha256.wordBytes (s₀.gpr .r2 <<< 3)

theorem lenL_eq {s₀ : State} {iv : HashValue} {m : List Byte} (hm : R₀ s₀ iv m) : lenL s₀ = lenBytes m := by
  have hc := hm.2.2
  have h8 : BitVec.ofNat 64 (8 * m.length) = countArm s₀ <<< 3 := by
    rw [hc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  rw [lenBytes_split m hm.2.1, ← hc, h8, wordBytes_split, wordBytes_split, hi_shr61, lo_shr61, hi_shl3,
    lo_shl3]
  simp only [countArm, hi_append, lo_append, lenL, List.append_assoc]

theorem lenL_length (s₀ : State) : (lenL s₀).length = 16 := rfl

/-- Writing the message length. -/
theorem len_ok {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = writeBytes s.mem (stA s₀ + 64 + BitVec.ofNat 64 112) (lenL s₀) → Q s') :
    WP isa (.block lenW) s Q := by
  have hst := hp.st_fit; have hsc := hp.scr_fit
  have hin : ∀ o, o + 4 ≤ 272 → InRegions (s.rd ++ s.wr) (scA s₀ + BitVec.ofNat 64 o) 4 := fun o ho =>
    ⟨scR s₀, by simp [hC.wr, hC.rd, hp.wr], contains_offset (by omega) (by omega)⟩
  have hout : ∀ o, o + 4 ≤ 192 → InRegions s.wr (stA s₀ + BitVec.ofNat 64 o) 4 := fun o ho =>
    ⟨stR s₀, by simp [hC.wr, hp.wr], contains_offset (by omega) (by omega)⟩
  have h2 := hC.saved (.r2, 260) (by decide)
  have h3 := hC.saved (.r3, 264) (by decide)
  unfold lenW
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 260) (by decide) (by rw [hC.r3, addr_add (by omega)])
    (hin 260 (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 264) (by decide)
    (by rw [u₁.other _ (by decide), hC.r3, addr_add (by omega)])
    (by rw [u₁.rd, u₁.wr]; exact hin 264 (by omega)) fun s₂ u₂ => ?_
  have e0 : s₂.gpr .r0 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hC.r0]
  have e9 : s₂.gpr .r9 = s₀.gpr .r2 := by rw [u₂.other _ (by decide), u₁.gpr, h2]
  have e10 : s₂.gpr .r10 = s₀.gpr .r3 := by rw [u₂.gpr, u₁.mem, h3]
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ =>
    wp_str (a := stA s₀ + BitVec.ofNat 64 176) (by decide)
      (by rw [u₃.other _ (by decide), e0, addr_add (by omega)])
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hout 176 (by omega)) fun s₄ g₄ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_rev fun s₆ u₆ =>
    wp_str (a := stA s₀ + BitVec.ofNat 64 180) (by decide)
      (by rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide), e0,
        addr_add (by omega)])
      (by rw [u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hout 180 (by omega)) fun s₇ g₇ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₈ u₈ => wp_orr (op2_lsr (by decide)) fun s₉ u₉ =>
    wp_rev fun s₁₀ u₁₀ => wp_str (a := stA s₀ + BitVec.ofNat 64 184) (by decide)
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), g₇.gpr,
        u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide), e0, addr_add (by omega)])
      (by rw [u₁₀.wr, u₉.wr, u₈.wr, g₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hout 184 (by omega))
      fun s₁₁ g₁₁ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₂ u₁₂ => wp_rev fun s₁₃ u₁₃ =>
    wp_str (a := stA s₀ + BitVec.ofNat 64 188) (by decide)
      (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), g₁₁.gpr, u₁₀.other _ (by decide),
        u₉.other _ (by decide), u₈.other _ (by decide), g₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
        g₄.gpr, u₃.other _ (by decide), e0, addr_add (by omega)])
      (by rw [u₁₃.wr, u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, g₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]
          exact hout 188 (by omega))
      fun s₁₄ g₁₄ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s₁₄.gpr r = s.gpr r := fun r a b c => by
    rw [g₁₄.gpr, u₁₃.other r c, u₁₂.other r c, g₁₁.gpr, u₁₀.other r c, u₉.other r c, u₈.other r c, g₇.gpr,
      u₆.other r c, u₅.other r c, g₄.gpr, u₃.other r c, u₂.other r b, u₁.other r a]
  -- The values stored.
  have v1 : s₆.gpr .r11 = rev (s₀.gpr .r3 >>> 29) := by
    rw [u₆.gpr, u₅.gpr, g₄.gpr, u₃.other _ (by decide), e10]
  have v2 : s₁₀.gpr .r11 = rev ((s₀.gpr .r3 <<< 3) ||| (s₀.gpr .r2 >>> 29)) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₈.other .r9 (by decide), g₇.gpr, u₆.other .r10 (by decide),
      u₆.other .r9 (by decide), u₅.other .r10 (by decide), u₅.other .r9 (by decide), g₄.gpr,
      u₃.other .r10 (by decide), u₃.other .r9 (by decide), e10, e9]
  have v3 : s₁₃.gpr .r11 = rev (s₀.gpr .r2 <<< 3) := by
    rw [u₁₃.gpr, u₁₂.gpr, g₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      g₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide), e9]
  have v0 : s₃.gpr .r11 = rev 0 := by rw [u₃.gpr]; decide
  have hw : s₁₄.mem = writeBytes s.mem (stA s₀ + 64 + BitVec.ofNat 64 112) (lenL s₀) := by
    have a1 : stA s₀ + BitVec.ofNat 64 180 = stA s₀ + BitVec.ofNat 64 176 + BitVec.ofNat 64 4 := by
      rw [BitVec.add_assoc]; rfl
    have a2 : stA s₀ + BitVec.ofNat 64 184 = stA s₀ + BitVec.ofNat 64 176 + BitVec.ofNat 64 8 := by
      rw [BitVec.add_assoc]; rfl
    have a3 : stA s₀ + BitVec.ofNat 64 188 = stA s₀ + BitVec.ofNat 64 176 + BitVec.ofNat 64 12 := by
      rw [BitVec.add_assoc]; rfl
    have a0 : stA s₀ + 64 + BitVec.ofNat 64 112 = stA s₀ + BitVec.ofNat 64 176 := by
      rw [BitVec.add_assoc]; rfl
    rw [g₁₄.mem, u₁₃.mem, u₁₂.mem, g₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, g₇.mem, u₆.mem, u₅.mem, g₄.mem, u₃.mem,
      u₂.mem, u₁.mem, v3, v2, v1, v0, writeW_rev, writeW_rev, writeW_rev, writeW_rev, a0, a1, a2, a3,
      show (4 : Nat) = (Spec.Sha256.wordBytes 0).length from rfl,
      writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]),
      show (8 : Nat) = (Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (s₀.gpr .r3 >>> 29)).length from rfl,
      writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]),
      show (12 : Nat) = (Spec.Sha256.wordBytes 0 ++ Spec.Sha256.wordBytes (s₀.gpr .r3 >>> 29) ++
        Spec.Sha256.wordBytes ((s₀.gpr .r3 <<< 3) ||| (s₀.gpr .r2 >>> 29))).length from rfl,
      writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes])]
    rfl
  obtain ⟨-, hfr, hsv⟩ := hC.writeBuf hp (n := 112) (xs := lenL s₀) (by rw [lenL_length])
  refine hQ s₁₄ ⟨?_, ?_, by rw [keep _ (by decide) (by decide) (by decide), hC.r0],
    by rw [keep _ (by decide) (by decide) (by decide), hC.r3],
    by rw [keep _ (by decide) (by decide) (by decide), hC.r6], ?_, by rw [hw]; exact hfr,
    by rw [hw]; exact hsv⟩ keep hw
  · rw [g₁₄.rd, u₁₃.rd, u₁₂.rd, g₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, g₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd,
      hC.rd]
  · rw [g₁₄.wr, u₁₃.wr, u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, g₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr,
      hC.wr]
  · rw [g₁₄.sp, u₁₃.sp, u₁₂.sp, g₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, g₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp,
      hC.sp]

/-! ## One block -/

/-- The end of the loop's body: the length, if this is the last block, and
the compression. -/
def tailP : Prog isa :=
  .seq (.block [.cmp .r5 (.imm 0)])
  (.seq (.ite .eq (.block lenW) (.block []))
  (.seq compressAt (.block [.mov .r4 (.imm 0), .subs .r5 .r5 (.imm 1)])))

theorem body_eq : finalizeBody =
    .seq (.block [.mov .r9 (.imm 128), .cmp .r5 (.imm 0)])
    (.seq (.ite .eq (.block [.mov .r9 (.imm 112)]) (.block []))
    (.seq (.block [.mov .r12 (.imm 0), .subs .r9 .r9 (.reg .r4)])
    (.seq (.ite .eq (.block []) (.loop (.block zeroBody) .ne)) tailP))) := rfl

/-- Zeroing the rest of the block, up to the length or its end. -/
theorem pad_ok {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → s'.gpr .r5 = BitVec.ofNat 32 k →
      stateAt s'.mem (stA s₀) = stateAt s.mem (stA s₀) →
      bytesAt s'.mem (stA s₀ + 64) (112 + 16 * k) =
        bytesAt s.mem (stA s₀ + 64) n ++ List.replicate (112 + 16 * k - n) 0 →
      WP isa tailP s' Q) :
    WP isa finalizeBody s Q := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit
  have hC := h.toCommon
  rw [body_eq]
  -- `r9 := 128` or `112`: the end of the zeros.
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have hz₂ : s₂.z = decide (k = 0) := by rw [z₂, u₁.other _ (by decide), h.r5, cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .r9 = BitVec.ofNat 32 (112 + 16 * k) ∧
      (∀ r, r ≠ .r9 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h9₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show VG.Arm.eval .eq s₂ = _; rw [eval_eq, hz₂])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr]; rfl, fun r hr => ?_,
        by rw [u₃.mem, f₂.mem, u₁.mem], by rw [u₃.rd, f₂.rd, u₁.rd], by rw [u₃.wr, f₂.wr, u₁.wr],
        by rw [u₃.sp, f₂.sp, u₁.sp]⟩
      rw [u₃.other r hr, f₂.gpr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [f₂.gpr, u₁.gpr, show k = 1 by omega]; rfl, fun r hr => ?_,
        by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.sp, u₁.sp]⟩
      rw [f₂.gpr, u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_subs (op2_reg _ _) fun s₅ u₅ z₅ =>
    WP.block_nil ?_)
  have h9₅ : s₅.gpr .r9 = BitVec.ofNat 32 (112 + 16 * k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), h9₃, u₄.other _ (by decide), g₃ _ (by decide), h.r4,
      sub_ofNat (by omega)]
  have hZ : Zero s₀ s n (112 + 16 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, by rw [h9₅, Nat.sub_zero], ?_⟩
    · have : r ≠ .r9 ∧ r ≠ .r12 := by
        simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.r4, Nat.add_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  have hz₅ : s₅.z = decide (112 + 16 * k - n - 0 = 0) := by
    rw [z₅, ← u₅.gpr, h9₅, ofNat_beq_zero (by omega), Nat.sub_zero]
  refine WP.seq (WP.mono (zero_ok hp hC (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  obtain ⟨-, hfr₆, hsv₆⟩ := hC.writeBuf hp (n := n) (xs := List.replicate (112 + 16 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  refine hQ s₆ ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r0],
      by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r3], by rw [hZ₆.keep _ (by simp [keepRegs]), hC.r6],
      hZ₆.sp.trans hC.sp,
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
    (by rw [hZ₆.keep _ (by simp [keepRegs]), h.r5]) ?_ ?_
  · rw [hZ₆.mem]
    apply stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  · rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega

/-- The length, if this is the last block, and the compression. -/
theorem tail_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k ≤ 1) {s : State} (hC : Common s₀ s)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 k) {H : HashValue} {B : List Byte}
    (hst : stateAt s.mem (stA s₀) = H) (hby : bytesAt s.mem (stA s₀ + 64) (112 + 16 * k) = B) :
    WP isa tailP s fun s' => Common s₀ s' ∧ VG.Arm.eval .eq s' = some (decide (k = 1)) ∧
      s'.gpr .r4 = 0 ∧ s'.gpr .r5 = BitVec.ofNat 32 k - 1 ∧
      ∀ iv m, R₀ s₀ iv m → stateAt s'.mem (stA s₀) =
        compress H (parseBlock fun t => (B ++ if k = 1 then [] else lenBytes m).getD t 0) := by
  have hst' := hp.st_fit
  unfold tailP
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hC₁ := hC.of_flags f₁
  have hz₁ : s₁.z = decide (k = 0) := by rw [z₁, h5, cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => Common s₀ s₂ ∧ s₂.gpr .r5 = BitVec.ofNat 32 k ∧
      stateAt s₂.mem (stA s₀) = H ∧
      ∀ iv m, R₀ s₀ iv m → bytesAt s₂.mem (stA s₀ + 64) 128 = B ++ if k = 1 then [] else lenBytes m) ?_
    fun s₂ ⟨hC₂, h5₂, hst₂, hby₂⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz₁])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine len_ok hp hC₁ fun s₂ hC₂ keep hw =>
        ⟨hC₂, by rw [keep _ (by decide) (by decide) (by decide), f₁.gpr, h5], ?_, fun iv m hm => ?_⟩
      · rw [hw, ← hst, ← f₁.mem]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by rw [lenL_length]; omega)
      · have e := bytesAt_writeBytes s₁.mem (stA s₀ + 64) 112 (lenL s₀) (by rw [lenL_length]; omega)
        rw [lenL_length] at e
        rw [show 112 + 16 * 0 = 112 from rfl] at hby
        rw [hw, e, f₁.mem, hby, lenL_eq hm]
        simp
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      rw [show 112 + 16 * 1 = 128 from rfl] at hby
      exact WP.block_nil ⟨hC₁, by rw [f₁.gpr, h5], by rw [f₁.mem, hst], fun iv m _ => by rw [f₁.mem, hby]; simp⟩
  -- Compress the block.
  refine WP.seq (compress_buf hp hC₂ fun s₃ hC₃ g₃ hst₃ => ?_)
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_subs (op2_imm (by decide)) fun s₅ u₅ z₅ =>
    WP.block_nil ?_
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 k := by rw [g₃ _ (by decide) (by decide), h5₂]
  refine ⟨(hC₃.of_upd u₄ (by decide)).of_upd u₅ (by decide), ?_, ?_, ?_, fun iv m hm => ?_⟩
  · rw [eval_eq, z₅, u₄.other _ (by decide), h5₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by omega)]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), h5₃]
  · rw [u₅.mem, u₄.mem, hst₃, hst₂]
    exact congrArg (compress H) (parseBlock_congr fun t ht => bytesAt_getD (hby₂ iv m hm) ht)

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (VG.Arm.eval .eq s = some false ∧ Done s₀ s) ∨ (VG.Arm.eval .eq s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

theorem body_ok {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s (Step s₀ k) := by
  have hk := h.k_le; have hn := h.n_le
  refine pad_ok hp h fun s₁ hC₁ h5₁ hst₁ hby₁ =>
    WP.mono (tail_ok hp hk hC₁ h5₁ hst₁ hby₁) fun s' ⟨hC', he, h4, h5, hst'⟩ => ?_
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by rw [he]; rfl, rfl, ⟨hC', by omega, by omega, by rw [h4]; rfl, by rw [h5]; rfl,
      fun iv m hm => ?_⟩⟩
    rw [h.hash iv m hm]
    simp only [ite_true, show ¬ ((0 : Nat) = 1) by decide, ite_false, Fin1, Fin0, hst' iv m hm,
      List.append_nil, show 112 + 16 * 1 - n = 128 - n by omega, Nat.sub_zero]
    rfl
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by rw [he]; rfl, hC', fun iv m hm => ?_⟩
    rw [h.hash iv m hm, hst' iv m hm]
    simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false, Fin0, Nat.mul_zero, Nat.add_zero]

/-! ## Prologue -/

set_option simprocs false in
theorem saveMem_stored (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ stored, (saveMem m B g stored).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [stored, saved, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [stored, saved, List.cons_append, List.nil_append, saveMem,
    Mem.readW_writeW_self32, readW_writeW_save]

/-- The prologue after saving. -/
def prologue : List Instr :=
  [.mov .r3 (.reg .r12), .ldrSp .r6 0, .dp .and .r4 .r2 (.imm 127),
   .mov .r12 (.imm 0x80), .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 64, .dp .add .r4 .r4 (.imm 1),
   .dp .add .r5 .r4 (.imm 15), .mov .r5 (.shifted .r5 .lsr 7)]

theorem finalize_eq : finalize =
    .seq (.block (([.ldrSp .r12 4] : List Instr) ++ (stored.map (fun p => Instr.str p.1 .r12 p.2) ++ prologue)))
    (.seq (.loop finalizeBody .eq) (.block ((List.range 8).flatMap outW ++ restore))) := rfl

theorem argAddr_eq {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact sub_offset (by omega) (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (([.ldrSp .r12 4] : List Instr) ++ (stored.map (fun p => Instr.str p.1 .r12 p.2) ++ prologue))) s₀
      fun s => ∃ k, LInv s₀ k (cnt s₀ % 128 + 1) s := by
  have hr : cnt s₀ % 128 < 128 := Nat.mod_lt _ (by omega)
  have hsc := hp.scr_fit; have hst := hp.st_fit
  rw [List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine saveList_ok stored s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have := stored_bound p hp'
    exact ⟨by omega, by rw [h12]; omega, ⟨scR s₀, by simp [u₁.wr, hp.wr],
      by rw [h12]; exact contains_offset (by omega) (by omega)⟩⟩
  have hframe : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]
    exact saveMem_frame _ _ _ (by omega) stored fun p hp' => by have := (stored_bound p hp').2; omega
  unfold prologue
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide))
    fun s₄ u₄ => wp_and (op2_imm (by decide)) fun s₅ u₅ => ?_
  have hm₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have g₅ : ∀ r, r ∉ [Reg.r3, .r4, .r6, .r12] → s₅.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other r hr.2.1, u₄.other r hr.2.2.1, u₃.other r hr.1, g₂, u₁.other r hr.2.2.2]
  have hC₅ : Common s₀ s₅ := by
    refine ⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
      g₅ _ (by decide), ?_, ?_, by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
      by rw [hm₅]; exact hframe.mono (by simp), fun p hp' => ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h12]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem]
      exact hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp (by decide))))
        (by decide)
    · rw [hm₅, m₂, u₁.mem, h12, saveMem_stored _ _ _ p hp', u₁.other]
      simp only [stored, Impl.Sha512.Arm.Stream.saved, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr4 : s₅.gpr .r4 = BitVec.ofNat 32 (cnt s₀ % 128) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), and127, cnt_mod]
  -- The `0x80` byte.
  have hout : InRegions s₅.wr (stA s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) 1 := by
    refine ⟨stR s₀, by simp [hC₅.wr, hp.wr], ?_⟩
    rw [st_add]; exact contains_offset (by omega) (by omega)
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => wp_add (op2_reg _ _) fun s₇ u₇ =>
    wp_strb (a := stA s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) (by omega) ?_
      (by rw [u₇.wr, u₆.wr]; exact hout) fun s₈ g₈ => ?_
  · rw [u₇.gpr, u₆.other _ (by decide), u₆.other _ (by decide), hC₅.r0, hr4, buf_addr hp hr]
  obtain ⟨-, hfr, hsv⟩ := hC₅.writeBuf hp (n := cnt s₀ % 128) (xs := [0x80]) (by simp; omega)
  have hm₈ : s₈.mem = writeBytes s₅.mem (stA s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) [0x80] := by
    rw [g₈.mem, u₇.mem, u₆.mem, u₇.other _ (by decide), u₆.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_add (op2_imm (by decide)) fun s₉ u₉ => wp_add (op2_imm (by decide)) fun s₁₀ u₁₀ =>
    wp_mov (op2_lsr (by decide)) fun s₁₁ u₁₁ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → r ≠ .r1 → s₁₁.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₁.other r h2, u₁₀.other r h2, u₉.other r h1, g₈.gpr, u₇.other r h4, u₆.other r h3]
  have hm₁₁ : s₁₁.mem = s₈.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem]
  have hC₁₁ : Common s₀ s₁₁ :=
    ⟨by rw [u₁₁.rd, u₁₀.rd, u₉.rd, g₈.rd, u₇.rd, u₆.rd, hC₅.rd],
      by rw [u₁₁.wr, u₁₀.wr, u₉.wr, g₈.wr, u₇.wr, u₆.wr, hC₅.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₅.r0],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₅.r3],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₅.r6],
      by rw [u₁₁.sp, u₁₀.sp, u₉.sp, g₈.sp, u₇.sp, u₆.sp, hC₅.sp],
      by rw [hm₁₁, hm₈]; exact hfr, by rw [hm₁₁, hm₈]; exact hsv⟩
  have hr4₉ : s₉.gpr .r4 = BitVec.ofNat 32 (cnt s₀ % 128 + 1) := by
    rw [u₉.gpr, g₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), hr4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  have hr4' : s₁₁.gpr .r4 = BitVec.ofNat 32 (cnt s₀ % 128 + 1) := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), hr4₉]
  have hr5 : s₁₁.gpr .r5 = BitVec.ofNat 32 ((cnt s₀ % 128 + 16) / 128) := by
    rw [u₁₁.gpr, u₁₀.gpr, hr4₉, show (15 : BitVec 32) = BitVec.ofNat 32 15 from rfl, ← BitVec.ofNat_add,
      shr7 (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, R₀ s₀ iv m →
      bytesAt s₁₁.mem (stA s₀ + 64) (cnt s₀ % 128 + 1) = rest m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₅.mem (stA s₀ + 64) (cnt s₀ % 128) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₁, hm₈, e, hm₅]
    congr 1
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := frame_bytes hframe (R := stR s₀) (by simpa using hp.st_scr) (by simp) (i := 64 + i)
      (by show 64 + i < 192; omega)
    rwa [← st_add] at this
  have hstate : stateAt s₁₁.mem (stA s₀) = stateAt s₀.mem (stA s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₁₁, hm₈, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₅]
    exact frame_bytes hframe (R := stR s₀) (by simpa using hp.st_scr) (by simp) (by show i < 192; omega)
  by_cases hb : 112 ≤ cnt s₀ % 128
  · have hk : (cnt s₀ % 128 + 16) / 128 = 1 := by omega
    refine ⟨1, hC₁₁, (Nat.le_refl _), by omega, hr4', by rw [hr5, hk], fun iv m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 128 - (cnt s₀ % 128 + 1) = 127 - cnt s₀ % 128 by omega]
  · have hk : (cnt s₀ % 128 + 16) / 128 = 0 := by omega
    refine ⟨0, hC₁₁, by omega, by omega, hr4', by rw [hr5, hk], fun iv m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 112 - (cnt s₀ % 128 + 1) = 111 - cnt s₀ % 128 by omega]

/-! ## Output and epilogue -/

/-- `k` words of the digest are written. -/
structure Out (s₀ sD : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ keepRegs, s.gpr r = sD.gpr r
  sp : s.sp = sD.sp
  mem : s.mem = writeBytes sD.mem (outA s₀) (((stateAt sD.mem (stA s₀)).toList.take k).flatMap wordBytes)

theorem flat_length (H : HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap wordBytes).length = 8 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (wordBytes w).length = 8 := fun w _ => by simp [wordBytes]
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

theorem out_frame (s₀ : State) (m : Mem) (xs : List Byte) (hx : xs.length ≤ 64) :
    Frame [outR s₀] m (writeBytes m (outA s₀) xs) :=
  writeBytes_frame _ _ _ (by
    rw [show outA s₀ = outA s₀ + BitVec.ofNat 64 0 by simp]
    exact contains_offset (by omega) (by omega))

theorem out_step {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {k : Nat} (hk : k < 8)
    {s : State} (h : Out s₀ sD k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out s₀ sD (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  have hC := hD.1
  have hst := hp.st_fit; have ho := hp.out_fit
  have hr0 : s.gpr .r0 = st s₀ := by rw [h.keep _ (by simp [keepRegs]), hC.r0]
  have hr6 : s.gpr .r6 = out s₀ := by rw [h.keep _ (by simp [keepRegs]), hC.r6]
  have hP := flat_length (stateAt sD.mem (stA s₀)) k (Nat.le_of_lt hk)
  -- The word's halves, unchanged since `Done`.
  have hread : ∀ o, o + 4 ≤ 8 → s.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * k + o)) 32 =
      sD.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * k + o)) 32 := by
    intro o ho'
    rw [h.mem]
    refine (out_frame s₀ sD.mem _ (by omega)).readW (r := ⟨stA s₀ + BitVec.ofNat 64 (8 * k + o), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.st_out.sub_left (sub_offset (by omega) (by omega))
  have hw : (stateAt sD.mem (stA s₀))[k] = sD.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * k)) 64 := by
    simp [stateAt]
  have wlo : sD.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * k + 0)) 32 = lo (stateAt sD.mem (stA s₀))[k] := by
    rw [hw, readW_lo, Nat.add_zero]
  have whi : sD.mem.readW (stA s₀ + BitVec.ofNat 64 (8 * k + 4)) 32 = hi (stateAt sD.mem (stA s₀))[k] := by
    rw [hw, readW_hi, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  simp only [outW, List.cons_append, List.nil_append]
  refine wp_ldr (a := stA s₀ + BitVec.ofNat 64 (8 * k + 0)) (by omega) (by rw [hr0, addr_add (by omega), Nat.add_zero])
    ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_ldr (a := stA s₀ + BitVec.ofNat 64 (8 * k + 4)) (by omega)
    (by rw [u₁.other _ (by decide), hr0, addr_add (by omega)])
    (by rw [u₁.rd, u₁.wr]; exact ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₂ u₂ => wp_rev fun s₃ u₃ => wp_rev fun s₄ u₄ => ?_
  refine wp_str (a := outA s₀ + BitVec.ofNat 64 (8 * k)) (by omega)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hr6, addr_add (by omega)])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact ⟨outR s₀, by simp [h.wr, hp.wr], contains_offset (by omega) (by omega)⟩) fun s₅ g₅ => ?_
  refine wp_str (a := outA s₀ + BitVec.ofNat 64 (8 * k + 4)) (by omega)
    (by rw [g₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr6, addr_add (by omega)])
    (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
        exact ⟨outR s₀, by simp [h.wr, hp.wr], contains_offset (by omega) (by omega)⟩) fun s₆ g₆ =>
    hnext s₆ ⟨by rw [g₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
      by rw [g₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], fun r hr => ?_,
      by rw [g₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], ?_⟩
  · have : r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [g₆.gpr, g₅.gpr, u₄.other r this.1, u₃.other r this.2, u₂.other r this.2, u₁.other r this.1,
      h.keep r hr]
  · have v10 : s₄.gpr .r10 = rev (hi (stateAt sD.mem (stA s₀))[k]) := by
      rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.mem, hread 4 (by omega), whi]
    have v9 : s₅.gpr .r9 = rev (lo (stateAt sD.mem (stA s₀))[k]) := by
      rw [g₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hread 0 (by omega), wlo]
    have a4 : outA s₀ + BitVec.ofNat 64 (8 * k + 4) =
        outA s₀ + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (Spec.Sha256.wordBytes (hi (stateAt sD.mem (stA s₀))[k])).length := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    have a8 : outA s₀ + BitVec.ofNat 64 (8 * k) = outA s₀ +
        BitVec.ofNat 64 (((stateAt sD.mem (stA s₀)).toList.take k).flatMap wordBytes).length := by
      rw [hP]
    rw [g₆.mem, v9, g₅.mem, v10, u₄.mem, u₃.mem, u₂.mem, u₁.mem, writeW_rev, writeW_rev, a4,
      writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]), ← wordBytes_split, h.mem, a8,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Proof.Sha512.finalizeArm.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : Out s₀ sD 8 s) : WP isa (.block restore) s (Post s₀) := by
  have hC := hD.1
  have hfo := out_frame s₀ sD.mem (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes)
    (by rw [flat_length _ _ (Nat.le_refl _)])
  refine restore_ok (scr := scr s₀) (by rw [h.keep _ (by simp [keepRegs]), hC.r3]) hp.scr_fit
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs ho hmem _ _ hsp =>
      ⟨⟨preserved_saved hs,
        by rw [hsp, h.sp, hC.sp]⟩, fun iv m hr hl hc => ?_⟩
  · rw [h.mem, ← hC.saved p (saved_stored hp')]
    refine hfo.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (stored_sub (saved_stored hp'))
  · have e := bytesAt_writeBytes sD.mem (outA s₀) 0 (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes)
      (by rw [flat_length _ _ (Nat.le_refl _)]; omega)
    have e' : bytesAt (writeBytes sD.mem (outA s₀) (((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes))
        (outA s₀) 64 = ((stateAt sD.mem (stA s₀)).toList.take 8).flatMap wordBytes := by
      rw [flat_length _ _ (Nat.le_refl _), show outA s₀ + BitVec.ofNat 64 0 = outA s₀ by simp,
        show bytesAt sD.mem (outA s₀) 0 = [] from rfl, List.nil_append] at e
      exact e
    rw [← h.mem, ← hmem] at e'
    show bytesAt s'.mem (outA s₀) 64 = _
    rw [e', hD.2 iv m ⟨hr, hl, hc⟩, List.take_of_length_le (by simp)]

theorem out_all {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) :
    ∀ j ≤ 8, ∀ s, Out s₀ sD (8 - j) s →
      WP isa (.block (((List.range 8).drop (8 - j)).flatMap outW ++ restore)) s (Post s₀) := by
  intro j
  induction j with
  | zero =>
    intro _ s h
    rw [show (List.range 8).drop (8 - 0) = [] from rfl, List.flatMap_nil, List.nil_append]
    exact epilogue_ok hp hD h
  | succ j ih =>
    intro hj s h
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.append_assoc,
      List.getElem_range]
    refine out_step hp hD (by omega) h fun s' h' => ?_
    rw [show 8 - (j + 1) + 1 = 8 - j by omega]
    exact ih (by omega) s' (by rwa [show 8 - (j + 1) + 1 = 8 - j by omega] at h')

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa finalize s₀ (Post s₀) := by
  rw [finalize_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := Done s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have := out_all hp hD 8 (Nat.le_refl _) sD ⟨hD.1.rd, hD.1.wr, fun _ _ => rfl, rfl, by simp [writeBytes_nil]⟩
    rw [show 8 - 8 = 0 from rfl, List.drop_zero] at this
    exact this

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 8 bytes of stack arguments are public, the
second one pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [192, 64, 272], bases := [(.r0, 0)], argLen := 8,
    argBases := [(4, 2)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32) {k : Nat} (hk : k < 8) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem wf₀ {s : State} (h : Proof.Sha512.finalizeArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.st_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_st
    · exact hp.a_out
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha512.finalizeArm.pre s₁) (h₂ : Proof.Sha512.finalizeArm.pre s₂)
    (hpub : Proof.Sha512.finalizeArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, outR, scR, stA, outA, scA, st, out, scr, p0, a0, a1]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- A state satisfying the precondition: `out` at `0x2000` and the scratch
space at `0x3000`, passed on the stack at `0x5000`. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 272⟩]

theorem finalize_verified : Verified Arm.target finalize Proof.Sha512.finalizeArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
  · have e0 : stackArg sat 0 = 0x2000 := by decide
    have e1 : stackArg sat 1 = 0x3000 := by decide
    refine ⟨sat, ?_⟩
    simp only [Proof.Sha512.finalizeArm, e0, e1]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat, stackArgAddr, State.addr] at h₁ h₂
      bv_omega

end VG.Proof.Sha512.Arm.Stream.Finalize
