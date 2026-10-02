import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Streaming SHA-512 on ARMv7: common lemmas

Saving and restoring our caller's registers, the call of the compression
function in the terms of the streaming proofs, and arithmetic on 32-bit
values.
-/

namespace VG.Proof.Sha512.Arm.Stream

open VG VG.Arm VG.Impl.Sha512.Arm.Stream
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd saveMem saveList_ok restoreList_ok readW_writeW_save
  sub_offset wp_add wp_mov op2_imm)
open VG.Proof.Sha512.Arm (temps)
open VG.Proof.Sha512.Arm.Compress (compress_verified)
open VG.Spec.Sha512 (HashValue stateAt blockAt compress compressBlocks)

/-! ## Saving and restoring our caller's registers -/

theorem save_eq (b : Reg) : save b = saved.map (fun p => Instr.str p.1 b p.2) := rfl

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 272 ≤ 2 ^ 32)
    (hin : ∀ d, 224 ≤ d → d + 4 ≤ 260 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok saved s Q (fun p hp => ?_) k
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨by decide, by simp only; omega, hin _ (by decide) (by decide)⟩

set_option simprocs false in
theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) {N : Nat} (hN : N < 2 ^ 64) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ N) → Frame [⟨B, N⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (n := 32 / 8) h (by omega))).trans (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem saved_bound : ∀ p ∈ saved, 224 ≤ p.2 ∧ p.2 + 4 ≤ 260 := by decide

theorem restore_eq : restore = saved.map (fun p => Instr.ldr p.1 .r3 p.2) := rfl

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch`. -/
theorem restore_ok {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr) (hfit : scr.toNat + 272 ≤ 2 ^ 32)
    (hin : ∀ d, 224 ≤ d → d + 4 ≤ 260 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : ∀ p ∈ saved, s.mem.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  rw [restore_eq, ← List.append_nil (saved.map _)]
  refine restoreList_ok saved s Q (by decide) (fun p hp => ?_)
    fun s' ho hr hm hrd hwr hsp => WP.block_nil (k s' (fun p hp => ?_) hr hm hrd hwr hsp)
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [h3]
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by simp only; omega, hin _ (by decide) (by decide)⟩
  · rw [ho p hp, h3, hsv p hp]

/-- The saved registers are preserved by the ABI. -/
theorem preserved_saved {s₀ s' : State} (hs : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs (.r4, 224) (by simp [saved])
  · exact hs (.r5, 228) (by simp [saved])
  · exact hs (.r6, 232) (by simp [saved])
  · exact hs (.r7, 236) (by simp [saved])
  · exact hs (.r8, 240) (by simp [saved])
  · exact hs (.r9, 244) (by simp [saved])
  · exact hs (.r10, 248) (by simp [saved])
  · exact hs (.r11, 252) (by simp [saved])
  · exact hs (.lr, 256) (by simp [saved])

/-! ## The call of the compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

/-- No instruction of the compression function writes `r0` or `r3`. -/
theorem r03_ok : ((instrs Impl.Sha512.Arm.compress).all fun i =>
    dstOf i != some .r0 && dstOf i != some .r3) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem r0_ok : ∀ i ∈ instrs Impl.Sha512.Arm.compress, dstOf i ≠ some .r0 := fun i hi => by
  have := List.all_eq_true.mp r03_ok i hi
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.1

theorem r3_ok : ∀ i ∈ instrs Impl.Sha512.Arm.compress, dstOf i ≠ some .r3 := fun i hi => by
  have := List.all_eq_true.mp r03_ok i hi
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.2

/-- The registers the compression function's contract accounts for: every
register but its temporaries and `lr` is `r0`, `r3` or callee-saved. -/
theorem regs_split (r : Reg) (ht : r ∉ temps) (hl : r ≠ .lr) : r = .r0 ∨ r = .r3 ∨ r ∈ preserved := by
  revert ht hl; cases r <;> decide

/-- What `compressAt` needs of the state it starts from: the state at `st` in
`r0`, the scratch space `scr` in `r3`. -/
structure AtPre (st scr : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = st
  r3 : s.gpr .r3 = scr
  hS : ⟨State.addr st, 192⟩ ∈ s.wr
  hV : ⟨State.addr scr, 272⟩ ∈ s.wr

/-- The registers the compression function is called with. -/
structure CallRegs (st scr : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = st + 64
  r2 : s.gpr .r2 = 1
  r3 : s.gpr .r3 = scr
  hS : ⟨State.addr st, 192⟩ ∈ s.wr
  hV : ⟨State.addr scr, 272⟩ ∈ s.wr

/-- The arguments of the call. -/
abbrev argsAt : List Instr := [.dp .add .r1 .r0 (.imm 64), .mov .r2 (.imm 1)]

theorem compressAt_eq : compressAt = .seq (.block argsAt) compressCall := rfl

theorem argsAt_ok {st scr : BitVec 32} {s : State} (h : AtPre st scr s) :
    WP isa (.block argsAt) s fun s' => CallRegs st scr s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r := by
  refine wp_add (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  exact ⟨⟨by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r0], by rw [u₂.other _ (by decide), u₁.gpr, h.r0],
    u₂.gpr, by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r3], by rw [wr₂]; exact h.hS,
    by rw [wr₂]; exact h.hV⟩, by rw [u₂.rd, u₁.rd], wr₂, by rw [u₂.mem, u₁.mem], by rw [u₂.sp, u₁.sp],
    fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1]⟩

/-- The regions the compression function is given to read (the block in the
buffer) and to write (the hash value and the scratch space it uses). -/
abbrev rdC (st : BitVec 32) : List Region := [⟨State.addr (st + 64), 128 * 1⟩]
abbrev wrC (st scr : BitVec 32) : List Region := [⟨State.addr st, 64⟩, ⟨State.addr scr, 224⟩]

theorem addr_st64 {st : BitVec 32} (f₀ : st.toNat + 192 ≤ 2 ^ 32) :
    State.addr (st + 64) = State.addr st + BitVec.ofNat 64 64 := addr_add (k := 64) (by omega)

theorem callEntry_gpr_of {s : State} {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

section
variable {st scr : BitVec 32} (f₀ : st.toNat + 192 ≤ 2 ^ 32) (f₃ : scr.toNat + 272 ≤ 2 ^ 32)
    (d : Region.Disjoint ⟨State.addr st, 192⟩ ⟨State.addr scr, 272⟩)
include f₀ f₃ d

/-- The compression function may be called: its precondition holds, narrowed
to `rdC` and `wrC`. -/
theorem callPre {s : State} (c : CallRegs st scr s) :
    Proof.Sha512.compressArm.pre (s.callEntry.withRegions (rdC st) (wrC st scr)) ∧
    Covers (rdC st ++ wrC st scr) (s.rd ++ s.wr) ∧ Covers (wrC st scr) s.wr := by
  have hb := addr_st64 f₀
  have hbt : (st + 64).toNat = st.toNat + 64 := by
    rw [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega)]
  have sS : Region.Sub ⟨State.addr st, 64⟩ ⟨State.addr st, 192⟩ := Region.sub_prefix (by omega)
  have sB : Region.Sub ⟨State.addr (st + 64), 128 * 1⟩ ⟨State.addr st, 192⟩ := by
    rw [hb]; exact sub_offset (off := 64) (len := 128 * 1) (len' := 192) (by decide) (by decide)
  have sV : Region.Sub ⟨State.addr scr, 224⟩ ⟨State.addr scr, 272⟩ := Region.sub_prefix (by omega)
  have dBS : Region.Disjoint ⟨State.addr (st + 64), 128 * 1⟩ ⟨State.addr st, 64⟩ := by
    rw [hb]; exact Offset.disjoint_base _ (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha512.compressArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr_of (show Reg.r0 ∉ linkRegs by decide),
      callEntry_gpr_of (show Reg.r1 ∉ linkRegs by decide), callEntry_gpr_of (show Reg.r2 ∉ linkRegs by decide),
      callEntry_gpr_of (show Reg.r3 ∉ linkRegs by decide), c.r0, c.r1, c.r2, c.r3]
    exact ⟨rfl, trivial, (d.sub_left sS).sub_right sV, dBS, (d.sub_left sB).sub_right sV, by omega,
      by rw [hbt]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega, by omega⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ c.hS, 64, hb, by simp⟩
    · exact ⟨_, List.mem_append_right _ c.hS, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ c.hV, 0, by simp, by simp⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, c.hS, 0, by simp, by simp⟩
    · exact ⟨_, c.hV, 0, by simp, by simp⟩

/-- Compressing the buffer of the state at `r0` into its hash value, with
the scratch space (272 bytes, of which the compression function uses 224) at
`r3`. -/
theorem compressBuf_ok {s : State} (h : AtPre st scr s) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r, r ∉ temps → r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨State.addr st, 192⟩, ⟨State.addr scr, 224⟩] s.mem s'.mem →
      stateAt s'.mem (State.addr st) =
        compress (stateAt s.mem (State.addr st)) (blockAt s.mem (State.addr st + 64)) → Q s') :
    WP isa compressAt s Q := by
  rw [compressAt_eq]
  refine WP.seq (WP.mono (argsAt_ok h) fun s₂ ⟨c, rd₂, wr₂, m₂, sp₂, g₂⟩ => ?_)
  have hb := addr_st64 f₀
  have sS : Region.Sub ⟨State.addr st, 64⟩ ⟨State.addr st, 192⟩ := Region.sub_prefix (by omega)
  obtain ⟨hpre, hc, hw⟩ := callPre f₀ f₃ d c
  refine WP.call (k := Proof.Sha512.compressArm) compress_verified.1 hpre hc hw ?_
  intro s' hrd hwr hsp hf hcs hg hpost
  simp only [Proof.Sha512.compressArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr_of (show Reg.r0 ∉ linkRegs by decide), callEntry_gpr_of (show Reg.r1 ∉ linkRegs by decide),
    callEntry_gpr_of (show Reg.r2 ∉ linkRegs by decide), c.r0, c.r1, c.r2, m₂] at hpost
  rw [show (BitVec.toNat (1 : BitVec 32)) = 1 from rfl, compressBlocks_one, hb] at hpost
  refine hQ s' (hrd.trans rd₂) (hwr.trans wr₂) (fun r hr hlr => ?_) (hsp.trans sp₂) ?_ hpost
  · rcases regs_split r hr hlr with rfl | rfl | hp
    · rw [hg _ r0_ok (by decide), c.r0, h.r0]
    · rw [hg _ r3_ok (by decide), c.r3, h.r3]
    · have h1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hp
      have h2 : r ≠ .r2 := by rintro rfl; simp [preserved] at hp
      rw [hcs r hp hlr, g₂ r h1 h2]
  · rw [← m₂]
    refine hf.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, sS⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- Two runs of `compressAt` from states that agree on `st` and `scr` leak
the same trace: the arguments by the taint analysis, the call by the
compression function's contract. -/
theorem compressAt_rel :
    RelCT isa (fun s₁ s₂ => AtPre st scr s₁ ∧ AtPre st scr s₂) compressAt fun _ _ => True := by
  rw [compressAt_eq]
  refine RelCT.seq (R := fun s₁ s₂ => CallRegs st scr s₁ ∧ CallRegs st scr s₂) ?_ ?_
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => Taint.agree_ofRegs fun r hr => ?_)
      (c := .block argsAt) (by taint_decide)).wp
      (F₁ := CallRegs st scr) (F₂ := CallRegs st scr) fun _ _ h =>
        ⟨WP.mono (argsAt_ok h.1) fun _ h => h.1, WP.mono (argsAt_ok h.2) fun _ h => h.1⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
    simp only [List.mem_singleton] at hr
    subst hr
    rw [h.1.r0, h.2.r0]
  · refine RelCT.call compress_verified.1 compress_verified.2.1 (rdC st) (wrC st scr) fun s₁ s₂ ⟨c₁, c₂⟩ => ?_
    obtain ⟨p₁, v₁, w₁⟩ := callPre f₀ f₃ d c₁
    obtain ⟨p₂, v₂, w₂⟩ := callPre f₀ f₃ d c₂
    refine ⟨p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
    simp only [Proof.Sha512.compressArm, State.withRegions_gpr,
      callEntry_gpr_of (show Reg.r0 ∉ linkRegs by decide), callEntry_gpr_of (show Reg.r1 ∉ linkRegs by decide),
      callEntry_gpr_of (show Reg.r2 ∉ linkRegs by decide), callEntry_gpr_of (show Reg.r3 ∉ linkRegs by decide),
      c₁.r0, c₁.r1, c₁.r2, c₁.r3, c₂.r0, c₂.r1, c₂.r2, c₂.r3, and_self]

end

/-! ## Arithmetic -/

theorem and127 (x : BitVec 32) : x &&& 127 = BitVec.ofNat 32 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end VG.Proof.Sha512.Arm.Stream

/-!
# Streaming SHA-512 on ARMv7: `update`

The structure of the SHA-256 proof (`VG.Proof.MdStream.Arm.Update`), with
`state` in `r0`, `scratch` in `r3`, `data` in `r5`, the bytes left in `r6` and
the buffered bytes in `r4`; every block goes through the buffer, which is
compressed as soon as it is full.
-/

namespace VG.Proof.Sha512.Arm.Stream.Update

open VG VG.Arm VG.Impl.Sha512.Arm.Stream
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_and
  wp_subs wp_cmp wp_ldrb wp_strb wp_ldrSp saveMem sub_offset frame_bytes bytesAt_getD eval_eq
  eval_ne ofNat_beq_zero sub_ofNat sub_beq ofNat_shr)
open VG.Proof.Sha512.Arm (temps)
open VG.Proof.Sha512.Arm.Stream
open VG.Proof.Sha512.Stream
open VG.Spec.Sha512 (HashValue stateAt blockAt compress parseBlock bytesAt)
open VG.Proof.Sha512 (countArm)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev cnt : Nat := (countArm s₀).toNat
abbrev dp : BitVec 32 := stackArg s₀ 0
abbrev len : Nat := (stackArg s₀ 1).toNat
abbrev scr : BitVec 32 := stackArg s₀ 2
abbrev stA : Addr := State.addr (st s₀)
abbrev dA : Addr := State.addr (dp s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev stR : Region := ⟨stA s₀, 192⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, 272⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 12⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dA s₀) (len s₀)

/-- The messages the initial state represents, from the initial hash value `iv`. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha512.Repr iv s₀.mem (stA s₀) m ∧ countArm s₀ = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 192 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 272 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 12 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Sha512.updateArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 128 = (s₀.gpr .r2).toNat % 128 := by
  simp only [cnt, countArm]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : HashValue} {m : List Byte} (h : R₀ s₀ iv m) :
    cnt s₀ % 128 = m.length % 128 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (stackArg s₀ 1).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = dp s₀ + BitVec.ofNat 32 c
  r6 : s.gpr .r6 = BitVec.ofNat 32 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r4 : s.gpr .r4 = BitVec.ofNat 32 ((cnt s₀ + c) % 128)
  repr : ∀ iv m, R₀ s₀ iv m → Spec.Sha512.Repr iv s.mem (stA s₀) (m ++ (D s₀).take c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.r0, .r3, .r5, .r6, .lr], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r0 := by rw [hg _ (by simp)]; exact h.r0
  r3 := by rw [hg _ (by simp)]; exact h.r3
  sp := hsp.trans h.sp
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : ∀ r ∈ [Reg.r0, .r3, .r5, .r6, .lr, .r4], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_append_left [Reg.r4] hr)) hm hrd hwr hsp with
    r4 := by rw [hg _ (by simp)]; exact h.r4
    repr := by rw [hm]; exact h.repr }

theorem Inv.of_upd {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ [Reg.r0, .r3, .r5, .r6, .lr, .r4]) : Inv s₀ c s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Inv.of_flags {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s) (u : Fupd s s') : Inv s₀ c s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR s₀) :=
  sub_offset (by have := (saved_bound p hp).2; omega) (by have := (saved_bound p hp).2; omega)

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dA s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact frame_bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
    (by have := len_lt s₀; show len s₀ ≤ 2 ^ 64; omega) hi

theorem length_mid (s₀ : State) {iv : HashValue} {m : List Byte} (hm : R₀ s₀ iv m) {c : Nat}
    (hc : c ≤ len s₀) : (m ++ (D s₀).take c).length % 128 = (cnt s₀ + c) % 128 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Buffering data -/

section
variable (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % 128
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (128 - rr s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := stA s₀ + 64 + BitVec.ofNat 64 (rr s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt s₀ c)
end

theorem rr_lt (s₀ : State) (c : Nat) : rr s₀ c < 128 := Nat.mod_lt _ (by omega)
theorem tt_le (s₀ : State) (c : Nat) : tt s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt s₀ c ≤ 128 - rr s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr s₀ c = (cnt s₀ + c) % 128 := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt s₀ c = min (128 - rr s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q s₀ c = stA s₀ + BitVec.ofNat 64 (64 + rr s₀ c) := by
  simp only [q, BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

theorem xs_length (s₀ : State) (c : Nat) : (xs s₀ c).length = tt s₀ c := by
  have := tt_le s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

/-- Byte `k` of the buffer, addressed as `[r0 + k, #64]`. -/
theorem buf_addr {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) :
    State.addr (st s₀ + BitVec.ofNat 32 k + BitVec.ofNat 32 64) = stA s₀ + 64 + BitVec.ofNat 64 k := by
  have := hp.st_fit
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), Nat.add_comm, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  rfl

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = dp s₀ + BitVec.ofNat 32 (c + j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (len s₀ - c - tt s₀ c)
  r4 : s.gpr .r4 = BitVec.ofNat 32 (rr s₀ c + j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (tt s₀ c - j)
  mem : s.mem = writeBytes mI (q s₀ c) ((xs s₀ c).take j)

theorem write_frame (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt s₀ c) :
    Frame [stR s₀] mI (writeBytes mI (q s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.ldrb .r12 .r5 0, .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 64, .dp .add .r5 .r5 (.imm 1),
    .dp .add .r4 .r4 (.imm 1), .subs .r8 .r8 (.imm 1)]

theorem copy_step {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {j : Nat}
    (hj : j < tt s₀ c) {s : State} (h : Copy s₀ c sI.mem j s) :
    WP isa (.block copyBody) s fun s' =>
      Copy s₀ c sI.mem (j + 1) s' ∧ s'.z = (BitVec.ofNat 32 (tt s₀ c - (j + 1)) == 0) := by
  have hlen := len_lt s₀; have hd := hp.d_fit
  have hc := hI.c_le
  have hr := rr_lt s₀ c
  have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dA s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (dA s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact frame_bytes (write_frame s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (q s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length s₀ c
  unfold copyBody
  refine wp_ldrb (a := dA s₀ + BitVec.ofNat 64 (c + j)) (by omega)
    (by rw [h.r5, BitVec.add_zero, addr_add (by omega)]) hin
    fun s₁ u₁ => ?_
  refine wp_add (op2_reg _ _) fun s₂ u₂ => wp_strb (a := q s₀ c + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.r0, h.r4, buf_addr hp (by omega), q]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r12 → r ≠ .r1 → r ≠ .r5 → r ≠ .r4 → r ≠ .r8 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have h8 : s₆.gpr .r8 = BitVec.ofNat 32 (tt s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r8, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega),
      Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r0 (by decide) (by decide) (by decide) (by decide) (by decide), h.r0]
  · rw [g .r3 (by decide) (by decide) (by decide) (by decide) (by decide), h.r3]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r5, BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r6 (by decide) (by decide) (by decide) (by decide) (by decide), h.r6]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r4, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · have hj' : j < (xs s₀ c).length := by omega
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (xs s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (D s₀) (c + j) 0).setWidth 32).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]
  · rw [z₆, ← u₆.gpr, h8]

theorem copy_loop_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem 0 s) (ht : 0 < tt s₀ c) :
    WP isa (.loop (.block copyBody) .ne) s (Copy s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hp hI hj hc) fun s' ⟨hc', hz'⟩ => ?_
  have hz : isa.eval .ne s' = some (decide (tt s₀ c - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s' = _
    rw [eval_ne, hz', ofNat_beq_zero (by have := tt_le' s₀ c; omega)]
    simp
  by_cases hl : tt s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rwa [show j + 1 = tt s₀ c by omega] at hc'
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) :
    let mem := writeBytes sI.mem (q s₀ c) (xs s₀ c)
    Frame [stR s₀, scR s₀] s₀.mem mem ∧ Saved s₀ mem ∧ stateAt mem (stA s₀) = stateAt sI.mem (stA s₀) ∧
      bytesAt mem (stA s₀ + 64) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (stA s₀ + 64) (rr s₀ c) ++ xs s₀ c := by
  intro mem
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have hxs := xs_length s₀ c
  have hf : Frame [stR s₀] sI.mem mem := by
    have := write_frame s₀ c sI.mem (tt s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · rw [← hI.saved p hp']
    refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.st_scr.symm.sub_left (saved_sub hp')
  · apply stateAt_congr
    intro i hi
    simp only [mem, q_eq]
    exact writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- A full buffer: compress it. -/
theorem fill_full {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hfull : rr s₀ c + tt s₀ c = 128) :
    WP isa (.seq compressAt (.block [.mov .r4 (.imm 0)])) s (Inv s₀ (c + tt s₀ c)) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have hst := hp.st_fit; have hsc := hp.scr_fit
  obtain ⟨hfr, hsv, hstt, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  have e64 : Region.Sub ⟨scA s₀, 224⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine WP.seq (compressBuf_ok hst hsc hp.st_scr ⟨h.r0, h.r3, by simp [h.wr, hp.wr], by simp [h.wr, hp.wr]⟩
    fun s' hrd hwr hg hsp hf hstate => ?_)
  refine wp_mov (op2_imm (by decide)) fun s'' u => WP.block_nil ?_
  have e : ∀ r, r ≠ .r4 → r ∉ temps → r ≠ .lr → s''.gpr r = s.gpr r := fun r h4 ht hl => by
    rw [u.other r h4, hg r ht hl]
  refine ⟨⟨by omega, by rw [u.rd, hrd, h.rd], by rw [u.wr, hwr, h.wr],
    by rw [e _ (by decide) (by decide) (by decide), h.r0],
    by rw [e _ (by decide) (by decide) (by decide), h.r3], by rw [u.sp, hsp, h.sp],
    by rw [e _ (by decide) (by decide) (by decide), h.r5],
    by rw [e _ (by decide) (by decide) (by decide), h.r6, Nat.sub_sub],
    ?_, fun p hp' => ?_⟩, ?_, fun iv m hm => ?_⟩
  · rw [u.mem]
    rw [hmem] at hf
    refine hfr.trans (hf.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, e64⟩
  · rw [u.mem, ← hsv p hp', ← hmem]
    refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hp.st_scr.symm.sub_left (saved_sub hp')
    · have := saved_bound p hp'
      exact Offset.disjoint_base _ (by omega) (by omega)
  · rw [u.gpr]
    show 0 = BitVec.ofNat 32 ((cnt s₀ + (c + tt s₀ c)) % 128)
    rw [show (cnt s₀ + (c + tt s₀ c)) % 128 = 0 by have := rr_eq s₀ c; omega]; rfl
  · rw [← take_add_data]
    have hmod := length_mid s₀ hm hc
    refine repr_append_block (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [u.mem, hstate, hmem, hstt]
    refine congrArg (compress _) (parseBlock_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 128 from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hnf : rr s₀ c + tt s₀ c ≠ 128) : Inv s₀ (len s₀) s := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hstt, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine ⟨⟨(Nat.le_refl _), h.rd, h.wr, h.r0, h.r3, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩
  · rw [h.r5]; congr 2; omega
  · rw [h.r6]; congr 1; omega
  · rw [h.r4]; congr 1; omega
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega, ← take_add_data]
    refine repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hstt]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_eq : fill =
    .seq (.block [.mov .r8 (.imm 128), .dp .sub .r8 .r8 (.reg .r4), .mov .r12 (.shifted .r6 .lsr 7),
      .cmp .r12 (.imm 0)])
    (.seq (.ite .eq
        (.seq (.block [.dp .add .r12 .r6 (.reg .r4), .mov .r12 (.shifted .r12 .lsr 7), .cmp .r12 (.imm 0)])
          (.ite .eq (.block [.mov .r8 (.reg .r6)]) (.block [])))
        (.block []))
    (.seq (.block [.dp .sub .r6 .r6 (.reg .r8)])
    (.seq (.loop (.block copyBody) .ne)
    (.seq (.block [.cmp .r4 (.imm 128)])
      (.ite .eq (.seq compressAt (.block [.mov .r4 (.imm 0)])) (.block [])))))) := rfl

theorem shr7 {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> 7 = BitVec.ofNat 32 (a / 128) :=
  ofNat_shr h

theorem cmp0 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a - 0 == 0) = decide (a = 0) := by
  rw [show BitVec.ofNat 32 a - 0 = BitVec.ofNat 32 a by simp]; exact ofNat_beq_zero h

/-- The bytes consumed after an iteration that started with `c`. -/
def nextC (s₀ : State) (c : Nat) : Nat := if rr s₀ c + tt s₀ c = 128 then c + tt s₀ c else len s₀

/-- `fill` before the test of whether the buffer is full, and after. -/
def fillPre : Prog isa :=
    .seq (.seq (.seq (.seq (.block [.mov .r8 (.imm 128), .dp .sub .r8 .r8 (.reg .r4), .mov .r12 (.shifted .r6 .lsr 7),
      .cmp .r12 (.imm 0)])
    (.ite .eq
        (.seq (.block [.dp .add .r12 .r6 (.reg .r4), .mov .r12 (.shifted .r12 .lsr 7), .cmp .r12 (.imm 0)])
          (.ite .eq (.block [.mov .r8 (.reg .r6)]) (.block [])))
        (.block [])))
    (.block [.dp .sub .r6 .r6 (.reg .r8)]))
    (.loop (.block copyBody) .ne))
    (.block [.cmp .r4 (.imm 128)])

def fillEnd : Prog isa := .ite .eq (.seq compressAt (.block [.mov .r4 (.imm 0)])) (.block [])

theorem nextC_gt (s₀ : State) {c : Nat} (hcl : c < len s₀) : c < nextC s₀ c := by
  have := tt_eq s₀ c; have := rr_lt s₀ c
  simp only [nextC]; split <;> omega

/-- Where `fill` tests whether the buffer is full. -/
def Mid (s₀ : State) (c : Nat) (s : State) : Prop := AtPre (st s₀) (scr s₀) s ∧
  VG.Arm.eval .eq s = some (decide (rr s₀ c + tt s₀ c = 128)) ∧ WP isa fillEnd s (Inv s₀ (nextC s₀ c))

theorem pre_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa fillPre s (Mid s₀ c) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hc := hI.c_le; have hlen := len_lt s₀
  unfold fillPre
  refine WP.seq (WP.seq (WP.seq (WP.seq ?_)))
  -- `r8 := 128 - r; r12 := len >> 7`
  refine (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have hI₄ : Inv s₀ c s₄ := ((((hI.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide))).of_flags f₄
  have h8₄ : s₄.gpr .r8 = BitVec.ofNat 32 (128 - rr s₀ c) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r4,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, sub_ofNat (by omega)]
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hz₄ : s₄.z = decide ((len s₀ - c) / 128 = 0) := by
    rw [z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r6, shr7 (by omega), cmp0 (by omega)]
  -- `r8 := min(r8, len)`
  refine (WP.mono (Q := fun (s₅ : State) => Inv s₀ c s₅ ∧ s₅.gpr .r8 = BitVec.ofNat 32 (tt s₀ c) ∧
    s₅.mem = s.mem) ?_ fun s₅ ⟨hI₅, h8₅, hm₅⟩ => ?_)
  · refine WP.ite (decide ((len s₀ - c) / 128 = 0))
      (by show VG.Arm.eval .eq s₄ = _; rw [eval_eq, hz₄]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (wp_add (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_lsr (by decide)) fun s₇ u₇ =>
        wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_)
      have hI₈ : Inv s₀ c s₈ := ((hI₄.of_upd u₆ (by decide)).of_upd u₇ (by decide)).of_flags f₈
      have hz₈ : s₈.z = decide ((len s₀ - c + rr s₀ c) / 128 = 0) := by
        rw [z₈, u₇.gpr, u₆.gpr, hI₄.r6, hI₄.r4, ← BitVec.ofNat_add, shr7 (by omega), cmp0 (by omega)]
      have e₈ : ∀ r, r ≠ .r12 → s₈.gpr r = s₄.gpr r := fun r h => by rw [f₈.gpr, u₇.other r h, u₆.other r h]
      have hm₈ : s₈.mem = s.mem := by rw [f₈.mem, u₇.mem, u₆.mem, hm₄]
      refine WP.ite (decide ((len s₀ - c + rr s₀ c) / 128 = 0))
        (by show VG.Arm.eval .eq s₈ = _; rw [eval_eq, hz₈]) (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine wp_mov (op2_reg _ _) fun s₉ u₉ => WP.block_nil ⟨hI₈.of_upd u₉ (by decide), ?_,
          by rw [u₉.mem, hm₈]⟩
        rw [u₉.gpr, hI₈.r6]; congr 1; omega
      · simp only [decide_eq_false_iff_not] at hb'
        refine WP.block_nil ⟨hI₈, ?_, hm₈⟩
        rw [e₈ _ (by decide), h8₄]; congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨hI₄, ?_, hm₄⟩
      rw [h8₄]; congr 1; omega
  -- `r6 -= r8`
  refine (wp_sub (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_)
  have hC₀ : Copy s₀ c s.mem 0 s₆ := by
    have e : ∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r := fun r h => u₆.other r h
    refine ⟨Nat.zero_le _, by rw [u₆.rd, hI₅.rd], by rw [u₆.wr, hI₅.wr],
      by rw [e _ (by decide), hI₅.r0], by rw [e _ (by decide), hI₅.r3],
      by rw [u₆.sp, hI₅.sp], by rw [e _ (by decide), hI₅.r5, Nat.add_zero], ?_,
      by rw [e _ (by decide), hI₅.r4, Nat.add_zero], by rw [e _ (by decide), h8₅, Nat.sub_zero], ?_⟩
    · rw [u₆.gpr, hI₅.r6, h8₅, sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₆.mem, hm₅, List.take_zero, writeBytes_nil]
  -- Copy the bytes.
  refine (WP.mono (copy_loop_ok hp hI hC₀ (by omega)) fun s₇ hC => ?_)
  -- Is the buffer full?
  refine (wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_)
  have hC₈ : Copy s₀ c s.mem (tt s₀ c) s₈ :=
    ⟨hC.j_le, by rw [f₈.rd, hC.rd], by rw [f₈.wr, hC.wr], by rw [f₈.gpr, hC.r0], by rw [f₈.gpr, hC.r3],
      by rw [f₈.sp, hC.sp], by rw [f₈.gpr, hC.r5], by rw [f₈.gpr, hC.r6],
      by rw [f₈.gpr, hC.r4], by rw [f₈.gpr, hC.r8], by rw [f₈.mem, hC.mem]⟩
  have hz : VG.Arm.eval .eq s₈ = some (decide (rr s₀ c + tt s₀ c = 128)) := by
    rw [eval_eq, z₈, hC.r4, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl,
      sub_beq (by omega) (by omega)]
  refine ⟨⟨hC₈.r0, hC₈.r3, by simp [hC₈.wr, hp.wr], by simp [hC₈.wr, hp.wr]⟩, hz,
    WP.ite (decide (rr s₀ c + tt s₀ c = 128)) hz (fun hb => ?_) (fun hb => ?_)⟩
  · simp only [decide_eq_true_eq] at hb
    have e : nextC s₀ c = c + tt s₀ c := by simp only [nextC]; split <;> omega
    rw [e]
    exact fill_full hp hI hC₈ hb
  · simp only [decide_eq_false_iff_not] at hb
    have e : nextC s₀ c = len s₀ := by simp only [nextC]; split <;> omega
    rw [e]
    exact WP.block_nil (fill_done hp hI hC₈ hb)

theorem fill_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa fill s fun s' => ∃ c', c < c' ∧ Inv s₀ c' s' := by
  rw [fill_eq]
  exact WP.assoc (WP.assoc (WP.assoc (WP.assoc (WP.seq (WP.mono (pre_ok hp hI hcl)
    fun _ h => WP.mono h.2.2 fun _ h => ⟨_, nextC_gt s₀ hcl, h⟩)))))

/-! ## One iteration -/

/-- The loop's test: bytes left? -/
theorem test_ok {s₀ : State} {c : Nat} {s : State} (hI : Inv s₀ c s) :
    WP isa (.block [.cmp .r6 (.imm 0)]) s fun s' => Inv s₀ c s' ∧ s'.z = decide (len s₀ - c = 0) := by
  have hlen := len_lt s₀
  have hc'' := hI.c_le
  refine wp_cmp (op2_imm (by decide)) fun s'' f'' z'' => WP.block_nil ⟨hI.of_flags f'', ?_⟩
  rw [z'', hI.r6, cmp0 (by omega)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa updateBody s fun s' => ∃ c', c < c' ∧ Inv s₀ c' s' ∧ s'.z = decide (len s₀ - c' = 0) :=
  WP.seq (WP.mono (fill_ok hp hI hcl) fun _ ⟨c', hc', hI'⟩ =>
    WP.mono (test_ok hI') fun _ h => ⟨c', hc', h⟩)

/-! ## Prologue and epilogue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [.mov .r3 (.reg .r12), .dp .and .r4 .r2 (.imm 127), .ldrSp .r5 0, .ldrSp .r6 4, .cmp .r6 (.imm 0)]

theorem update_eq : update = .seq (.block (([.ldrSp .r12 8] : List Instr) ++ save .r12 ++ prologue))
    (.seq (.ite .eq (.block []) (.loop updateBody .ne)) (.block restore)) := rfl

/-- The stack arguments, word by word. -/
theorem argAddr_eq {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 3) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 3) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact sub_offset (by omega) (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (([.ldrSp .r12 8] : List Instr) ++ save .r12 ++ prologue)) s₀
      fun s => Inv s₀ 0 s ∧ s.z = decide (len s₀ = 0) := by
  have hsc := hp.scr_fit; have hst := hp.st_fit
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_offset (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The stack arguments are unchanged by the save.
  have hframe : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]
    exact saveMem_frame _ _ _ (by omega) saved fun p hp' => by have := (saved_bound p hp').2; omega
  have harg : ∀ k, k < 3 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp hk))) (by decide)
  unfold prologue
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_and (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide)
    (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide))
    fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  have mm : s₇.mem = s₂.mem := by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r12] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₇.gpr, u₆.other r hr.2.2.2.1, u₅.other r hr.2.2.1, u₄.other r hr.2.1, u₃.other r hr.1, g₂,
      u₁.other r hr.2.2.2.2]
  have h6' : s₆.gpr .r6 = stackArg s₀ 1 := by
    rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
  have h6 : s₇.gpr .r6 = stackArg s₀ 1 := by rw [f₇.gpr, h6']
  refine ⟨⟨⟨Nat.zero_le _, by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr], g _ (by decide), ?_,
    by rw [f₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, harg 0 (by decide)]; simp
  · rw [h6]; simp
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, saveMem_saved _ _ _ p hp', u₁.other]
    simp only [Impl.Sha512.Arm.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂,
      u₁.other _ (by decide), and127, Nat.add_zero, cnt_mod]
  · intro iv m hm
    rw [List.take_zero, List.append_nil, mm]
    exact repr_congr (fun i hi => frame_bytes hframe (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi) hm.1
  · rw [z₇, h6']
    have := cmp0 (a := len s₀) (len_lt s₀)
    simpa using this

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ Proof.Sha512.updateArm.post s₀ s' := by
  refine restore_ok hI.r3 hp.scr_fit
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hI.rd, hI.wr, hp.wr], contains_offset (by omega) (by omega)⟩) s₀.gpr
    hI.saved fun s' hs ho hmem _ _ hsp =>
      ⟨⟨preserved_saved hs, by rw [hsp, hI.sp]⟩, fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (Nat.le_of_eq (D_length s₀)), ← hmem] at this

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha512.updateArm.post s₀ s' := by
  have hlen := len_lt s₀
  rw [update_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (body_ok hp hI hcl) fun s' ⟨c', hc, hI', hz'⟩ => ?_
    have hc' := hI'.c_le
    have hz : isa.eval .ne s' = some (decide (len s₀ - c' ≠ 0)) := by
      show VG.Arm.eval .ne s' = _
      rw [eval_ne, hz']
      simp
    by_cases hl : len s₀ - c' = 0
    · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
      rwa [show c' = len s₀ by omega] at hI'
    · exact .inr ⟨by rw [hz, decide_eq_true hl], len s₀ - c', by omega, c', rfl, by omega, hI'⟩

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 12 bytes of stack arguments are public, the
third one pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [192, 272], bases := [(.r0, 0)], argLen := 12,
    argBases := [(8, 1)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) {k : Nat} (hk : k < 12) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem wf₀ {s : State} (h : Proof.Sha512.updateArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 12⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha512.updateArm.pre s₁) (h₂ : Proof.Sha512.updateArm.pre s₂)
    (hpub : Proof.Sha512.updateArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1, a2⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stA, scA, st, scr, p0, a2]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 := by omega
    rcases this with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

/-- A state satisfying the precondition (with no data, and the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0, 0⟩, ⟨0x4000, 12⟩]
  wr := [⟨0x1000, 192⟩, ⟨0, 272⟩]

/-! ## Constant time, by relating two runs

The prologue is checked by the taint analysis from the initial taint; in the
loop, `fill` up to the test of whether the buffer is full from the registers
that hold our variables, the call of the compression function by its
contract (`compressAt_rel`); the epilogue from the scratch pointer. How many
bytes each iteration consumes depends only on `count` and `len`, so both
runs go through the loop the same number of times, with the same
registers. -/

section CT
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hpub : Proof.Sha512.updateArm.pub s₀ s₀')

include hpub

theorem cnt_eq : cnt s₀ = cnt s₀' := by
  obtain ⟨-, -, p2, p3, -⟩ := hpub
  simp only [cnt, countArm, p2, p3]

theorem len_eq : len s₀ = len s₀' := by
  simp only [len, hpub.2.2.2.2.2.1]

theorem nextC_eq (c : Nat) : nextC s₀' c = nextC s₀ c := by
  unfold nextC tt rr
  rw [cnt_eq hpub, len_eq hpub]

theorem Inv.agree {c : Nat} {s s' : State} (h : Inv s₀ c s) (h' : Inv s₀' c s') :
    ∀ r ∈ [Reg.r0, .r3, .r4, .r5, .r6], s.gpr r = s'.gpr r := by
  have p0 := hpub.2.1
  have a0 := hpub.2.2.2.2.1
  have a2 := hpub.2.2.2.2.2.2
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.r0, h'.r0]; exact p0
  · rw [h.r3, h'.r3]; exact a2
  · rw [h.r4, h'.r4, cnt_eq hpub]
  · rw [h.r5, h'.r5, dp, dp, a0]
  · rw [h.r6, h'.r6, len_eq hpub]

include hp hp'

theorem fill_rel {c : Nat} (hcl : c < len s₀) :
    RelCT isa (fun s₁ s₂ => Inv s₀ c s₁ ∧ Inv s₀' c s₂) fill
      fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂ := by
  have hcl' : c < len s₀' := len_eq hpub ▸ hcl
  have e0 : st s₀' = st s₀ := hpub.2.1.symm
  have e2 : scr s₀' = scr s₀ := hpub.2.2.2.2.2.2.symm
  have ez : rr s₀' c + tt s₀' c = rr s₀ c + tt s₀ c := by unfold tt rr; rw [cnt_eq hpub, len_eq hpub]
  have pre : RelCT isa (fun s₁ s₂ => Inv s₀ c s₁ ∧ Inv s₀' c s₂) fillPre fun s₁ s₂ => Mid s₀ c s₁ ∧ Mid s₀' c s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r3, .r4, .r5, .r6])
      (fun _ _ h => Taint.agree_ofRegs (Inv.agree hpub h.1 h.2)) (c := fillPre) (by taint_decide)).wp
      (F₁ := Mid s₀ c) (F₂ := Mid s₀' c) fun _ _ h => ⟨pre_ok hp h.1 hcl, pre_ok hp' h.2 hcl'⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have hat : ∀ s, Mid s₀' c s → AtPre (st s₀) (scr s₀) s := fun s h => by
    have := h.1; rwa [e0, e2] at this
  have cmp : RelCT isa (fun s₁ s₂ => (Mid s₀ c s₁ ∧ Mid s₀' c s₂) ∧ isa.eval .eq s₁ = some true)
      (.seq compressAt (.block [.mov .r4 (.imm 0)]))
      fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂ := by
    have hz : ∀ s₁ s₂, (Mid s₀ c s₁ ∧ Mid s₀' c s₂) ∧ isa.eval .eq s₁ = some true →
        isa.eval .eq s₂ = some true := fun s₁ s₂ ⟨⟨m₁, m₂⟩, h⟩ => by
      have e₁ : isa.eval .eq s₁ = some (decide (rr s₀ c + tt s₀ c = 128)) := m₁.2.1
      have e₂ : isa.eval .eq s₂ = some (decide (rr s₀ c + tt s₀ c = 128)) := by rw [← ez]; exact m₂.2.1
      rw [e₂, ← e₁, h]
    refine RelCT.seq (R := fun s₁ s₂ => WP isa (.block [.mov .r4 (.imm 0)]) s₁ (Inv s₀ (nextC s₀ c)) ∧
      WP isa (.block [.mov .r4 (.imm 0)]) s₂ (Inv s₀' (nextC s₀' c))) ?_ ?_
    · exact (((compressAt_rel hp.st_fit hp.scr_fit hp.st_scr).mono (fun _ _ h => ⟨h.1.1.1, hat _ h.1.2⟩)
        fun _ _ h => h).wp
        fun s₁ s₂ h => ⟨WP.seq_iff.mp (WP.ite_true h.1.1.2.2 h.2),
          WP.seq_iff.mp (WP.ite_true h.1.2.2.2 (hz _ _ h))⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    · refine ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
        (c := .block [.mov .r4 (.imm 0)]) (by taint_decide)).wp fun _ _ h => h).mono (fun _ _ h => h)
        fun _ _ h => ⟨h.2.1, ?_⟩
      rw [← nextC_eq hpub]; exact h.2.2
  have fend : RelCT isa (fun s₁ s₂ => Mid s₀ c s₁ ∧ Mid s₀' c s₂) fillEnd
      fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂ := by
    refine RelCT.ite (fun s₁ s₂ h => ?_) cmp (RelCT.block_nil fun s₁ s₂ ⟨⟨m₁, m₂⟩, hf⟩ => ?_)
    · have e₁ : isa.eval .eq s₁ = some (decide (rr s₀ c + tt s₀ c = 128)) := h.1.2.1
      have e₂ : isa.eval .eq s₂ = some (decide (rr s₀ c + tt s₀ c = 128)) := by rw [← ez]; exact h.2.2.1
      rw [e₁, e₂]
    · have e₁ : isa.eval .eq s₁ = some (decide (rr s₀ c + tt s₀ c = 128)) := m₁.2.1
      have e₂ : isa.eval .eq s₂ = some false := by
        have : isa.eval .eq s₂ = some (decide (rr s₀ c + tt s₀ c = 128)) := by rw [← ez]; exact m₂.2.1
        rw [this, ← e₁, hf]
      refine ⟨WP.block_nil_iff.mp (WP.ite_false m₁.2.2 hf), ?_⟩
      rw [← nextC_eq hpub]; exact WP.block_nil_iff.mp (WP.ite_false m₂.2.2 e₂)
  rw [fill_eq]
  exact RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc (pre.seq fend))))

theorem update_rel (h₀ : Proof.Sha512.updateArm.pre s₀) (h₀' : Proof.Sha512.updateArm.pre s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') update fun _ _ => True := by
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.block (([.ldrSp .r12 8] : List Instr) ++ save .r12 ++ prologue)) fun s₁ s₂ =>
      (Inv s₀ 0 s₁ ∧ s₁.z = decide (len s₀ = 0)) ∧ (Inv s₀' 0 s₂ ∧ s₂.z = decide (len s₀' = 0)) :=
    ((RelCT.taint (A := taint) τ₀ (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact agree₀ h₀ h₀' hpub)
      (c := .block (([.ldrSp .r12 8] : List Instr) ++ save .r12 ++ prologue)) (by taint_decide)).wp
      (F₁ := fun (s : State) => Inv s₀ 0 s ∧ s.z = decide (len s₀ = 0))
      (F₂ := fun (s : State) => Inv s₀' 0 s ∧ s.z = decide (len s₀' = 0))
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have lp := RelCT.loop (M := isa) (body := updateBody) (c := .ne)
    (Q := fun s₁ s₂ => Inv s₀ (len s₀) s₁ ∧ Inv s₀' (len s₀') s₂)
    (fun n s₁ s₂ => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s₁ ∧ Inv s₀' c s₂) (fun n => RelCT.exists_ fun c => by
      by_cases hcn : c < len s₀ ∧ n = len s₀ - c
      · obtain ⟨hcl, rfl⟩ := hcn
        have hn := nextC_gt s₀ hcl
        have tst : RelCT isa (fun s₁ s₂ => Inv s₀ (nextC s₀ c) s₁ ∧ Inv s₀' (nextC s₀ c) s₂)
            (.block [.cmp .r6 (.imm 0)]) fun s₁ s₂ =>
            (Inv s₀ (nextC s₀ c) s₁ ∧ s₁.z = decide (len s₀ - nextC s₀ c = 0)) ∧
            (Inv s₀' (nextC s₀ c) s₂ ∧ s₂.z = decide (len s₀' - nextC s₀ c = 0)) :=
          ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
            (c := .block [.cmp .r6 (.imm 0)]) (by taint_decide)).wp
            (F₁ := fun (s : State) => Inv s₀ (nextC s₀ c) s ∧ s.z = decide (len s₀ - nextC s₀ c = 0))
            (F₂ := fun (s : State) => Inv s₀' (nextC s₀ c) s ∧ s.z = decide (len s₀' - nextC s₀ c = 0))
            fun _ _ h => ⟨test_ok h.1, test_ok h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
        refine ((fill_rel hp hp' hpub hcl).seq tst).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun s₁ s₂ h => ?_
        obtain ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ := h
        have hc' := I₁.c_le
        have e₁ : isa.eval .ne s₁ = some (decide (len s₀ - nextC s₀ c ≠ 0)) := by
          rw [show isa.eval .ne s₁ = some !s₁.z from rfl, z₁]; simp
        have e₂ : isa.eval .ne s₂ = some (decide (len s₀ - nextC s₀ c ≠ 0)) := by
          rw [show isa.eval .ne s₂ = some !s₂.z from rfl, z₂, ← len_eq hpub]; simp
        refine ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ⟨len s₀ - nextC s₀ c, by omega, nextC s₀ c, rfl,
          ?_, I₁, I₂⟩⟩
        · have : len s₀ - nextC s₀ c = 0 := by
            rw [e₁] at hf; simpa using hf
          have e : nextC s₀ c = len s₀ := by omega
          rw [e] at I₁ I₂; rw [← len_eq hpub]; exact ⟨I₁, I₂⟩
        · rw [e₁] at ht; simp at ht; omega
      · exact RelCT.of_false fun _ _ h => hcn ⟨h.2.1, h.1⟩) (len s₀)
  have ite : RelCT isa (fun s₁ s₂ =>
        (Inv s₀ 0 s₁ ∧ s₁.z = decide (len s₀ = 0)) ∧ (Inv s₀' 0 s₂ ∧ s₂.z = decide (len s₀' = 0)))
      (.ite .eq (.block []) (.loop updateBody .ne))
      fun s₁ s₂ => Inv s₀ (len s₀) s₁ ∧ Inv s₀' (len s₀') s₂ := by
    refine RelCT.ite (fun s₁ s₂ h => ?_) (RelCT.block_nil fun s₁ s₂ ⟨⟨⟨I₁, z₁⟩, ⟨I₂, _⟩⟩, ht⟩ => ?_)
      (lp.mono (fun s₁ s₂ ⟨⟨⟨I₁, z₁⟩, ⟨I₂, _⟩⟩, hf⟩ => ⟨0, by omega, ?_, I₁, I₂⟩) fun _ _ h => h)
    · rw [show isa.eval .eq s₁ = some s₁.z from rfl, show isa.eval .eq s₂ = some s₂.z from rfl, h.1.2, h.2.2,
        len_eq hpub]
    · have : len s₀ = 0 := by
        rw [show isa.eval .eq s₁ = some s₁.z from rfl, z₁] at ht; simpa using ht
      rw [← len_eq hpub, this]; exact ⟨I₁, I₂⟩
    · rw [show isa.eval .eq s₁ = some s₁.z from rfl, z₁] at hf; simp at hf; omega
  have epi : RelCT isa (fun s₁ s₂ => Inv s₀ (len s₀) s₁ ∧ Inv s₀' (len s₀') s₂) (.block restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r3]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r3, h.2.r3]; exact hpub.2.2.2.2.2.2) (by taint_decide)
  rw [update_eq]
  exact pro.seq (ite.seq epi)

end CT

theorem update_verified : Verified Arm.target update Proof.Sha512.updateArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
    exact (update_rel (pre_of h₁) (pre_of h₂) hpub h₁ h₂ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  · have e : ∀ k, stackArg sat k = 0 := fun k => by
      simp [stackArg, sat, Mem.readW, Mem.read]
    refine ⟨sat, ?_⟩
    simp only [Proof.Sha512.updateArm, e]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.Arm.Stream.Update
