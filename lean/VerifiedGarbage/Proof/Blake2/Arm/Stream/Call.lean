import VerifiedGarbage.Proof.Blake2.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Impl.Blake2.Arm.Stream

/-!
# Streaming BLAKE2 on ARMv7: the calls of the compression function

The streaming functions call any compression function verified against
`compressArm P` that makes no calls (`CalleeOk`), in a frame that pushes its
stack arguments (`t` in `r3:r11`, `last` in `r12`, `scratch` in `lr`).
`call_ok` runs such a frame from the state before its push (`WP.frame`,
`WP.call`), and `call_rel` relates two runs of it (`RelCT.frame`,
`RelCT.call`), as for HMAC's calls of `update`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`). The frame writes the 16 bytes below the
stack pointer (`below`), which `After` lets change.
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call)

/-- The 16 bytes below the stack pointer. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 16, 16⟩

/-- What the streaming functions need of the compression function they call:
that it is verified against `compressArm P` and makes no calls. -/
structure CalleeOk {w : Nat} (P : Params w) (code : Prog isa) : Prop where
  verified : Verified Arm.target code (compressArm P)
  noCalls : code.noCalls = true

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and the 16 bytes
below the stack pointer. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below s]) s.mem s'.mem

theorem frame_app {ws ws' : List Region} {m m' : Mem} (h : Frame ws m m') : Frame (ws ++ ws') m m' :=
  h.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-! The argument registers are not changed by the call instruction. -/

@[simp] theorem ce0 (s : State) : s.callEntry.gpr .r0 = s.gpr .r0 := State.callEntry_gpr s (by decide)
@[simp] theorem ce1 (s : State) : s.callEntry.gpr .r1 = s.gpr .r1 := State.callEntry_gpr s (by decide)
@[simp] theorem ce2 (s : State) : s.callEntry.gpr .r2 = s.gpr .r2 := State.callEntry_gpr s (by decide)

/-- `x - k + i` (for `i ≤ k ≤ x`) widened to 64 bits. -/
theorem addr_sub_add {x : BitVec 32} {k i : Nat} (hk : k ≤ x.toNat) (hi : i ≤ k) :
    State.addr (x - BitVec.ofNat 32 k + BitVec.ofNat 32 i) =
      State.addr x - BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega_nat), Nat.mod_eq_of_lt (a := i) (by omega_nat),
    Nat.mod_eq_of_lt (a := k) (by omega_nat), Nat.mod_eq_of_lt (a := i) (by omega_nat),
    Nat.mod_eq_of_lt (a := x.toNat) (by omega_nat),
    show 2 ^ 32 - k + x.toNat = 2 ^ 32 + (x.toNat - k) by omega_nat, Nat.add_mod_left,
    show 2 ^ 64 - k + x.toNat = 2 ^ 64 + (x.toNat - k) by omega_nat, Nat.add_mod_left]
  omega_nat

/-- `x - k` (for `k ≤ x`) widened to 64 bits. -/
theorem addr_sub {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) :
    State.addr (x - BitVec.ofNat 32 k) = State.addr x - BitVec.ofNat 64 k := by
  have := addr_sub_add (i := 0) hk (Nat.zero_le _)
  simpa using this

/-- Bytes at two offsets from a base that do not overlap. -/
theorem sep_off (b : Addr) {d e n k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n < 2 ^ 32)
    (he : e + k < 2 ^ 32) : Mem.Sep (b + BitVec.ofNat 64 d) n (b + BitVec.ofNat 64 e) k :=
  Offset.sep b h (by omega_nat) (by omega_nat)

/-- Bytes at an offset from a region's base, in it. -/
theorem contains_off (b : Addr) {len d n : Nat} (h : d + n ≤ len) (hl : len < 2 ^ 64) :
    Region.Contains ⟨b, len⟩ (b + BitVec.ofNat 64 d) n := Offset.contains_base b h (by omega_nat)

section
variable {w : Nat}

/-- What a call needs of the state before its push: the hash value at `st`
in `r0`, the `n` blocks at `blk` in `r1` and `r2`, the counter `t` in
`r11:r3` (low word in `r3`), `last` in `r12` and the scratch space at `scr` in
`lr`; the regions the callee may read and write, disjoint as it needs, and
from the 16 bytes below the stack pointer; and that none of them wraps
around. -/
structure CallArgs (s : State) (st scr blk : BitVec 32) (n : Nat) (t : BitVec 64) (last : BitVec 32) :
    Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = blk
  r2 : s.gpr .r2 = BitVec.ofNat 32 n
  t : s.gpr .r11 ++ s.gpr .r3 = t
  r12 : s.gpr .r12 = last
  lr : s.gpr .lr = scr
  hn : n < 2 ^ 32
  sp16 : 16 ≤ s.sp.toNat
  cb : Covers [⟨State.addr blk, blockBytes w * n⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr st, bufOff w⟩, ⟨State.addr scr, 512⟩] s.wr
  st_sc : Region.Disjoint ⟨State.addr st, bufOff w⟩ ⟨State.addr scr, 512⟩
  b_st : Region.Disjoint ⟨State.addr blk, blockBytes w * n⟩ ⟨State.addr st, bufOff w⟩
  b_sc : Region.Disjoint ⟨State.addr blk, blockBytes w * n⟩ ⟨State.addr scr, 512⟩
  w_st : (below s).Disjoint ⟨State.addr st, bufOff w⟩
  w_b : (below s).Disjoint ⟨State.addr blk, blockBytes w * n⟩
  w_sc : (below s).Disjoint ⟨State.addr scr, 512⟩
  nst : st.toNat + bufOff w ≤ 2 ^ 32
  nb : blk.toNat + blockBytes w * n ≤ 2 ^ 32
  nsc : scr.toNat + 512 ≤ 2 ^ 32

/-- The four words the frame pushes. -/
abbrev args4 : List Reg := [.r3, .r11, .r12, .lr]

theorem e16 : BitVec.ofNat 32 (4 * args4.length) = 16 := rfl

/-- The regions the callee is given: the blocks and its stack arguments, the
state and the scratch space. -/
abbrev CallArgs.rd (w : Nat) (sp blk : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr blk, blockBytes w * n⟩, ⟨State.addr sp - 16, 16⟩]
abbrev CallArgs.wr (w : Nat) (st scr : BitVec 32) : List Region :=
  [⟨State.addr st, bufOff w⟩, ⟨State.addr scr, 512⟩]

variable {P : Params w}

namespace CallArgs
variable {s : State} {st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
  (h : CallArgs (w := w) s st scr blk n t last)
include h

theorem a0 : State.addr (s.sp - 16) = State.addr s.sp - 16 := addr_sub h.sp16
theorem a4 : State.addr (s.sp - 16 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 4 :=
  addr_sub_add h.sp16 (by decide)
theorem a8 : State.addr (s.sp - 16 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 8 := by
  rw [BitVec.add_assoc]; exact addr_sub_add (k := 16) (i := 8) h.sp16 (by decide)
theorem a12 : State.addr (s.sp - 16 + 4 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 12 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; exact addr_sub_add (k := 16) (i := 12) h.sp16 (by decide)

/-- The memory after the push. -/
theorem pmem : (pushed args4 s).mem =
    (((s.mem.writeW (State.addr s.sp - 16) (s.gpr .r3)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 4)
      (s.gpr .r11)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 8) last).writeW
      (State.addr s.sp - 16 + BitVec.ofNat 64 12) scr := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * args4.length))
    [s.gpr .r3, s.gpr .r11, s.gpr .r12, s.gpr .lr] = _
  rw [e16]
  show (((s.mem.writeW (State.addr (s.sp - 16)) _).writeW (State.addr (s.sp - 16 + 4)) _).writeW
    (State.addr (s.sp - 16 + 4 + 4)) _).writeW (State.addr (s.sp - 16 + 4 + 4 + 4)) _ = _
  rw [h.a0, h.a4, h.a8, h.a12, h.r12, h.lr]

omit h in
theorem psp : (pushed args4 s).sp = s.sp - 16 := by rw [pushed_sp, e16]

/-- The stack arguments, in a state whose stack pointer is that after the push. -/
theorem sa (T : State) (ht : T.sp = s.sp - 16) (i : Nat) (hi : i < 4) :
    stackArgAddr T i = State.addr s.sp - 16 + BitVec.ofNat 64 (4 * i) := by
  simp only [stackArgAddr, ht]
  exact addr_sub_add (k := 16) h.sp16 (by omega_nat)

theorem sa0 (T : State) (ht : T.sp = s.sp - 16) : stackArgAddr T 0 = State.addr s.sp - 16 := by
  rw [h.sa T ht 0 (by decide)]; exact BitVec.add_zero _

theorem arg0 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 0 = s.gpr .r3 := by
  rw [stackArg, h.sa T ht 0 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 0 = 0 from rfl, BitVec.add_zero, Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 1 = s.gpr .r11 := by
  rw [stackArg, h.sa T ht 1 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 1 = 4 from rfl, Mem.readW_writeW_self32]

theorem arg2 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 2 = last := by
  rw [stackArg, h.sa T ht 2 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 2 = 8 from rfl, Mem.readW_writeW_self32]

theorem arg3 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 3 = scr := by
  rw [stackArg, h.sa T ht 3 (by decide), hm, h.pmem, show 4 * 3 = 12 from rfl, Mem.readW_writeW_self32]

/-- The push writes only below the stack pointer. -/
theorem fP : Frame [below s] s.mem (pushed args4 s).mem := by
  rw [h.pmem]
  have hc : ∀ k, k + 4 ≤ 16 → (below s).Contains (State.addr s.sp - 16 + BitVec.ofNat 64 k) (32 / 8) := by
    intro k hk; exact contains_off _ (by omega_nat) (by decide)
  refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
    ?_).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using hc 0 (by decide)
  · exact hc 4 (by decide)
  · exact hc 8 (by decide)
  · exact hc 12 (by decide)

omit h in
theorem vsp : ((pushed args4 s).callEntry.withRegions (rd w s.sp blk n) (wr w st scr)).sp = s.sp - 16 :=
  psp
omit h in
theorem vmem : ((pushed args4 s).callEntry.withRegions (rd w s.sp blk n) (wr w st scr)).mem =
    (pushed args4 s).mem := rfl

theorem hn' : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h.hn

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 16, 16⟩ (below s) := fun _ h => h

theorem pre : (compressArm P).pre ((pushed args4 s).callEntry.withRegions (rd w s.sp blk n) (wr w st scr)) := by
  simp only [compressArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0, ce1, ce2,
    pushed_gpr, h.arg3 _ vsp vmem, h.sa0 _ vsp, h.r0, h.r1, h.r2, h.hn']
  refine ⟨trivial, trivial, h.st_sc, h.b_st, h.b_sc, h.w_st, h.w_sc, h.nst, h.nb, h.nsc, ?_⟩
  rw [vsp, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.toNat_sub_ofNat]
  have := h.sp16; have := s.sp.isLt; omega_nat

theorem cov : Covers (rd w s.sp blk n ++ wr w st scr) ((pushed args4 s).rd ++ (pushed args4 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, e16]
  rcases hr with (rfl | rfl) | (rfl | rfl)
  · obtain ⟨r', hr', hc'⟩ := h.cb x n' ⟨_, List.mem_singleton_self _, hcn⟩
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact ⟨r', List.mem_append_left _ hr', hc'⟩
    · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a0]; exact hcn
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (wr w st scr) (pushed args4 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end CallArgs

/-- After a frame of `rs` around a call that keeps the regions and the stack
pointer. -/
theorem after_frame {s s₂ : State} {rs : List Reg} {ws : List Region}
    (fP : Frame [below s] s.mem (pushed rs s).mem)
    (hrd : s₂.rd = (pushed rs s).rd) (hwr : s₂.wr = (pushed rs s).wr) (hsp : s₂.sp = (pushed rs s).sp)
    (hf : Frame ws (pushed rs s).mem s₂.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = (pushed rs s).gpr r) :
    After s ws (popped .r3 (4 * rs.length) s₂) := by
  refine ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr3, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    exact (frame_app (ws' := ws) fP |>.mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢; grind).trans (frame_app (ws' := [below s]) hf)

variable {P : Params w}

/-- A call of the compression function, in its frame: the hash value at `st`
is updated with the `n` blocks at `blk`, the first with the counter `t`, as
the last ones if `last ≠ 0`. -/
theorem call_ok {name : String} {code : Prog isa} (hf : CalleeOk P code) {s : State}
    {st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (h : CallArgs (w := w) s st scr blk n t last) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, bufOff w⟩, ⟨State.addr scr, 512⟩] s' →
      stateAt w s'.mem (State.addr st) =
        compressBlocks P (stateAt w s.mem (State.addr st)) s.mem (State.addr blk) n t.toNat
          (last != 0) → Q s') :
    WP isa (call name code) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := args4) (r := .r3) rfl (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.call (k := compressArm P) hf.verified.1 h.pre h.cov h.covW ?_ hf.noCalls
  intro s₂ hrd hwr hsp hfr hcs _ hpost
  simp only [compressArm, tArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1,
    ce2, pushed_gpr, h.r0, h.r1, h.r2, h.hn', h.arg0 _ CallArgs.vsp CallArgs.vmem,
    h.arg1 _ CallArgs.vsp CallArgs.vmem, h.arg2 _ CallArgs.vsp CallArgs.vmem, h.t] at hpost
  refine hQ _ (after_frame h.fP hrd hwr hsp hfr hcs) ?_
  have hst : stateAt w (pushed args4 s).mem (State.addr st) = stateAt w s.mem (State.addr st) :=
    stateAt_congr fun i hi => h.fP.bytes (R := ⟨State.addr st, bufOff w⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.w_st.symm)
      (by show bufOff w ≤ 2 ^ 64; have := h.nst; omega_nat) hi
  have hbl : compressBlocks P (stateAt w s.mem (State.addr st)) (pushed args4 s).mem (State.addr blk) n
      t.toNat (last != 0) =
      compressBlocks P (stateAt w s.mem (State.addr st)) s.mem (State.addr blk) n t.toNat
        (last != 0) :=
    compressBlocks_congr P fun j hj => h.fP.bytes (R := ⟨State.addr blk, blockBytes w * n⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.w_b.symm)
      (by show blockBytes w * n ≤ 2 ^ 64; have := h.nb; omega_nat) hj
  rw [popped_mem, hpost, hst, hbl]

end

end VG.Proof.Blake2.Arm.Stream
