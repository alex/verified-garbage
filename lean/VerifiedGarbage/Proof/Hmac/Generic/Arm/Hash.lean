import VerifiedGarbage.Proof.Hmac.Generic.Arm.Contract
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Impl.Pbkdf2.Generic.Arm

/-!
# HMAC over any streaming hash function on 32-bit ARM: the functions we call

Untrusted: everything here is checked by Lean. As on x86-64 and AArch64
(`Proof/Hmac/Generic/AArch64/Hash.lean`): `HashOK H` is what the proofs know
of the hash function `H`: its streaming functions are verified against
`initK`, `updK` and `finK` and have no frames, the representation of its
streaming state is determined by the state's bytes, and its sizes are small.

`init` is called with `WP.callCalls`. `update` and `finalize` are called in
a frame that pushes their stack arguments (`WP.frame`), then sets the count
in `r2:r3`: `upd_frame` and `fin_frame` run such a frame, from the state
before its push. A frame writes the 16 bytes below the stack pointer, which
`After` lets change. `init_rel`, `upd_rel` and `fin_rel` relate two runs of
them (`RelCT.call`, `RelCT.frame`).
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)
open VG.Proof.MdStream.Arm (Upd WP.cons op2_imm op2_reg)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's 32-bit ARM functions, verified. `Wb` is the
scratch space their contracts use, at most the `8 W` bytes we give them. -/
structure HashOK (H : Hash) where
  SH : StreamingHash
  Wb : Nat
  hS : SH.stateBytes = H.S
  hD : SH.digestBytes = H.D
  hB : SH.H.blockSize = H.B
  hDF : H.D ≤ H.F
  hF : H.F ≤ 64
  hD0 : 0 < H.D
  hS0 : 0 < H.S
  hSB : H.S ≤ 256
  hB0 : 0 < H.B
  hBB : H.B ≤ 128
  hWb : Wb ≤ 8 * H.W
  hW : H.W ≤ 64
  /-- The representation depends only on the state's bytes. -/
  repr : ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < H.S, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p msg → SH.Repr m' q msg
  init : Verified Arm.target H.initC (initK H.S SH.Repr)
  upd : Verified Arm.target H.updC (updK H.S Wb SH.Repr)
  fin : Verified Arm.target H.finC (finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initNF : H.initC.noFrames = true
  updNF : H.updC.noFrames = true
  finNF : H.finC.noFrames = true

variable {H : Hash} (hH : HashOK H)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and the 16 bytes
below the stack pointer. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below s]) s.mem s'.mem

theorem covers_wr {ws : List Region} {s : State} (h : Covers ws s.wr) : Covers ([] ++ ws) (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n (by simpa using hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem frame_app {ws ws' : List Region} {m m' : Mem} (h : Frame ws m m') : Frame (ws ++ ws') m m' :=
  h.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-! The argument registers are not changed by the call instruction. -/

@[simp] theorem ce0 (s : State) : s.callEntry.gpr .r0 = s.gpr .r0 := State.callEntry_gpr s (by decide)
@[simp] theorem ce1 (s : State) : s.callEntry.gpr .r1 = s.gpr .r1 := State.callEntry_gpr s (by decide)
@[simp] theorem ce2 (s : State) : s.callEntry.gpr .r2 = s.gpr .r2 := State.callEntry_gpr s (by decide)
@[simp] theorem ce3 (s : State) : s.callEntry.gpr .r3 = s.gpr .r3 := State.callEntry_gpr s (by decide)

theorem wp_movw {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (Upd.setReg _ _ _))

/-! ## `init` -/

theorem init_call {s : State} {st : BitVec 32} (h0 : s.gpr .r0 = st) (hn : st.toNat + H.S ≤ 2 ^ 32)
    (hc : Covers [⟨State.addr st, H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, H.S⟩] s' → hH.SH.Repr s'.mem (State.addr st) [] → Q s') :
    WP isa (.call H.initN H.initC) s Q := by
  refine WP.callCalls (k := initK H.S hH.SH.Repr) hH.init.1 (rd := []) (wr := [⟨State.addr st, H.S⟩]) ?_
    (covers_wr hc) hc ?_ hH.initNF
  · exact ⟨rfl, by simp [h0], by simpa [h0] using hn⟩
  · intro s' h₁ h₂ h₃ h₄ h₅ _ hpost
    refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_app h₄⟩ ?_
    simpa [initK, h0] using hpost

/-! ## The frames

A frame of `n` bytes (8 or 16) stores its words below the stack pointer, in
`below s`, where the callee finds its stack arguments. -/

section Frames
variable {s : State} (h16 : 16 ≤ s.sp.toNat)
include h16

theorem addr_sub {k : Nat} (hk : k ≤ 16) :
    State.addr (s.sp - BitVec.ofNat 32 k) = State.addr s.sp - BitVec.ofNat 64 k := by
  simp only [State.addr]; bv_omega

theorem addr_off {k i : Nat} (hk : k ≤ 16) (hi : i < k) :
    State.addr (s.sp - BitVec.ofNat 32 k + BitVec.ofNat 32 i) =
      State.addr s.sp - BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
  simp only [State.addr]; bv_omega

omit h16 in
/-- The bytes `[k, k + n)` below the stack pointer are in `below s`. -/
theorem sub_below {k o n : Nat} (hk : k ≤ 16) (h : o + n ≤ k) :
    Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 k + BitVec.ofNat 64 o, n⟩ (below s) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  bv_omega

end Frames

/-- A 16-bit count in `r2:r3`. -/
theorem count_movw {t : State} {c : Nat} (hc : c < 2 ^ 16) (h2 : t.gpr .r2 = (BitVec.ofNat 16 c).setWidth 32)
    (h3 : t.gpr .r3 = 0) : count t = BitVec.ofNat 64 c := by
  simp only [count, h2, h3]
  apply BitVec.eq_of_toNat_eq
  have z : (0 : BitVec 32).toNat = 0 := rfl
  simp only [BitVec.toNat_append, BitVec.toNat_setWidth, BitVec.toNat_ofNat, z, Nat.zero_shiftLeft, Nat.zero_or]
  omega

/-! ## `update`, in its frame -/

/-- What a framed call of `update` needs of the state before its push: the
state at `st` in `r0`, the count in `r2:r3`, and `len` bytes of data at `d`
and the scratch space at `sc` in `r1`, `r7` and `r10`; the regions the
callee may read and write; that they are disjoint as it needs, and from the
16 bytes below the stack pointer; and that none of them wraps around. -/
structure UpdArgs (s : State) (st d sc : BitVec 32) (len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = d
  r7 : s.gpr .r7 = BitVec.ofNat 32 len
  r10 : s.gpr .r10 = sc
  hlen : len < 2 ^ 16
  sp16 : 16 ≤ s.sp.toNat
  cd : Covers [⟨State.addr d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨State.addr st, H.S⟩ ⟨State.addr sc, hH.Wb⟩
  d_st : Region.Disjoint ⟨State.addr d, len⟩ ⟨State.addr st, H.S⟩
  d_sc : Region.Disjoint ⟨State.addr d, len⟩ ⟨State.addr sc, hH.Wb⟩
  b_st : (below s).Disjoint ⟨State.addr st, H.S⟩
  b_d : (below s).Disjoint ⟨State.addr d, len⟩
  b_sc : (below s).Disjoint ⟨State.addr sc, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  nd : d.toNat + len ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The four words `update`'s frame pushes. -/
abbrev upd4 : List Reg := [.r1, .r7, .r10, .r12]

theorem e16 : BitVec.ofNat 32 (4 * upd4.length) = 16 := rfl

/-- The regions `update` is given: the data and its stack arguments, the state and the scratch space. -/
abbrev UpdArgs.rd (sp : BitVec 32) (d : BitVec 32) (len : Nat) : List Region :=
  [⟨State.addr d, len⟩, ⟨State.addr sp - 16, 12⟩]
abbrev UpdArgs.wr (st sc : BitVec 32) : List Region := [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩]

namespace UpdArgs
variable {hH} {s : State} {st d sc : BitVec 32} {len : Nat} (h : UpdArgs hH s st d sc len)
include h

theorem a0 : State.addr (s.sp - 16) = State.addr s.sp - 16 := by
  have := h.sp16; simp only [State.addr]; bv_omega
theorem a4 : State.addr (s.sp - 16 + 4) = State.addr s.sp - 16 + 4 := by
  have := h.sp16; simp only [State.addr]; bv_omega
theorem a8 : State.addr (s.sp - 16 + 4 + 4) = State.addr s.sp - 16 + 8 := by
  have := h.sp16; simp only [State.addr]; bv_omega
theorem a12 : State.addr (s.sp - 16 + 4 + 4 + 4) = State.addr s.sp - 16 + 12 := by
  have := h.sp16; simp only [State.addr]; bv_omega

/-- The memory after the push. -/
theorem pmem : (pushed upd4 s).mem =
    (((s.mem.writeW (State.addr s.sp - 16) d).writeW (State.addr s.sp - 16 + 4) (BitVec.ofNat 32 len)).writeW
      (State.addr s.sp - 16 + 8) sc).writeW (State.addr s.sp - 16 + 12) (s.gpr .r12) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * upd4.length)) [s.gpr .r1, s.gpr .r7, s.gpr .r10, s.gpr .r12] = _
  rw [e16]
  show (((s.mem.writeW (State.addr (s.sp - 16)) _).writeW (State.addr (s.sp - 16 + 4)) _).writeW
    (State.addr (s.sp - 16 + 4 + 4)) _).writeW (State.addr (s.sp - 16 + 4 + 4 + 4)) _ = _
  rw [h.a0, h.a4, h.a8, h.a12, h.r1, h.r7, h.r10]

omit h in
theorem psp : (pushed upd4 s).sp = s.sp - 16 := by rw [pushed_sp, e16]

/-- The stack arguments, in a state whose memory and stack pointer are those after the push. -/
theorem sa (T : State) (ht : T.sp = s.sp - 16) (i : Nat) (hi : i < 4) :
    stackArgAddr T i = State.addr s.sp - 16 + BitVec.ofNat 64 (4 * i) := by
  have := h.sp16
  simp only [stackArgAddr, ht, State.addr]
  have : 4 * i < 16 := by omega
  bv_omega

theorem sa0 (T : State) (ht : T.sp = s.sp - 16) : stackArgAddr T 0 = State.addr s.sp - 16 := by
  rw [h.sa T ht 0 (by decide)]; exact BitVec.add_zero _

theorem arg0 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed upd4 s).mem) : stackArg T 0 = d := by
  rw [stackArg, h.sa T ht 0 (by decide), hm, h.pmem, Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
    Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
    Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide), show 4 * 0 = 0 from rfl, BitVec.add_zero,
    Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed upd4 s).mem) :
    stackArg T 1 = BitVec.ofNat 32 len := by
  rw [stackArg, h.sa T ht 1 (by decide), hm, h.pmem, Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
    Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide), show BitVec.ofNat 64 (4 * 1) = 4 from rfl,
    Mem.readW_writeW_self32]

theorem arg2 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed upd4 s).mem) : stackArg T 2 = sc := by
  rw [stackArg, h.sa T ht 2 (by decide), hm, h.pmem, Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
    show BitVec.ofNat 64 (4 * 2) = 8 from rfl, Mem.readW_writeW_self32]

/-- The push writes only below the stack pointer. -/
theorem fP : Frame [below s] s.mem (pushed upd4 s).mem := by
  rw [h.pmem]
  have hc : ∀ k, k + 4 ≤ 16 → (below s).Contains (State.addr s.sp - 16 + BitVec.ofNat 64 k) (32 / 8) := by
    intro k hk; simp only [Region.Contains]; bv_omega
  refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
    (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using hc 0 (by decide)
  · exact hc 4 (by decide)
  · exact hc 8 (by decide)
  · exact hc 12 (by decide)

omit h in
theorem vsp : ((pushed upd4 s).callEntry.withRegions (rd s.sp d len) (wr hH st sc)).sp = s.sp - 16 := psp
omit h in
theorem vmem : ((pushed upd4 s).callEntry.withRegions (rd s.sp d len) (wr hH st sc)).mem = (pushed upd4 s).mem := rfl

theorem hlen' : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; have := h.hlen; omega

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 16, 12⟩ (below s) := by
  intro x hx; simp only [Region.Contains] at hx ⊢; omega

theorem pre : (updK H.S hH.Wb hH.SH.Repr).pre ((pushed upd4 s).callEntry.withRegions (rd s.sp d len) (wr hH st sc)) := by
  simp only [updK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0, pushed_gpr,
    h.arg0 _ vsp vmem, h.arg1 _ vsp vmem, h.arg2 _ vsp vmem, h.sa0 _ vsp, h.r0, h.hlen']
  refine ⟨trivial, trivial, h.st_sc, h.d_st, h.d_sc, (h.b_st.sub_left argsSub), (h.b_sc.sub_left argsSub),
    h.nst, h.nd, h.nsc, ?_⟩
  rw [vsp]; have := h.sp16; bv_omega

theorem cov : Covers (rd s.sp d len ++ wr hH st sc) ((pushed upd4 s).rd ++ (pushed upd4 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, e16]
  rcases hr with (rfl | rfl) | (rfl | rfl)
  · obtain ⟨r', hr', hc'⟩ := h.cd x n' ⟨_, List.mem_singleton_self _, hcn⟩
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact ⟨r', List.mem_append_left _ hr', hc'⟩
    · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a0]; simp only [Region.Contains, upd4, List.length_cons, List.length_nil] at hcn ⊢; omega
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (wr hH st sc) (pushed upd4 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end UpdArgs

/-- After a frame of `rs` of `n` bytes around a call that keeps the regions
and the stack pointer. -/
theorem after_frame {s s₂ : State} {rs : List Reg} {ws : List Region}
    (fP : Frame [below s] s.mem (pushed rs s).mem)
    (hrd : s₂.rd = (pushed rs s).rd) (hwr : s₂.wr = (pushed rs s).wr) (hsp : s₂.sp = (pushed rs s).sp)
    (hf : Frame ws (pushed rs s).mem s₂.mem) (hcs : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = (pushed rs s).gpr r) :
    After s ws (popped .r1 (4 * rs.length) s₂) := by
  refine ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have hr1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr1, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    exact (frame_app (ws' := ws) fP |>.mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢; tauto).trans (frame_app (ws' := [below s]) hf)

theorem upd_frame {s : State} {st d sc : BitVec 32} {len : Nat} (h : UpdArgs hH s st d sc len)
    {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → count s = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (State.addr st) (m ++ bytesAt s.mem (State.addr d) len)) → Q s') :
    WP isa (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := upd4) (r := .r1) rfl (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.callCalls (k := updK H.S hH.Wb hH.SH.Repr) hH.upd.1 h.pre h.cov h.covW ?_ hH.updNF
  intro s₂ hrd hwr hsp hf hcs _ hpost
  have vc : count ((pushed upd4 s).callEntry.withRegions (UpdArgs.rd s.sp d len) (UpdArgs.wr hH st sc)) = count s := by
    simp only [count, State.withRegions_gpr, ce2, ce3, pushed_gpr]
  simp only [updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, pushed_gpr, h.r0,
    h.arg0 _ UpdArgs.vsp UpdArgs.vmem, h.arg1 _ UpdArgs.vsp UpdArgs.vmem, h.hlen', vc] at hpost
  refine hQ _ (after_frame h.fP hrd hwr hsp hf hcs) fun m hr hcm => ?_
  have hs : ∀ r ∈ [below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed upd4 s).mem (State.addr st) m :=
    hH.repr _ _ _ _ _ (fun i hi => h.fP.bytes (R := ⟨State.addr st, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr
  have hd : bytesAt (pushed upd4 s).mem (State.addr d) len = bytesAt s.mem (State.addr d) len := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    exact h.fP.bytes (R := ⟨State.addr d, len⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.b_d.symm) (by show len ≤ 2 ^ 64; have := h.hlen; omega)
      (List.mem_range.mp hi)
  rw [popped_mem, ← hd]
  exact hpost m hr' hcm

/-! ## `finalize`, in its frame -/

/-- What a framed call of `finalize` needs of the state before its push:
the state at `st` in `r0`, the count in `r2:r3`, and `out` at `o` and the
scratch space at `sc` in `r1` and `r12`, as for `update`. -/
structure FinArgs (s : State) (st o sc : BitVec 32) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = o
  r12 : s.gpr .r12 = sc
  sp16 : 16 ≤ s.sp.toNat
  cw : Covers [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨State.addr st, H.S⟩ ⟨State.addr o, H.F⟩
  st_sc : Region.Disjoint ⟨State.addr st, H.S⟩ ⟨State.addr sc, hH.Wb⟩
  o_sc : Region.Disjoint ⟨State.addr o, H.F⟩ ⟨State.addr sc, hH.Wb⟩
  b_st : (below s).Disjoint ⟨State.addr st, H.S⟩
  b_o : (below s).Disjoint ⟨State.addr o, H.F⟩
  b_sc : (below s).Disjoint ⟨State.addr sc, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  no : o.toNat + H.F ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The two words `finalize`'s frame pushes. -/
abbrev fin2 : List Reg := [.r1, .r12]

theorem e8 : BitVec.ofNat 32 (4 * fin2.length) = 8 := rfl

/-- The regions `finalize` is given: its stack arguments, the state, `out` and the scratch space. -/
abbrev FinArgs.rd (sp : BitVec 32) : List Region := [⟨State.addr sp - 8, 8⟩]
abbrev FinArgs.wr (st o sc : BitVec 32) : List Region :=
  [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩]

namespace FinArgs
variable {hH} {s : State} {st o sc : BitVec 32} (h : FinArgs hH s st o sc)
include h

theorem a8 : State.addr (s.sp - 8) = State.addr s.sp - 8 := by
  have := h.sp16; simp only [State.addr]; bv_omega
theorem a4 : State.addr (s.sp - 8 + 4) = State.addr s.sp - 8 + 4 := by
  have := h.sp16; simp only [State.addr]; bv_omega

theorem pmem : (pushed fin2 s).mem =
    (s.mem.writeW (State.addr s.sp - 8) o).writeW (State.addr s.sp - 8 + 4) sc := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * fin2.length)) [s.gpr .r1, s.gpr .r12] = _
  rw [e8]
  show (s.mem.writeW (State.addr (s.sp - 8)) _).writeW (State.addr (s.sp - 8 + 4)) _ = _
  rw [h.a8, h.a4, h.r1, h.r12]

omit h in
theorem psp : (pushed fin2 s).sp = s.sp - 8 := by rw [pushed_sp, e8]

theorem sa0 (T : State) (ht : T.sp = s.sp - 8) : stackArgAddr T 0 = State.addr s.sp - 8 := by
  have := h.sp16; simp only [stackArgAddr, ht, State.addr]; bv_omega

theorem sa1 (T : State) (ht : T.sp = s.sp - 8) : stackArgAddr T 1 = State.addr s.sp - 8 + 4 := by
  have := h.sp16; simp only [stackArgAddr, ht, State.addr]; bv_omega

theorem arg0 (T : State) (ht : T.sp = s.sp - 8) (hm : T.mem = (pushed fin2 s).mem) : stackArg T 0 = o := by
  rw [stackArg, h.sa0 T ht, hm, h.pmem, Mem.readW_writeW_sep (fun x h₁ h₂ => by bv_omega) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 8) (hm : T.mem = (pushed fin2 s).mem) : stackArg T 1 = sc := by
  rw [stackArg, h.sa1 T ht, hm, h.pmem, Mem.readW_writeW_self32]

theorem fP : Frame [below s] s.mem (pushed fin2 s).mem := by
  rw [h.pmem]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains]; bv_omega
  · simp only [Region.Contains]; bv_omega

omit h in
theorem vsp : ((pushed fin2 s).callEntry.withRegions (rd s.sp) (wr hH st o sc)).sp = s.sp - 8 := psp
omit h in
theorem vmem : ((pushed fin2 s).callEntry.withRegions (rd s.sp) (wr hH st o sc)).mem = (pushed fin2 s).mem := rfl

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 8, 8⟩ (below s) := by
  intro x hx; simp only [Region.Contains] at hx ⊢; bv_omega

theorem pre : (finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash).pre
    ((pushed fin2 s).callEntry.withRegions (rd s.sp) (wr hH st o sc)) := by
  simp only [finK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0, pushed_gpr,
    h.arg0 _ vsp vmem, h.arg1 _ vsp vmem, h.sa0 _ vsp, h.r0]
  refine ⟨trivial, trivial, h.st_o, h.st_sc, h.o_sc, (h.b_st.sub_left argsSub), (h.b_o.sub_left argsSub),
    (h.b_sc.sub_left argsSub), h.nst, h.no, h.nsc, ?_⟩
  rw [vsp]; have := h.sp16; bv_omega

theorem cov : Covers (rd s.sp ++ wr hH st o sc) ((pushed fin2 s).rd ++ (pushed fin2 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, e8]
  rcases hr with rfl | (rfl | rfl | rfl)
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a8]; simp only [Region.Contains, fin2, List.length_cons, List.length_nil] at hcn ⊢; omega
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (wr hH st o sc) (pushed fin2 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end FinArgs

theorem fin_frame {s : State} {st o sc : BitVec 32} (h : FinArgs hH s st o sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → m.length < 2 ^ 64 → count s = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (State.addr o) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := fin2) (r := .r1) rfl (by show 8 ≤ s.sp.toNat; omega) (by decide) ?_
  refine WP.callCalls (k := finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 h.pre h.cov h.covW ?_ hH.finNF
  intro s₂ hrd hwr hsp hf hcs _ hpost
  have vc : count ((pushed fin2 s).callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)) = count s := by
    simp only [count, State.withRegions_gpr, ce2, ce3, pushed_gpr]
  simp only [finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, pushed_gpr, h.r0,
    h.arg0 _ FinArgs.vsp FinArgs.vmem, vc] at hpost
  refine hQ _ (after_frame h.fP hrd hwr hsp hf hcs) fun m hr hl hcm => ?_
  have hs : ∀ r ∈ [below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed fin2 s).mem (State.addr st) m :=
    hH.repr _ _ _ _ _ (fun i hi => h.fP.bytes (R := ⟨State.addr st, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr
  rw [popped_mem]
  exact hpost m hr' hl hcm

/-! ## The calls in two runs

A call is constant time when the callee's precondition holds in both runs
and its public arguments agree (`RelCT.call`); a frame around it, when the
stack pointer is the same in both (`RelCT.frame`). -/

theorem push_eq {rs : List Reg} {s a : State} (hrs : regList rs = true) (h : isa.push (.push rs) s = some a) :
    a = pushed rs s := by
  rw [push_pushed hrs (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

include hH in
theorem init_rel {P : State → State → Prop} {st : BitVec 32}
    (h : ∀ s s', P s s' → s.gpr .r0 = st ∧ s'.gpr .r0 = st ∧ st.toNat + H.S ≤ 2 ^ 32 ∧
      Covers [⟨State.addr st, H.S⟩] s.wr ∧ Covers [⟨State.addr st, H.S⟩] s'.wr) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  refine RelCT.call hH.init.1 hH.init.2.1 [] [⟨State.addr st, H.S⟩] fun s s' hp => ?_
  obtain ⟨d, d', hn, c, c'⟩ := h s s' hp
  refine ⟨⟨rfl, by simp [d], by simpa [d] using hn⟩, ⟨rfl, by simp [d'], by simpa [d'] using hn⟩, ?_,
    covers_wr c, c, covers_wr c', c'⟩
  simp only [initK, State.withRegions_gpr, ce0, d, d']

theorem upd_rel {P : State → State → Prop} {sp : BitVec 32} {st d sc : BitVec 32} {len : Nat}
    (h : ∀ s s', P s s' → UpdArgs hH s st d sc len ∧ UpdArgs hH s' st d sc len ∧ count s = count s' ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hH.upd.1 hH.upd.2.1 (UpdArgs.rd sp d len) (UpdArgs.wr hH st sc)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨u, u', hc, e, e'⟩ := h s s' hp
  rw [push_eq rfl pa, push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : UpdArgs.rd s.sp d len = UpdArgs.rd s'.sp d len := by rw [v]
  have t1 : ((pushed upd4 s).callEntry.withRegions (UpdArgs.rd s.sp d len) (UpdArgs.wr hH st sc)).sp =
    s.sp - 16 := UpdArgs.psp
  have t2 : ((pushed upd4 s').callEntry.withRegions (UpdArgs.rd s.sp d len) (UpdArgs.wr hH st sc)).sp =
    s'.sp - 16 := UpdArgs.psp
  refine ⟨u.pre, hv' ▸ u'.pre, ?_, u.cov, u.covW, hv' ▸ u'.cov, u'.covW⟩
  obtain ⟨c3, c2⟩ := BitVec.append_32_inj hc
  simp only [updK]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, ce0, pushed_gpr, u.r0, u'.r0]
  · simp only [State.withRegions_gpr, ce2, pushed_gpr, c2]
  · simp only [State.withRegions_gpr, ce3, pushed_gpr, c3]
  · rw [u.arg0 _ t1 rfl, u'.arg0 _ t2 rfl]
  · rw [u.arg1 _ t1 rfl, u'.arg1 _ t2 rfl]
  · rw [u.arg2 _ t1 rfl, u'.arg2 _ t2 rfl]

theorem fin_rel {P : State → State → Prop} {sp : BitVec 32} {st o sc : BitVec 32}
    (h : ∀ s s', P s s' → FinArgs hH s st o sc ∧ FinArgs hH s' st o sc ∧ count s = count s' ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hH.fin.1 hH.fin.2.1 (FinArgs.rd sp) (FinArgs.wr hH st o sc)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨f, f', hc, e, e'⟩ := h s s' hp
  rw [push_eq rfl pa, push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : FinArgs.rd s.sp = FinArgs.rd s'.sp := by rw [v]
  have t1 : ((pushed fin2 s).callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)).sp =
    s.sp - 8 := FinArgs.psp
  have t2 : ((pushed fin2 s').callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)).sp =
    s'.sp - 8 := FinArgs.psp
  refine ⟨f.pre, hv' ▸ f'.pre, ?_, f.cov, f.covW, hv' ▸ f'.cov, f'.covW⟩
  obtain ⟨c3, c2⟩ := BitVec.append_32_inj hc
  simp only [finK]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, ce0, pushed_gpr, f.r0, f'.r0]
  · simp only [State.withRegions_gpr, ce2, pushed_gpr, c2]
  · simp only [State.withRegions_gpr, ce3, pushed_gpr, c3]
  · rw [f.arg0 _ t1 rfl, f'.arg0 _ t2 rfl]
  · rw [f.arg1 _ t1 rfl, f'.arg1 _ t2 rfl]

/-- Code the taint analysis checks from the registers `rs`, in two runs
whose single-run facts `F` and `F'` agree on them. -/
theorem rel_taint {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2)) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The taint in which the registers `rs` and the first `n` bytes of stack
arguments are public. -/
def argTaint (rs : List Reg) (n : Nat) : VG.Arm.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, argLen := n }

/-- The first `4 j` bytes of stack arguments agree when their first `j` words do. -/
theorem argMem_of {s₁ s₂ : State} {j : Nat} (hsp : s₁.sp = s₂.sp) (hf : s₁.sp.toNat + 4 * j ≤ 2 ^ 32)
    (h : ∀ i < j, stackArg s₁ i = stackArg s₂ i) :
    ∀ k < 4 * j, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  intro k hk
  have e : ∀ s : State, s.sp.toNat + 4 * j ≤ 2 ^ 32 →
      VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := fun s hs => by
    simp only [VG.Arm.Taint.argByte, stackArgAddr]
    rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [e s₁ hf, e s₂ (hsp ▸ hf), Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
    Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (h _ (by omega))

theorem agree_argTaint {rs : List Reg} {n : Nat} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : s₁.sp = s₂.sp)
    (hw₁ : s₁.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₁.wr, Region.Disjoint ⟨State.addr s₁.sp, n⟩ r)
    (hw₂ : s₂.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₂.wr, Region.Disjoint ⟨State.addr s₂.sp, n⟩ r)
    (hm : ∀ k < n, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k)) :
    VG.Arm.Taint.Agree (argTaint rs n) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₁,
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₂,
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp _ := hsp
  argMem := hm

/-- Code the taint analysis checks from `τ`, in two runs whose single-run
facts `F` and `F'` make them agree on it. -/
theorem rel_agree {F F' G G' : State → Prop} {c : Prog isa} (τ : VG.Arm.Taint.T)
    (hag : ∀ s s', F s → F' s' → VG.Arm.Taint.Agree τ s s')
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) τ (fun s s' h => hag s s' h.1 h.2) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Hmac.Generic.Arm
