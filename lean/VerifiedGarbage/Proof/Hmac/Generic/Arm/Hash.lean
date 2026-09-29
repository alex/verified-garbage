import VerifiedGarbage.Proof.Hmac.Generic.Arm.Contract
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
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
open VG.Proof.Sha256.Arm.Stream (Upd WP.cons op2_imm op2_reg)
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
state at `st`, `len` bytes of data at `d` and the scratch space at `sc`, in
`r0`–`r3`; the regions the callee may read and write; that they are
disjoint as it needs, and from the 16 bytes below the stack pointer; and
that none of them wraps around. -/
structure UpdArgs (s : State) (st d sc : BitVec 32) (len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = d
  r2 : s.gpr .r2 = BitVec.ofNat 32 len
  r3 : s.gpr .r3 = sc
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
abbrev upd4 : List Reg := [.r1, .r2, .r3, .r12]

theorem e16 : BitVec.ofNat 32 (4 * upd4.length) = 16 := rfl

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
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * upd4.length)) [s.gpr .r1, s.gpr .r2, s.gpr .r3, s.gpr .r12] = _
  rw [e16]
  show (((s.mem.writeW (State.addr (s.sp - 16)) _).writeW (State.addr (s.sp - 16 + 4)) _).writeW
    (State.addr (s.sp - 16 + 4 + 4)) _).writeW (State.addr (s.sp - 16 + 4 + 4 + 4)) _ = _
  rw [h.a0, h.a4, h.a8, h.a12, h.r1, h.r2, h.r3]

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

end UpdArgs

theorem upd_frame {s : State} {st d sc : BitVec 32} {len c : Nat} (h : UpdArgs hH s st d sc len)
    (hc : c < 2 ^ 16) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → BitVec.ofNat 64 c = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (State.addr st) (m ++ bytesAt s.mem (State.addr d) len)) → Q s') :
    WP isa (.frame (.push upd4)
      (.seq (.block [.movw .r2 (BitVec.ofNat 16 c), .mov .r3 (.imm 0)]) (.call H.updN H.updC))
      (.pop .r1 16)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := upd4) (r := .r1) rfl (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.seq (wp_movw fun t₁ u₁ => VG.Proof.Sha256.Arm.Stream.wp_mov (op2_imm (by decide)) fun t₂ u₂ =>
    WP.block_nil ?_)
  have tsp : t₂.sp = s.sp - 16 := by rw [u₂.sp, u₁.sp, UpdArgs.psp]
  have tmem : t₂.mem = (pushed upd4 s).mem := by rw [u₂.mem, u₁.mem]
  have t0 : t₂.gpr .r0 = st := by rw [u₂.other _ (by decide), u₁.other _ (by decide), pushed_gpr, h.r0]
  have tc : count t₂ = BitVec.ofNat 64 c := count_movw hc (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr
  let rd : List Region := [⟨State.addr d, len⟩, ⟨State.addr s.sp - 16, 12⟩]
  let wr : List Region := [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩]
  have vsp : (t₂.callEntry.withRegions rd wr).sp = s.sp - 16 := tsp
  have vmem : (t₂.callEntry.withRegions rd wr).mem = (pushed upd4 s).mem := tmem
  have hlen : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; have := h.hlen; omega
  have argsSub : Region.Sub ⟨State.addr s.sp - 16, 12⟩ (below s) := by
    intro x hx; simp only [Region.Contains] at hx ⊢; omega
  refine WP.callCalls (k := updK H.S hH.Wb hH.SH.Repr) hH.upd.1 (rd := rd) (wr := wr) ?_ ?_ ?_ ?_ hH.updNF
  · simp only [updK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0,
      h.arg0 _ vsp vmem, h.arg1 _ vsp vmem, h.arg2 _ vsp vmem, h.sa0 _ vsp, t0, hlen, rd, wr]
    refine ⟨trivial, trivial, h.st_sc, h.d_st, h.d_sc, (h.b_st.sub_left argsSub), (h.b_sc.sub_left argsSub),
      h.nst, h.nd, h.nsc, ?_⟩
    rw [vsp]; bv_omega
  · intro x n' ⟨r, hr, hcn⟩
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, rd, wr] at hr
    rw [u₂.rd, u₁.rd, u₂.wr, u₁.wr, pushed_rd, pushed_wr, e16]
    rcases hr with (rfl | rfl) | (rfl | rfl)
    · obtain ⟨r', hr', hc'⟩ := h.cd x n' ⟨_, List.mem_singleton_self _, hcn⟩
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact ⟨r', List.mem_append_left _ hr', hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
    · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      rw [h.a0]; simp only [Region.Contains, upd4, List.length_cons, List.length_nil] at hcn ⊢; omega
    · obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
    · obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · intro x n' hi
    obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
    exact ⟨r', by rw [u₂.wr, u₁.wr, pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · intro s₂ hrd hwr hsp hf hcs _ hpost
    refine hQ _ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ fun m hr hcm => ?_
    · rw [popped_rd, hrd, u₂.rd, u₁.rd, pushed_rd]
    · rw [popped_wr, hwr, u₂.wr, u₁.wr, pushed_wr]; rfl
    · rw [popped_sp, hsp, tsp]; exact BitVec.sub_add_cancel _ _
    · have hr1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
      have hr2 : r ≠ .r2 := by rintro rfl; simp [preserved] at hr
      have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
      rw [popped_gpr hr1, hcs r hr hl, u₂.other r hr3, u₁.other r hr2, pushed_gpr]
    · rw [popped_mem]
      exact (frame_app (ws' := wr) h.fP |>.mono fun r hr => by
          simp only [List.mem_append, List.mem_singleton, wr] at hr ⊢; tauto).trans
        (frame_app (ws' := [below s]) (tmem ▸ hf))
    · have vc : count (t₂.callEntry.withRegions rd wr) = count t₂ := by
        simp only [count, State.withRegions_gpr, ce2, ce3]
      simp only [updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, t0, tmem,
        h.arg0 _ vsp vmem, h.arg1 _ vsp vmem, hlen, vc, tc] at hpost
      have hs : ∀ r ∈ [below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
        simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
      have hr' : hH.SH.Repr (pushed upd4 s).mem (State.addr st) m :=
        hH.repr _ _ _ _ _ (fun i hi => h.fP.bytes (R := ⟨State.addr st, H.S⟩) hs (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr
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
the state at `st` in `r0`, and `out` at `o` and the scratch space at `sc` in
`r1` and `r12`, as for `update`. -/
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

/-- What the block that sets the count leaves, in the frame of `s`: the
count `C`, and the other registers but `r2` and `r3`. -/
structure CntOK (s t : State) (C : BitVec 64) : Prop where
  gpr : ∀ r, r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r
  cnt : count t = C
  mem : t.mem = s.mem
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem cnt_nil (s : State) : WP isa (.block []) s fun t => CntOK s t (count s) :=
  WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cnt_movw (s : State) {c : Nat} (hc : c < 2 ^ 16) :
    WP isa (.block [.movw .r2 (BitVec.ofNat 16 c), .mov .r3 (.imm 0)]) s fun t => CntOK s t (BitVec.ofNat 64 c) :=
  wp_movw fun t₁ u₁ => VG.Proof.Sha256.Arm.Stream.wp_mov (op2_imm (by decide)) fun t₂ u₂ => WP.block_nil
    ⟨fun r h2 h3 => by rw [u₂.other r h3, u₁.other r h2], count_movw hc (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr,
      by rw [u₂.mem, u₁.mem], by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩

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

end FinArgs

theorem fin_frame {s : State} {st o sc : BitVec 32} (h : FinArgs hH s st o sc) {cnt : List Instr} {C : BitVec 64}
    (hcnt : WP isa (.block cnt) (pushed fin2 s) fun t => CntOK (pushed fin2 s) t C) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → m.length < 2 ^ 64 → C = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (State.addr o) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push fin2) (.seq (.block cnt) (.call H.finN H.finC)) (.pop .r1 8)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := fin2) (r := .r1) rfl (by show 8 ≤ s.sp.toNat; omega) (by decide) ?_
  refine WP.seq (WP.mono hcnt fun t k => ?_)
  have tsp : t.sp = s.sp - 8 := by rw [k.sp, FinArgs.psp]
  have tmem : t.mem = (pushed fin2 s).mem := k.mem
  have t0 : t.gpr .r0 = st := by rw [k.gpr _ (by decide) (by decide), pushed_gpr, h.r0]
  let rd : List Region := [⟨State.addr s.sp - 8, 8⟩]
  let wr : List Region := [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩]
  have vsp : (t.callEntry.withRegions rd wr).sp = s.sp - 8 := tsp
  have vmem : (t.callEntry.withRegions rd wr).mem = (pushed fin2 s).mem := tmem
  have argsSub : Region.Sub ⟨State.addr s.sp - 8, 8⟩ (below s) := by
    intro x hx; simp only [Region.Contains] at hx ⊢; bv_omega
  refine WP.callCalls (k := finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 (rd := rd) (wr := wr)
    ?_ ?_ ?_ ?_ hH.finNF
  · simp only [finK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0,
      h.arg0 _ vsp vmem, h.arg1 _ vsp vmem, h.sa0 _ vsp, t0, rd, wr]
    refine ⟨trivial, trivial, h.st_o, h.st_sc, h.o_sc, (h.b_st.sub_left argsSub), (h.b_o.sub_left argsSub),
      (h.b_sc.sub_left argsSub), h.nst, h.no, h.nsc, ?_⟩
    rw [vsp]; bv_omega
  · intro x n' ⟨r, hr, hcn⟩
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, rd, wr] at hr
    rw [k.rd, k.wr, pushed_rd, pushed_wr, e8]
    rcases hr with rfl | (rfl | rfl | rfl)
    · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      rw [h.a8]; simp only [Region.Contains, fin2, List.length_cons, List.length_nil] at hcn ⊢; omega
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · intro x n' hi
    obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
    exact ⟨r', by rw [k.wr, pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩
  · intro s₂ hrd hwr hsp hf hcs _ hpost
    have vc : count (t.callEntry.withRegions rd wr) = C := by
      rw [← k.cnt]; simp only [count, State.withRegions_gpr, ce2, ce3]
    simp only [finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, t0, tmem,
      h.arg0 _ vsp vmem, vc] at hpost
    refine hQ _ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ fun m hr hl hcm => ?_
    · rw [popped_rd, hrd, k.rd, pushed_rd]
    · rw [popped_wr, hwr, k.wr, pushed_wr]; rfl
    · rw [popped_sp, hsp, tsp]; exact BitVec.sub_add_cancel _ _
    · have hr1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
      have hr2 : r ≠ .r2 := by rintro rfl; simp [preserved] at hr
      have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
      rw [popped_gpr hr1, hcs r hr hl, k.gpr r hr2 hr3, pushed_gpr]
    · rw [popped_mem]
      exact (frame_app (ws' := wr) h.fP |>.mono fun r hr => by
          simp only [List.mem_append, List.mem_singleton, wr] at hr ⊢; tauto).trans
        (frame_app (ws' := [below s]) (tmem ▸ hf))
    · have hs : ∀ r ∈ [below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
        simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
      have hr' : hH.SH.Repr (pushed fin2 s).mem (State.addr st) m :=
        hH.repr _ _ _ _ _ (fun i hi => h.fP.bytes (R := ⟨State.addr st, H.S⟩) hs
          (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr
      rw [popped_mem]
      exact hpost m hr' hl hcm

end VG.Proof.Hmac.Generic.Arm
