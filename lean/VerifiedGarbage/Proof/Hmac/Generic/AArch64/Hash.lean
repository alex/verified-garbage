import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Contract
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Impl.Pbkdf2.Generic.AArch64

/-!
# HMAC over any streaming hash function on AArch64: the functions we call

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/Hash.lean`): `HashOK H` is what the proofs know
of the hash function `H`: its streaming functions are verified against
`initK`, `updK` and `finK`, the representation of its streaming state is
determined by the state's bytes, and its sizes are small. From it, each call
is run with `WP.callF` (the callee may have a frame, in the 16 bytes below
the stack pointer), and shown constant time in two runs with `RelCT.call`.
A call writes no memory of its own on AArch64: the return address is in
`x30`.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's AArch64 functions, verified. `Wb` is the
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
  init : Verified AArch64.target H.initC (initK H.S SH.Repr)
  upd : Verified AArch64.target H.updC (updK H.S Wb SH.Repr)
  fin : Verified AArch64.target H.finC (finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initDepth : H.initC.fdepth ≤ 1
  updDepth : H.updC.fdepth ≤ 1
  finDepth : H.finC.fdepth ≤ 1

variable {H : Hash} (hH : HashOK H)

theorem stk_eq (s : State) : stk s = below s.sp 16 := rfl

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `x30`, and memory outside what it may write and the 16 bytes
below the stack pointer. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below s.sp 16]) s.mem s'.mem

/-- The stack of a callee with at most one frame. -/
theorem frame_depth {c : Prog isa} (hd : c.fdepth ≤ 1) {s : State} {ws : List Region} {m' : Mem}
    (h : Frame (ws ++ [below s.sp (16 * c.fdepth)]) s.mem m') :
    Frame (ws ++ [below s.sp 16]) s.mem m' :=
  Frame.below_mono h (by omega) (by omega)

theorem fdepth_lt {c : Prog isa} (hd : c.fdepth ≤ 1) : 16 * c.fdepth < 2 ^ 64 := by omega

theorem covers_wr {ws : List Region} {s : State} (h : Covers ws s.wr) : Covers ([] ++ ws) (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n (by simpa using hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! The argument registers are not changed by the call instruction. -/

@[simp] theorem ce0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := State.callEntry_gpr s (by decide)
@[simp] theorem ce1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := State.callEntry_gpr s (by decide)
@[simp] theorem ce2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := State.callEntry_gpr s (by decide)
@[simp] theorem ce3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := State.callEntry_gpr s (by decide)
@[simp] theorem ce4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := State.callEntry_gpr s (by decide)

/-! ## `init` -/

theorem init_call {s : State} {st : Addr} (h0 : s.gpr .x0 = st) (hc : Covers [⟨st, H.S⟩] s.wr)
    {Q : State → Prop} (hQ : ∀ s', After s [⟨st, H.S⟩] s' → hH.SH.Repr s'.mem st [] → Q s') :
    WP isa (.call H.initN H.initC) s Q := by
  refine WP.callF (k := initK H.S hH.SH.Repr) hH.init.1 (rd := []) (wr := [⟨st, H.S⟩]) ?_
    (covers_wr hc) hc ?_ (fdepth_lt hH.initDepth)
  · exact ⟨rfl, by simp [ce0, h0]⟩
  · intro s' h₁ h₂ h₃ h₄ h₅ hpost
    refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hH.initDepth h₄⟩ ?_
    simpa [initK, ce0, ce1, ce2, ce3, ce4, h0] using hpost

/-! ## `update` -/

/-- The regions of a call of `update`. -/
structure UpdArgs (s : State) (st d sc : Addr) (len : Nat) : Prop where
  x0 : s.gpr .x0 = st
  x2 : s.gpr .x2 = d
  x3 : (s.gpr .x3).toNat = len
  x4 : s.gpr .x4 = sc
  cd : Covers [⟨d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  d_st : Region.Disjoint ⟨d, len⟩ ⟨st, H.S⟩
  d_sc : Region.Disjoint ⟨d, len⟩ ⟨sc, hH.Wb⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_st : (below s.sp 16).Disjoint ⟨st, H.S⟩
  stk_d : (below s.sp 16).Disjoint ⟨d, len⟩
  stk_sc : (below s.sp 16).Disjoint ⟨sc, hH.Wb⟩

theorem UpdArgs.covers {s : State} {st d sc : Addr} {len : Nat} (h : UpdArgs hH s st d sc len) :
    Covers ([⟨d, len⟩] ++ [⟨st, H.S⟩, ⟨sc, hH.Wb⟩]) (s.rd ++ s.wr) :=
  fun a n hi => by
    rcases List.mem_append.mp (show _ ∈ _ from hi.choose_spec.1) with hr | hr
    · exact h.cd a n ⟨_, hr, hi.choose_spec.2⟩
    · obtain ⟨r, hr', hc⟩ := h.cw a n ⟨_, hr, hi.choose_spec.2⟩
      exact ⟨r, List.mem_append_right _ hr', hc⟩

theorem UpdArgs.pre {s : State} {st d sc : Addr} {len : Nat} (h : UpdArgs hH s st d sc len) :
    (updK H.S hH.Wb hH.SH.Repr).pre (s.callEntry.withRegions [⟨d, len⟩] [⟨st, H.S⟩, ⟨sc, hH.Wb⟩]) := by
  simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, ce0, ce2, ce3, ce4, h.x0, h.x2, h.x3, h.x4]
  exact ⟨by trivial, by trivial, h.st_sc, h.d_st, h.d_sc, h.sp16, h.stk_st, h.stk_d, h.stk_sc⟩

theorem upd_call {s : State} {st d sc : Addr} {len : Nat} (h : UpdArgs hH s st d sc len)
    {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .x1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem d len)) → Q s') :
    WP isa (.call H.updN H.updC) s Q := by
  refine WP.callF (k := updK H.S hH.Wb hH.SH.Repr) hH.upd.1 (h.pre hH) (h.covers hH) h.cw ?_
    (fdepth_lt hH.updDepth)
  intro s' h₁ h₂ h₃ h₄ h₅ hpost
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hH.updDepth h₄⟩ fun m hr hc => ?_
  simp only [updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, ce3, h.x0,
    h.x2, h.x3] at hpost
  exact hpost m hr hc

/-! ## `finalize` -/

/-- The regions of a call of `finalize`. -/
structure FinArgs (s : State) (st o sc : Addr) : Prop where
  x0 : s.gpr .x0 = st
  x2 : s.gpr .x2 = o
  x3 : s.gpr .x3 = sc
  cw : Covers [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨st, H.S⟩ ⟨o, H.F⟩
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  o_sc : Region.Disjoint ⟨o, H.F⟩ ⟨sc, hH.Wb⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_st : (below s.sp 16).Disjoint ⟨st, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨o, H.F⟩
  stk_sc : (below s.sp 16).Disjoint ⟨sc, hH.Wb⟩

theorem FinArgs.pre {s : State} {st o sc : Addr} (h : FinArgs hH s st o sc) :
    (finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash).pre
      (s.callEntry.withRegions [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩]) := by
  simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, ce0, ce2, ce3, h.x0, h.x2, h.x3]
  exact ⟨by trivial, by trivial, h.st_o, h.st_sc, h.o_sc, h.sp16, h.stk_st, h.stk_o, h.stk_sc⟩

theorem fin_call {s : State} {st o sc : Addr} (h : FinArgs hH s st o sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .x1 = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem o H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) s Q := by
  refine WP.callF (k := finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 (h.pre hH)
    (covers_wr h.cw) h.cw ?_ (fdepth_lt hH.finDepth)
  intro s' h₁ h₂ h₃ h₄ h₅ hpost
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hH.finDepth h₄⟩ fun m hr hl hc => ?_
  simp only [finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, h.x0,
    h.x2] at hpost
  exact hpost m hr hl hc

/-! ## The calls in two runs

A call is constant time when the callee's precondition holds in both runs
and its public arguments agree (`RelCT.call`). -/

include hH in
theorem init_rel {P : State → State → Prop} {st : Addr}
    (h : ∀ s s', P s s' → s.gpr .x0 = st ∧ s'.gpr .x0 = st ∧ Covers [⟨st, H.S⟩] s.wr ∧
      Covers [⟨st, H.S⟩] s'.wr ∧ s.sp = s'.sp) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  refine RelCT.call hH.init.1 hH.init.2.1 [] [⟨st, H.S⟩] fun s s' hp => ?_
  obtain ⟨d, d', c, c', sp⟩ := h s s' hp
  refine ⟨⟨rfl, by simp [ce0, d]⟩, ⟨rfl, by simp [d']⟩, ?_, covers_wr c, c, covers_wr c', c'⟩
  simp only [initK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, d, d',
    sp]
  exact ⟨trivial, trivial⟩

theorem upd_rel {P : State → State → Prop} {st d sc : Addr} {len : Nat}
    (h : ∀ s s', P s s' → UpdArgs hH s st d sc len ∧ UpdArgs hH s' st d sc len ∧
      s.gpr .x1 = s'.gpr .x1 ∧ s.sp = s'.sp) :
    RelCT isa P (.call H.updN H.updC) fun _ _ => True := by
  refine RelCT.call hH.upd.1 hH.upd.2.1 [⟨d, len⟩] [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', x1, sp⟩ := h s s' hp
  have x3 : s.gpr .x3 = s'.gpr .x3 := BitVec.eq_of_toNat_eq (by rw [a.x3, a'.x3])
  refine ⟨a.pre hH, a'.pre hH, ?_, a.covers hH, a.cw, a'.covers hH, a'.cw⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4, a.x0,
    a'.x0, a.x2, a'.x2, a.x4, a'.x4, x1, x3, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem fin_rel {P : State → State → Prop} {st o sc : Addr}
    (h : ∀ s s', P s s' → FinArgs hH s st o sc ∧ FinArgs hH s' st o sc ∧
      s.gpr .x1 = s'.gpr .x1 ∧ s.sp = s'.sp) :
    RelCT isa P (.call H.finN H.finC) fun _ _ => True := by
  refine RelCT.call hH.fin.1 hH.fin.2.1 [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', x1, sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_wr a.cw, a.cw, covers_wr a'.cw, a'.cw⟩
  simp only [finK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, a.x0,
    a'.x0, a.x2, a'.x2, a.x3, a'.x3, x1, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Code the taint analysis checks from the registers `rs` (and the stack
pointer), in two runs whose single-run facts `F` and `F'` agree on them. -/
theorem rel_taint {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  refine ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => ?_) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨sp, hr⟩ := hag s s' h.1 h.2
  exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Hmac.Generic.AArch64
