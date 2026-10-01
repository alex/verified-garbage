import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Impl.Hmac.Generic.AArch64
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any streaming hash function: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against, as on x86-64
(`Proof/Hmac/Generic/X86_64/Hash.lean`).

* `initK`, `updK` and `finK` are the AArch64 contracts of a hash function's
  streaming `init`, `update` and `finalize`, with the sizes and the
  representation of the streaming state as parameters. Each lets the callee
  use the 16 bytes below the stack pointer (a frame saving `x30`), as SHA-1's
  and MD5's do; the contracts the functions are proved against imply them
  (the SHA-512 family's, which use no stack, too).
* `initG` and `finG` are those of our functions, which use no
  stack of their own but let the functions they call use those 16 bytes;
  the artifacts are emitted with the shared contracts of
  `Spec/Hmac/Generic.lean`, which imply them
  (`Contract.Implies`).

The return address is in `x30`, not on the stack, so no region needs to be
kept disjoint from it.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- The 16 bytes below the stack pointer. -/
abbrev stk (s : State) : Region := ⟨s.sp - 16, 16⟩

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, S⟩]
  post s s' := R s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, S⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, Wb⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint state ∧ (stk s).Disjoint data ∧ (stk s).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, S⟩
    let out : Region := ⟨s.gpr .x2, F⟩
    let scratch : Region := ⟨s.gpr .x3, Wb⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint state ∧ (stk s).Disjoint out ∧ (stk s).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .x0) m → m.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 m.length → (bytesAt s'.mem (s.gpr .x2) F).take D = hash m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    (s.gpr .x3).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint inner ∧ (stk s).Disjoint outer ∧ (stk s).Disjoint key ∧
    (stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    S.Repr s'.mem (s.gpr .x0) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .x1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let out : Region := ⟨s.gpr .x3, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint inner ∧ (stk s).Disjoint outer ∧ (stk s).Disjoint out ∧
    (stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (s.gpr .x0) (xorPad k0 ipad ++ text) →
    s.gpr .x2 = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (s.gpr .x1) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Hmac.Generic.AArch64

/-!
# HMAC over any streaming hash function on AArch64: the functions we call

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/Hash.lean`): `HashOK H` is what the proofs know
of the hash function `H`: its streaming functions are verified against
`initK`, `updK` and `finK`, the representation of its streaming state is
determined by the state's bytes, and its sizes are small. From it, each call
is run with `WP.callFV` (the callee may have a frame, in the 16 bytes below
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

/-- The ABI-preserved low halves of v8–v15. -/
abbrev VecKept (s s' : State) : Prop :=
  ∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem VecKept.trans {s t u : State} (h : VecKept s t) (k : VecKept t u) : VecKept s u :=
  fun r hr => (k r hr).trans (h r hr)

/-- What a call leaves: the regions, stack pointer, callee-saved GPRs except
`x30`, preserved SIMD low halves, and memory outside its writable regions. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below s.sp 16]) s.mem s'.mem
  vec : VecKept s s'

/-- The stack of a callee with at most one frame. -/
theorem frame_depth {c : Prog isa} (hd : c.fdepth ≤ 1) {s : State} {ws : List Region} {m' : Mem}
    (h : Frame (ws ++ [below s.sp (16 * c.fdepth)]) s.mem m') :
    Frame (ws ++ [below s.sp 16]) s.mem m' :=
  Frame.below_mono h (by omega_nat) (by omega_nat)

theorem fdepth_lt {c : Prog isa} (hd : c.fdepth ≤ 1) : 16 * c.fdepth < 2 ^ 64 := by omega_nat

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
  refine WP.callFV (k := initK H.S hH.SH.Repr) hH.init.1 (rd := []) (wr := [⟨st, H.S⟩]) ?_
    (covers_wr hc) hc ?_ (fdepth_lt hH.initDepth)
  · exact ⟨rfl, by simp [ce0, h0]⟩
  · intro s' h₁ h₂ h₃ h₄ h₅ hv hpost
    refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hH.initDepth h₄, hv⟩ ?_
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
  refine WP.callFV (k := updK H.S hH.Wb hH.SH.Repr) hH.upd.1 (h.pre hH) (h.covers hH) h.cw ?_
    (fdepth_lt hH.updDepth)
  intro s' h₁ h₂ h₃ h₄ h₅ hv hpost
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hH.updDepth h₄, hv⟩ fun m hr hc => ?_
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
  refine WP.callFV (k := finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 (h.pre hH)
    (covers_wr h.cw) h.cw ?_ (fdepth_lt hH.finDepth)
  intro s' h₁ h₂ h₃ h₄ h₅ hv hpost
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hH.finDepth h₄, hv⟩ fun m hr hl hc => ?_
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
