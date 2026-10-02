import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Impl.Hmac.Generic.X86_64
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any streaming hash function: the x86-64 contracts

The contracts the proofs are written against.

* `initK`, `updK` and `finK` are the x86-64 contracts of a hash function's
  streaming `init`, `update` and `finalize`, with the sizes and the
  representation of the streaming state as parameters. At SHA-1 and MD5
  they are the contracts those functions are proved against
  (`Proof/<Alg>/X86_64/Contract.lean`); the SHA-512 family's imply them.
* `initG` and `finG` are those of our functions; the artifacts are emitted
  with the shared contracts of `Spec/Hmac/Generic.lean`, which imply them
  (`Contract.Implies`). (PBKDF2's iteration on x86-64 calls the compression
  functions directly: `Proof/Pbkdf2/X86_64/`.)
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state] ∧ ret.Disjoint state
  post s s' := R s'.mem (s.gpr .rdi) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space and one call below it. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, Wb⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let out : Region := ⟨s.gpr .rdx, F⟩
    let scratch : Region := ⟨s.gpr .rcx, Wb⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .rdi) m → m.length < 2 ^ 64 →
    s.gpr .rsi = BitVec.ofNat 64 m.length → (bytesAt s'.mem (s.gpr .rdx) F).take D = hash m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. Each function calls functions that call functions, so it
uses the 16 bytes of stack below its return address. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    (s.gpr .rcx).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    S.Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let out : Region := ⟨s.gpr .rcx, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (s.gpr .rdi) (xorPad k0 ipad ++ text) →
    s.gpr .rdx = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (s.gpr .rsi) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Hmac.Generic.X86_64

/-!
# HMAC over any streaming hash function on x86-64: the functions we call

`HashOK H` is what the proofs know of the hash function `H`: its streaming
functions are verified against `initK`, `updK` and `finK`, the representation
of its streaming state is determined by the state's bytes, and its sizes are
small. From it, each call is run with `WP.call`, and shown constant time in
two runs with `RelCT.call`.
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's x86-64 functions, verified. `Wb` is the
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
  hW : H.W ≤ 256
  /-- The representation depends only on the state's bytes. -/
  repr : ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < H.S, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p msg → SH.Repr m' q msg
  init : Verified X86_64.target H.initC (initK H.S SH.Repr)
  upd : Verified X86_64.target H.updC (updK H.S Wb SH.Repr)
  fin : Verified X86_64.target H.finC (finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initDepth : H.initC.depth ≤ 1
  updDepth : H.updC.depth ≤ 1
  finDepth : H.finC.depth ≤ 1
  initSp : NoSp H.initC
  updSp : NoSp H.updC
  finSp : NoSp H.finC

variable {H : Hash} (hH : HashOK H)

/-- What a call leaves: the regions, the callee-saved registers, and memory
outside what it may write. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below (s.gpr .rsp) 16]) s.mem s'.mem

/-- The stack of a call nested at most one deep. -/
theorem frame_depth {c : Prog isa} (hd : c.depth ≤ 1) {s : State} {ws : List Region} {m' : Mem}
    (h : Frame (ws ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem m') :
    Frame (ws ++ [below (s.gpr .rsp) 16]) s.mem m' :=
  h.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega_nat) (by omega_nat)⟩

/-- A region disjoint from the 16 bytes below `rsp` reads the same on entry
to a callee. -/
theorem callEntry_bytes (s : State) {p : Addr} {n : Nat} (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    s.callEntry.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
  Proof.Sha256.X86_64.Stream.callEntry_byte s (R := ⟨p, n⟩)
    (hd.sub_left (below_sub (by omega_nat) (by omega_nat))) hn hi

theorem ret_sub (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (s.gpr .rsp) 16) := by
  rw [State.callEntry_rsp]; exact Offset.sub_below _ (a := 8) (by omega_nat) (by omega_nat)

theorem stk_sub (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 16) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 8 = s.gpr .rsp - BitVec.ofNat 64 16 from Offset.sub_sub_ofNat _ 8 8]
  exact Offset.sub_below _ (a := 16) (by omega_nat) (by omega_nat)

theorem covers_wr {ws : List Region} {s : State} (h : Covers ws s.wr) : Covers ([] ++ ws) (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n (by simpa using hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem ne_rsp {r : Reg} (h : r ≠ .rsp) (s : State) : s.callEntry.gpr r = s.gpr r := State.callEntry_gpr _ h

/-! ## `init` -/

theorem init_call {s : State} {st : Addr} (hdi : s.gpr .rdi = st) (hc : Covers [⟨st, H.S⟩] s.wr)
    (hstk : (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, H.S⟩] s' → hH.SH.Repr s'.mem st [] → Q s') :
    WP isa (.call H.initN H.initC) s Q := by
  refine WP.call (k := initK H.S hH.SH.Repr) hH.init.1 hH.initSp (by have := hH.initDepth; omega_nat)
    (rd := []) (wr := [⟨st, H.S⟩]) ?_ (covers_wr hc) hc ?_
  · refine ⟨rfl, by simp [ne_rsp (by decide : Reg.rdi ≠ .rsp), hdi], ?_⟩
    simp only [State.withRegions_gpr, ne_rsp (by decide : Reg.rdi ≠ .rsp), hdi]
    exact hstk.sub_left (ret_sub s)
  · intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
    refine hQ s' ⟨h₁, h₂, h₃, frame_depth hH.initDepth h₄⟩ ?_
    simp only [initK, State.withRegions_gpr, ne_rsp (by decide : Reg.rdi ≠ .rsp), hdi, hm] at hpost
    exact hpost

/-! ## `update` -/

/-- The regions of a call of `update`. -/
structure UpdArgs (s : State) (st d sc : Addr) (len : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rdx : s.gpr .rdx = d
  rcx : (s.gpr .rcx).toNat = len
  r8 : s.gpr .r8 = sc
  cd : Covers [⟨d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  d_st : Region.Disjoint ⟨d, len⟩ ⟨st, H.S⟩
  d_sc : Region.Disjoint ⟨d, len⟩ ⟨sc, hH.Wb⟩
  stk_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩
  stk_d : (below (s.gpr .rsp) 16).Disjoint ⟨d, len⟩
  stk_sc : (below (s.gpr .rsp) 16).Disjoint ⟨sc, hH.Wb⟩

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
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rdx, h.rcx, h.r8]
  exact ⟨by trivial, by trivial, h.st_sc, h.d_st, h.d_sc, h.stk_st.sub_left (ret_sub s), h.stk_sc.sub_left (ret_sub s),
    h.stk_st.sub_left (stk_sub s), h.stk_d.sub_left (stk_sub s), h.stk_sc.sub_left (stk_sub s)⟩

theorem upd_call {s : State} {st d sc : Addr} {len : Nat} (h : UpdArgs hH s st d sc len)
    (hlen : len ≤ 2 ^ 64) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .rsi = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem d len)) → Q s') :
    WP isa (.call H.updN H.updC) s Q := by
  refine WP.call (k := updK H.S hH.Wb hH.SH.Repr) hH.upd.1 hH.updSp (by have := hH.updDepth; omega_nat)
    (h.pre hH) (h.covers hH) h.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' ⟨h₁, h₂, h₃, frame_depth hH.updDepth h₄⟩ fun m hr hc => ?_
  simp only [updK, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rdx ≠ .rsp), ne_rsp (by decide : Reg.rcx ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rdx, h.rcx, hm] at hpost
  have hS := hH.hSB
  have e : bytesAt s.callEntry.mem d len = bytesAt s.mem d len := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => callEntry_bytes s h.stk_d hlen (List.mem_range.mp hi)
  rw [← e]
  exact hpost m (hH.repr _ _ _ _ _ (fun i hi => callEntry_bytes s h.stk_st (by omega_nat) hi) hr) hc

/-! ## `finalize` -/

/-- The regions of a call of `finalize`. -/
structure FinArgs (s : State) (st o sc : Addr) : Prop where
  rdi : s.gpr .rdi = st
  rdx : s.gpr .rdx = o
  rcx : s.gpr .rcx = sc
  cw : Covers [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨st, H.S⟩ ⟨o, H.F⟩
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  o_sc : Region.Disjoint ⟨o, H.F⟩ ⟨sc, hH.Wb⟩
  stk_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩
  stk_o : (below (s.gpr .rsp) 16).Disjoint ⟨o, H.F⟩
  stk_sc : (below (s.gpr .rsp) 16).Disjoint ⟨sc, hH.Wb⟩

theorem FinArgs.pre {s : State} {st o sc : Addr} (h : FinArgs hH s st o sc) :
    (finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash).pre
      (s.callEntry.withRegions [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩]) := by
  simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rdx, h.rcx]
  exact ⟨by trivial, by trivial, h.st_o, h.st_sc, h.o_sc, h.stk_st.sub_left (ret_sub s),
    h.stk_o.sub_left (ret_sub s), h.stk_sc.sub_left (ret_sub s), h.stk_st.sub_left (stk_sub s),
    h.stk_o.sub_left (stk_sub s), h.stk_sc.sub_left (stk_sub s)⟩

theorem fin_call {s : State} {st o sc : Addr} (h : FinArgs hH s st o sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .rsi = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem o H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) s Q := by
  refine WP.call (k := finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 hH.finSp
    (by have := hH.finDepth; omega_nat) (h.pre hH) (covers_wr h.cw) h.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' ⟨h₁, h₂, h₃, frame_depth hH.finDepth h₄⟩ fun m hr hl hc => ?_
  simp only [finK, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rdx ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rdx, hm] at hpost
  have hS := hH.hSB
  exact hpost m (hH.repr _ _ _ _ _ (fun i hi => callEntry_bytes s h.stk_st (by omega_nat) hi) hr) hl hc

/-! ## The calls in two runs

A call is constant time when the callee's precondition holds in both runs
and its public arguments agree (`RelCT.call`). -/

include hH in
theorem init_rel {P : State → State → Prop} {st : Addr}
    (h : ∀ s s', P s s' → s.gpr .rdi = st ∧ s'.gpr .rdi = st ∧ Covers [⟨st, H.S⟩] s.wr ∧
      Covers [⟨st, H.S⟩] s'.wr ∧ (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩ ∧
      (below (s'.gpr .rsp) 16).Disjoint ⟨st, H.S⟩ ∧ s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  refine RelCT.call hH.init.1 hH.init.2.1 [] [⟨st, H.S⟩] fun s s' hp => ?_
  obtain ⟨d, d', c, c', k, k', sp⟩ := h s s' hp
  have pre : ∀ t : State, t.gpr .rdi = st → (below (t.gpr .rsp) 16).Disjoint ⟨st, H.S⟩ →
      (initK H.S hH.SH.Repr).pre (t.callEntry.withRegions [] [⟨st, H.S⟩]) := fun t hd hk => by
    refine ⟨rfl, by simp [ne_rsp (by decide : Reg.rdi ≠ .rsp), hd], ?_⟩
    simp only [State.withRegions_gpr, ne_rsp (by decide : Reg.rdi ≠ .rsp), hd]
    exact hk.sub_left (ret_sub t)
  exact ⟨pre s d k, pre s' d' k', by
    simp only [initK, State.withRegions_gpr, ne_rsp (by decide : Reg.rdi ≠ .rsp), d, d'],
    covers_wr c, c, covers_wr c', c', sp⟩

theorem upd_rel {P : State → State → Prop} {st d sc : Addr} {len : Nat}
    (h : ∀ s s', P s s' → UpdArgs hH s st d sc len ∧ UpdArgs hH s' st d sc len ∧
      s.gpr .rsi = s'.gpr .rsi ∧ s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.updN H.updC) fun _ _ => True := by
  refine RelCT.call hH.upd.1 hH.upd.2.1 [⟨d, len⟩] [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', si, sp⟩ := h s s' hp
  have cx : s.gpr .rcx = s'.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a.rcx, a'.rcx])
  refine ⟨a.pre hH, a'.pre hH, ?_, a.covers hH, a.cw, a'.covers hH, a'.cw, sp⟩
  simp only [updK, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rdx, a'.rdx,
    a.r8, a'.r8, si, cx, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem fin_rel {P : State → State → Prop} {st o sc : Addr}
    (h : ∀ s s', P s s' → FinArgs hH s st o sc ∧ FinArgs hH s' st o sc ∧
      s.gpr .rsi = s'.gpr .rsi ∧ s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.finN H.finC) fun _ _ => True := by
  refine RelCT.call hH.fin.1 hH.fin.2.1 [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', si, sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_wr a.cw, a.cw, covers_wr a'.cw, a'.cw, sp⟩
  simp only [finK, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a'.rdi, a.rdx, a'.rdx, a.rcx, a'.rcx, si, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Code the taint analysis checks from the registers `rs`, in two runs
whose single-run facts `F` and `F'` agree on them. -/
theorem rel_taint {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2))
    hc).wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Hmac.Generic.X86_64
