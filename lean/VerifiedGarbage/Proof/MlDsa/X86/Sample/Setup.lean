import VerifiedGarbage.Proof.MlKem.X86.SampleSetup
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlDsa.Sample.Mem
import VerifiedGarbage.Impl.MlDsa.X86.Sample.Common

/-!
# ML-DSA on x86 (32-bit): the layout of the sampling functions

Untrusted: everything here is checked by Lean. The four sampling functions
share a layout (`Impl/MlDsa/X86/Sample/Common.lean`), described by a `Lay`:
their number of arguments `nA` (the message pointer first), the arguments
that are the output polynomial (`iA`) and `scratch` (`iS`), the rate of the
SHAKE they use, the bytes they squeeze, and the message length: a constant,
or (`sample_in_ball`) the second argument. `Pre L` is what their shared
contracts' preconditions say, for the stack of 56 bytes they use (16 for
the leaf's frame, 40 for the calls); `PubP L` that two entry states have the
same pointers and `esp`. `Base` is what holds throughout the body: `esp` as
the leaf's frame left it, the permissions, and memory changed only in the
output polynomial, `scratch`, the 40 bytes of stack below the frame the
calls use, and the arguments on the stack (which `sample_in_ball`
overwrites; `Ctx` says they are intact, with `esi = scratch`).
-/

namespace VG.Proof.MlDsa.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem.X86.Sample (cR E1)

/-- The layout of a sampling function. -/
structure Lay where
  /-- The number of (32-bit) arguments. -/
  nA : Nat
  /-- The argument that is the output polynomial. -/
  iA : Nat
  /-- The argument that is `scratch`. -/
  iS : Nat
  rate : Nat
  outlen : Nat
  /-- The length of the message: a constant, or (`none`) argument 1. -/
  mlen : Option Nat

namespace Lay

/-- The message length. -/
def ml (L : Lay) (s₀ : State) : Nat := match L.mlen with
  | some k => k
  | none => (arg s₀ 1).toNat

/-- The source of the message length in the code. -/
def lenSrc (L : Lay) : Src := match L.mlen with
  | some k => .imm (BitVec.ofNat 32 k)
  | none => .mem (Impl.MlDsa.X86.Sample.argOp 1)

abbrev dP (_L : Lay) (s₀ : State) : BitVec 32 := arg s₀ 0
abbrev aP (L : Lay) (s₀ : State) : BitVec 32 := arg s₀ L.iA
abbrev sP (L : Lay) (s₀ : State) : BitVec 32 := arg s₀ L.iS
abbrev dA (L : Lay) (s₀ : State) : Addr := (L.dP s₀).setWidth 64
abbrev aA (L : Lay) (s₀ : State) : Addr := (L.aP s₀).setWidth 64
abbrev sA (L : Lay) (s₀ : State) : Addr := (L.sP s₀).setWidth 64
abbrev dR (L : Lay) (s₀ : State) : Region := ⟨L.dA s₀, L.ml s₀⟩
abbrev aR (L : Lay) (s₀ : State) : Region := ⟨L.aA s₀, 1024⟩
abbrev sR (L : Lay) (s₀ : State) : Region := ⟨L.sA s₀, 2048⟩
abbrev gR (L : Lay) (s₀ : State) : Region := ⟨argAddr s₀ 0, 4 * L.nA⟩
abbrev stkR (_L : Lay) (s₀ : State) : Region := ⟨(E0 s₀).setWidth 64 - 56#64, 56⟩
/-- The message. -/
abbrev Msg (L : Lay) (s₀ : State) : List Byte := bytesAt s₀.mem (L.dA s₀) (L.ml s₀)
/-- The Keccak functions' working space. -/
abbrev WW (L : Lay) (s₀ : State) : BitVec 32 := L.sP s₀ + BitVec.ofNat 32 200
/-- What the body may change. -/
abbrev W (L : Lay) (s₀ : State) : List Region := [L.aR s₀, L.sR s₀, cR s₀, L.gR s₀]
/-- The XOF output. -/
abbrev out (L : Lay) (s₀ : State) : List Byte :=
  Spec.Sha3.squeezeFrom L.rate (Proof.MlDsa.Sample.padded L.rate Spec.Sha3.shakeSuffix (L.Msg s₀)) 0 L.outlen

end Lay

/-- What the preconditions of the sampling functions' contracts say, for a
stack of 56 bytes. -/
structure Pre (L : Lay) (s₀ : State) : Prop where
  sp : 56 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * L.nA ≤ 2 ^ 32
  rd : s₀.rd = [L.dR s₀]
  wr : s₀.wr = [L.aR s₀, L.sR s₀, L.gR s₀]
  d_a : (L.dR s₀).Disjoint (L.aR s₀)
  d_s : (L.dR s₀).Disjoint (L.sR s₀)
  d_g : (L.dR s₀).Disjoint (L.gR s₀)
  a_s : (L.aR s₀).Disjoint (L.sR s₀)
  a_g : (L.aR s₀).Disjoint (L.gR s₀)
  s_g : (L.sR s₀).Disjoint (L.gR s₀)
  ret_d : (retR s₀).Disjoint (L.dR s₀)
  ret_a : (retR s₀).Disjoint (L.aR s₀)
  ret_s : (retR s₀).Disjoint (L.sR s₀)
  ret_g : (retR s₀).Disjoint (L.gR s₀)
  stk_d : (L.stkR s₀).Disjoint (L.dR s₀)
  stk_a : (L.stkR s₀).Disjoint (L.aR s₀)
  stk_s : (L.stkR s₀).Disjoint (L.sR s₀)
  stk_g : (L.stkR s₀).Disjoint (L.gR s₀)
  d_fit : (L.dP s₀).toNat + L.ml s₀ ≤ 2 ^ 32
  a_fit : (L.aP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (L.sP s₀).toNat + 2048 ≤ 2 ^ 32
  /-- The message is shorter than a block. -/
  ml_lt : L.ml s₀ < L.rate

/-- The pointers and `esp` agree (and so do the arguments). -/
def PubP (L : Lay) (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ ∀ i < L.nA, arg s₀ i = arg s₀' i

/-- The taint analysis proves `c` constant time from the registers `R`. -/
def TaintOk (R : List Reg) (c : Prog isa) : Prop :=
  ∃ hc : Taint.Hint VG.X86.Taint.T, (VG.X86.taint.check (τr R) c hc).isSome = true

/-- The layout's facts about its numbers, and the taint analysis of its
blocks (which depend on them). -/
structure Lay.Ok (L : Lay) : Prop where
  iA : L.iA < L.nA
  iS : L.iS < L.nA
  one : 1 < L.nA
  rate : L.rate ∈ Spec.Sha3.rates
  out : 840 + L.outlen + 4 ≤ 2048
  mlen : ∀ k, L.mlen = some k → k < 2 ^ 32
  tLd : TaintOk [.esp] (.block [.mov .esi (.mem (Impl.MlDsa.X86.Sample.argOp L.iS))])
  tAbs : TaintOk [.esp] (.block (Impl.MlDsa.X86.Sample.absArgs L.rate L.lenSrc))
  tPad : TaintOk [.esp] (.block (Impl.MlDsa.X86.Sample.padArgs L.rate L.lenSrc))
  tSqz : TaintOk [] (.block (Impl.MlDsa.X86.Sample.sqzArgs L.rate L.outlen))

namespace PubP
variable {L : Lay} {s₀ s₀' : State} (hL : L.Ok) (hq : PubP L s₀ s₀')
include hL hq

theorem dP : L.dP s₀ = L.dP s₀' := hq.2 0 (by have := hL.one; omega)
theorem aP : L.aP s₀ = L.aP s₀' := hq.2 _ hL.iA
theorem sP : L.sP s₀ = L.sP s₀' := hq.2 _ hL.iS
theorem ml : L.ml s₀ = L.ml s₀' := by
  unfold Lay.ml; split
  · rfl
  · rw [hq.2 1 hL.one]

omit hL in
theorem e1 : E1 s₀ = E1 s₀' := by simp only [E1, P0_esp, hq.1]

end PubP

theorem esp_nat (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) : (E1 s₀).toNat = (E0 s₀).toNat - 16 :=
  VG.Proof.MlKem.X86.Sample.esp_nat s₀ h

namespace Pre
variable {L : Lay} {s₀ : State} (hp : Pre L s₀)
include hp

theorem stk_below : L.stkR s₀ = below (E0 s₀) 56 := by
  simp only [Lay.stkR, below]; rw [Taint.sub_setWidth hp.sp]

theorem frame_sub : Region.Sub (frameR s₀) (L.stkR s₀) := by
  rw [hp.stk_below]; exact below_sub (by omega) hp.sp

theorem c_sub : Region.Sub (cR s₀) (L.stkR s₀) := by
  rw [hp.stk_below, VG.Proof.MlKem.X86.Sample.Pre.cR_eq]
  exact below_inner (sp := E0 s₀) (a := 40) (b := 56) (k := 16) (by omega) hp.sp

theorem frame_c : (frameR s₀).Disjoint (cR s₀) :=
  VG.Proof.MlKem.X86.Sample.Pre.cR_eq (s₀ := s₀) ▸
    VG.Proof.MlKem.X86.Sample.below_adj (sp := E0 s₀) (a := 16) (b := 40) (by have := hp.sp; omega)

theorem ret_c : (retR s₀).Disjoint (cR s₀) :=
  (hp.stk_below ▸ VG.Proof.MlKem.X86.Sample.ret_below (sp := E0 s₀) hp.sp).sub_right hp.c_sub

theorem fr16 : (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth (by have := hp.sp; omega)]

theorem hW : ∀ r ∈ L.W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [Lay.W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨hp.stk_a.sub_left hp.frame_sub, hp.ret_a⟩
  · exact ⟨hp.stk_s.sub_left hp.frame_sub, hp.ret_s⟩
  · exact ⟨hp.frame_c, hp.ret_c⟩
  · exact ⟨hp.stk_g.sub_left hp.frame_sub, hp.ret_g⟩

theorem dW : ∀ r ∈ L.W s₀, (L.dR s₀).Disjoint r := by
  intro r hr
  simp only [Lay.W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.d_a
  · exact hp.d_s
  · exact (hp.stk_d.sub_left hp.c_sub).symm
  · exact hp.d_g

theorem sub_s {o n : Nat} (h : o + n ≤ 2048) : Region.Sub ⟨L.sA s₀ + BitVec.ofNat 64 o, n⟩ (L.sR s₀) :=
  sub_of_contains (contains_at h hp.s_fit)

theorem off_eq {o : Nat} (h : o < 2048) :
    (L.sP s₀ + BitVec.ofNat 32 o).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 o :=
  ea_off (by have := hp.s_fit; omega)

theorem reg_s {o n : Nat} (h : o < 2048) :
    reg32 (L.sP s₀ + BitVec.ofNat 32 o) n = ⟨L.sA s₀ + BitVec.ofNat 64 o, n⟩ := by
  show (⟨(L.sP s₀ + BitVec.ofNat 32 o).setWidth 64, n⟩ : Region) = _
  rw [hp.off_eq h]

omit hp in
theorem reg_s0 {n : Nat} : reg32 (L.sP s₀) n = ⟨L.sA s₀ + BitVec.ofNat 64 0, n⟩ := by
  show (⟨(L.sP s₀).setWidth 64, n⟩ : Region) = _
  simp only [BitVec.add_zero]

/-- The push changes nothing but the frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide)
    (by rw [saveRegs_len]; exact Nat.le_trans (by decide) hp.sp)
  rw [saveRegs_len] at hf
  exact hf

theorem msg0 : bytesAt (P0 s₀).mem (L.dA s₀) (L.ml s₀) = L.Msg s₀ :=
  VG.Proof.MlKem.bytesAt_frame hp.P0_keep (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.stk_d.sub_left hp.frame_sub).symm) (by have := hp.d_fit; omega)

theorem kbufs : KBufs (E1 s₀) (L.sP s₀) (L.WW s₀) := by
  have hs := hp.s_fit
  have e := esp_nat s₀ (by have := hp.sp; omega)
  have hsp := hp.sp
  refine ⟨by rw [e]; omega, by omega, by rw [VG.Proof.MlKem.X86.Sample.toNat_off (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [reg_s0, hp.reg_s (by omega)]
    exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
  · rw [reg_s0]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · rw [hp.reg_s (by omega)]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))

theorem within_s {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (ho : o < 2048) (h : o + n ≤ 2048) :
    Within (reg32 (L.sP s₀ + BitVec.ofNat 32 o) n) s.wr := by
  rw [hp.reg_s ho]
  exact ⟨L.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, o, rfl, h⟩

theorem within_s0 {s : State} (hw : s.wr = (P0 s₀).wr) {n : Nat} (h : n ≤ 2048) :
    Within (reg32 (L.sP s₀) n) s.wr := by
  rw [reg_s0]
  exact ⟨L.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, 0, rfl, by simpa using h⟩

/-- An access of `n` bytes at offset `o` of `scratch` is permitted. -/
theorem inS {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (h : o + n ≤ 2048) :
    InRegions s.wr (L.sA s₀ + BitVec.ofNat 64 o) n :=
  ⟨L.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, contains_at h hp.s_fit⟩

theorem inS' {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (h : o + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (L.sA s₀ + BitVec.ofNat 64 o) n :=
  let ⟨r, hr, hc⟩ := hp.inS hw h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A write within the output polynomial is permitted. -/
theorem inA {s : State} (hw : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 256) :
    InRegions s.wr (Proof.MlDsa.Sample.coeffAddr (L.aA s₀) i) 4 :=
  ⟨L.aR s₀, by rw [hw, P0_wr, hp.wr]; simp, Proof.MlDsa.Sample.coeff_contains _ hi⟩

end Pre

/-! ## What holds throughout the body -/

structure Base (L : Lay) (s₀ s : State) : Prop where
  esp : s.gpr .esp = E1 s₀
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame (L.W s₀) (P0 s₀).mem s.mem

/-- `Base`, with the arguments intact and `esi = scratch`. -/
structure Ctx (L : Lay) (s₀ s : State) : Prop extends Base L s₀ s where
  args : ∀ i < L.nA, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i
  esi : s.gpr .esi = L.sP s₀

namespace Base
variable {L : Lay} {s₀ s : State} (hp : Pre L s₀) (h : Base L s₀ s)
include hp h

theorem msg : bytesAt s.mem (L.dA s₀) (L.ml s₀) = L.Msg s₀ :=
  (VG.Proof.MlKem.bytesAt_frame h.frame hp.dW (by have := hp.d_fit; omega)).trans hp.msg0

theorem argIn {i : Nat} (hi : i < L.nA) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [h.rd, h.wr]
  exact P0_argIn hi hp.sp' (by simp [hp.wr])

theorem argInW {i : Nat} (hi : i < L.nA) : InRegions s.wr (argAddr s₀ i) 4 := by
  rw [h.wr, P0_wr, hp.wr]
  exact ⟨L.gR s₀, by simp, arg_contains hi hp.sp'⟩

omit hp in
theorem argEa {i : Nat} : (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h.esp]; exact P0_argAddr s₀ i

omit hp in
/-- After a call that changes memory only within `rs`, parts of `W`. -/
theorem call {s' : State} (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ L.W s₀, Region.Sub r r') : Base L s₀ s' :=
  ⟨by rw [e₃ .esp (by simp [calleeSaved]), h.esp], by rw [e₁, h.rd], by rw [e₂, h.wr],
    h.frame.trans (fr.sub hs)⟩

end Base

/-- The arguments at the push. -/
theorem args0 {L : Lay} {s₀ : State} (hp : Pre L s₀) : ∀ i < L.nA, (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
  fun _ hi => P0_arg (by have := hp.sp; omega) hi hp.sp'
    (by rw [hp.fr16]; exact (hp.stk_g.sub_left hp.frame_sub))

/-- The regions a call of the Keccak functions changes are parts of `W`,
apart from the arguments. -/
theorem calls_sub {L : Lay} (hL : L.Ok) {s₀ : State} (hp : Pre L s₀) :
    ∀ r ∈ [reg32 (L.sP s₀) 200, reg32 (L.sP s₀ + BitVec.ofNat 32 840) L.outlen, reg32 (L.WW s₀) 640,
      below (E1 s₀) 40], ∃ r' ∈ L.W s₀, Region.Sub r r' ∧ r'.Disjoint (L.gR s₀) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.sR s₀, by simp, by rw [Pre.reg_s0]; exact hp.sub_s (by omega), hp.s_g⟩
  · exact ⟨L.sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by have := hL.out; omega), hp.s_g⟩
  · exact ⟨L.sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by omega), hp.s_g⟩
  · exact ⟨cR s₀, by simp, fun _ h => h, hp.stk_g.sub_left hp.c_sub⟩

end VG.Proof.MlDsa.X86.Sample
