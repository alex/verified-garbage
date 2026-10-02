import VerifiedGarbage.Impl.Scrypt.X86.Scrypt
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scrypt on x86 (32-bit): where everything is

As on x86-64 (`Proof/Scrypt/X86_64/Whole/Layout.lean`): the contract the proof
is written against (`scryptX86`), the function's buffers and the 116 bytes of
stack below its return address, from `A` up (`Lay`): the 80 bytes the calls
use, then the frame (36 bytes, from `A + 80`: the callee's arguments, then the
next block). The return address is at `A + 116`, our arguments from `A + 120`.
`Ctx` is what holds between the frame's push and pop: the permissions, `esp`,
the callee-saved registers, our arguments (`Kept`), and that memory changed
only in the writable buffers and the stack.
-/

namespace VG.Proof.Scrypt

open VG.X86 in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. x86 contract for `vg_scrypt(password,
password_len, salt, salt_len, r, b, blen, v, vlen, scratch, slen, out,
out_len)`, every argument on the stack, with 116 bytes of stack below the
return address. -/
def scryptX86 : Contract X86.isa where
  pre s :=
    let r := (arg s 4).toNat
    let pwR : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let saltR : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let bR : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat * 128⟩
    let vR : Region := ⟨(arg s 7).setWidth 64, (arg s 8).toNat * 128⟩
    let scR : Region := ⟨(arg s 9).setWidth 64, (arg s 10).toNat * 128⟩
    let outR : Region := ⟨(arg s 11).setWidth 64, (arg s 12).toNat⟩
    let args : Region := ⟨argAddr s 0, 52⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116, 116⟩
    116 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 56 ≤ 2 ^ 32 ∧
    s.rd = [pwR, saltR] ∧ s.wr = [bR, vR, scR, outR, args] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧ pwR.Disjoint args ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    saltR.Disjoint args ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    ret.Disjoint pwR ∧ ret.Disjoint saltR ∧ ret.Disjoint bR ∧ ret.Disjoint vR ∧ ret.Disjoint scR ∧
    ret.Disjoint outR ∧ ret.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧ stack.Disjoint args ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + (arg s 6).toNat * 128 ≤ 2 ^ 32 ∧ (arg s 7).toNat + (arg s 8).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 9).toNat + (arg s 10).toNat * 128 ≤ 2 ^ 32 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32 ∧
    0 < r ∧ (arg s 6).toNat % r = 0 ∧ (arg s 8).toNat % r = 0 ∧
    Spec.Scrypt.valid ((arg s 8).toNat / r) r ((arg s 6).toNat / r) (arg s 12).toNat ∧
    (arg s 12).toNat ≤ (2 ^ 32 - 1) * 32 ∧ (arg s 10).toNat = r + 16
  post s s' :=
    let r := (arg s 4).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
      (Spec.Scrypt.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) ((arg s 8).toNat / r) r
      ((arg s 6).toNat / r) (arg s 12).toNat =
      some (Spec.Scrypt.bytesAt s'.mem ((arg s 11).setWidth 64) (arg s 12).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 13, arg s₁ i = arg s₂ i) ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem ((arg s₁ 0).setWidth 64) (arg s₁ 1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem ((arg s₁ 2).setWidth 64) (arg s₁ 3).toNat) (arg s₁ 4).toNat
        ((arg s₁ 6).toNat / (arg s₁ 4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (arg s₁ 4).toNat ((arg s₁ 8).toNat / (arg s₁ 4).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem ((arg s₂ 0).setWidth 64) (arg s₂ 1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem ((arg s₂ 2).setWidth 64) (arg s₂ 3).toNat) (arg s₂ 4).toNat
        ((arg s₂ 6).toNat / (arg s₂ 4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (arg s₂ 4).toNat ((arg s₂ 8).toNat / (arg s₂ 4).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86
open VG.Proof.Pbkdf2.Whole.X86 (toNat_setWidth64)

/-- The arguments and the lowest byte of the stack used (`esp - 116` on entry). -/
structure Lay where
  pw : BitVec 32
  pwl : BitVec 32
  salt : BitVec 32
  sl : BitVec 32
  r : BitVec 32
  b : BitVec 32
  blen : BitVec 32
  v : BitVec 32
  vlen : BitVec 32
  scr : BitVec 32
  slen : BitVec 32
  out : BitVec 32
  ol : BitVec 32
  B : BitVec 32

namespace Lay

variable (L : Lay)

/-- The lowest byte of the stack used, as an address. -/
abbrev A : Addr := L.B.setWidth 64

abbrev PW : Region := ⟨L.pw.setWidth 64, L.pwl.toNat⟩
abbrev SALT : Region := ⟨L.salt.setWidth 64, L.sl.toNat⟩
abbrev BB : Region := ⟨L.b.setWidth 64, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨L.v.setWidth 64, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨L.scr.setWidth 64, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨L.out.setWidth 64, L.ol.toNat⟩
/-- Our arguments. -/
abbrev ARGS : Region := ⟨L.A + BitVec.ofNat 64 120, 52⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.A, 116⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.A + BitVec.ofNat 64 80, 36⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.A + BitVec.ofNat 64 116, 4⟩

/-- `p` and `N`. -/
abbrev pp : Nat := L.blen.toNat / L.r.toNat
abbrev NN : Nat := L.vlen.toNat / L.r.toNat

/-- What the contract says of where the buffers and the stack are, and of
the parameters. -/
structure Ok : Prop where
  pb : L.PW.Disjoint L.BB
  pv : L.PW.Disjoint L.VV
  pc : L.PW.Disjoint L.SC
  po : L.PW.Disjoint L.OUT
  pa : L.PW.Disjoint L.ARGS
  sb : L.SALT.Disjoint L.BB
  sv : L.SALT.Disjoint L.VV
  sc : L.SALT.Disjoint L.SC
  so : L.SALT.Disjoint L.OUT
  sa : L.SALT.Disjoint L.ARGS
  bv : L.BB.Disjoint L.VV
  bc : L.BB.Disjoint L.SC
  bo : L.BB.Disjoint L.OUT
  ba : L.BB.Disjoint L.ARGS
  vc : L.VV.Disjoint L.SC
  vo : L.VV.Disjoint L.OUT
  va : L.VV.Disjoint L.ARGS
  co : L.SC.Disjoint L.OUT
  ca : L.SC.Disjoint L.ARGS
  oa : L.OUT.Disjoint L.ARGS
  rp : L.RET.Disjoint L.PW
  rs : L.RET.Disjoint L.SALT
  rb : L.RET.Disjoint L.BB
  rv : L.RET.Disjoint L.VV
  rc : L.RET.Disjoint L.SC
  ro : L.RET.Disjoint L.OUT
  kp : L.STK.Disjoint L.PW
  ks : L.STK.Disjoint L.SALT
  kb : L.STK.Disjoint L.BB
  kv : L.STK.Disjoint L.VV
  kc : L.STK.Disjoint L.SC
  ko : L.STK.Disjoint L.OUT
  np : L.pw.toNat + L.pwl.toNat ≤ 2 ^ 32
  ns : L.salt.toNat + L.sl.toNat ≤ 2 ^ 32
  nb : L.b.toNat + L.blen.toNat * 128 ≤ 2 ^ 32
  nv : L.v.toNat + L.vlen.toNat * 128 ≤ 2 ^ 32
  nc : L.scr.toNat + L.slen.toNat * 128 ≤ 2 ^ 32
  no : L.out.toNat + L.ol.toNat ≤ 2 ^ 32
  nB : L.B.toNat + 172 ≤ 2 ^ 32
  rpos : 0 < L.r.toNat
  bmod : L.blen.toNat % L.r.toNat = 0
  vmod : L.vlen.toNat % L.r.toNat = 0
  valid : Spec.Scrypt.valid L.NN L.r.toNat L.pp L.ol.toNat
  olb : L.ol.toNat ≤ (2 ^ 32 - 1) * 32
  slen : L.slen.toNat = L.r.toNat + 16

end Lay

/-! ## Regions within the buffers and the stack -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

/-- A word `B + k` of the stack, as an address. -/
theorem addr_B {B : BitVec 32} {k : Nat} (h : B.toNat + k < 2 ^ 32) :
    (B + BitVec.ofNat 32 k).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have := B.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := B.toNat + k) h,
    Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := B.toNat) (by omega),
    Nat.mod_eq_of_lt (a := B.toNat + k) (by omega)]

/-- A writable region is within one of the writable buffers. -/
def InBuf (L : Lay) (r : Region) : Prop :=
  Within r L.BB ∨ Within r L.VV ∨ Within r L.SC ∨ Within r L.OUT

theorem InBuf.sub {L : Lay} {r : Region} (h : InBuf L r) :
    ∃ R, (R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) ∧ Region.Sub r R := by
  rcases h with h | h | h | h
  · exact ⟨_, .inl rfl, h.sub⟩
  · exact ⟨_, .inr (.inl rfl), h.sub⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), h.sub⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), h.sub⟩

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

omit h in
theorem toNat_A : L.A.toNat = L.B.toNat := toNat_setWidth64 _

/-- `[esp + d]` in the frame. -/
theorem ea_sp {d : Nat} (hd : d + 4 ≤ 92) :
    (L.B + BitVec.ofNat 32 80 + BitVec.ofNat 32 d).setWidth 64 = L.A + BitVec.ofNat 64 (80 + d) := by
  have := h.nB
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, addr_B (by omega)]

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_in {d n : Nat} (h₁ : d + n ≤ 116) {r : Region} (hr : InBuf L r) :
    Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.A + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  obtain ⟨R, hR, hsr⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hsr
  · exact (h.kv.sub_left hs).sub_right hsr
  · exact (h.kc.sub_left hs).sub_right hsr
  · exact (h.ko.sub_left hs).sub_right hsr

/-- A range in our arguments is disjoint from one in a writable buffer. -/
theorem args_in {d n : Nat} (h₁ : 120 ≤ d) (h₂ : d + n ≤ 172) {r : Region} (hr : InBuf L r) :
    Region.Disjoint ⟨L.A + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.A + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  obtain ⟨R, hR, hsr⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hsr
  · exact (h.va.symm.sub_left hs).sub_right hsr
  · exact (h.ca.symm.sub_left hs).sub_right hsr
  · exact (h.oa.symm.sub_left hs).sub_right hsr

/-- The password misses every writable buffer. -/
theorem pw_in {r : Region} (hr : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.pb.sub_right hs, h.pv.sub_right hs, h.pc.sub_right hs, h.po.sub_right hs]

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

end Lay.Ok

/-! ## What the calls cannot change -/

/-- Our arguments, the words from `A + 120` (`[esp + 40]` in the frame). -/
structure Kept (L : Lay) (m : Mem) : Prop where
  pw : m.readW (L.A + BitVec.ofNat 64 120) 32 = L.pw
  pwl : m.readW (L.A + BitVec.ofNat 64 124) 32 = L.pwl
  salt : m.readW (L.A + BitVec.ofNat 64 128) 32 = L.salt
  sl : m.readW (L.A + BitVec.ofNat 64 132) 32 = L.sl
  r : m.readW (L.A + BitVec.ofNat 64 136) 32 = L.r
  b : m.readW (L.A + BitVec.ofNat 64 140) 32 = L.b
  blen : m.readW (L.A + BitVec.ofNat 64 144) 32 = L.blen
  v : m.readW (L.A + BitVec.ofNat 64 148) 32 = L.v
  vlen : m.readW (L.A + BitVec.ofNat 64 152) 32 = L.vlen
  scr : m.readW (L.A + BitVec.ofNat 64 156) 32 = L.scr
  out : m.readW (L.A + BitVec.ofNat 64 164) 32 = L.out
  ol : m.readW (L.A + BitVec.ofNat 64 168) 32 = L.ol

/-- Our arguments survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {m m' : Mem} {rs : List Region} (hk : Kept L m) (hf : Frame rs m m')
    (hd : ∀ R ∈ rs, L.ARGS.Disjoint R) : Kept L m' := by
  have k : ∀ d, 120 ≤ d → d + 4 ≤ 172 →
      m'.readW (L.A + BitVec.ofNat 64 d) 32 = m.readW (L.A + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => hf.readW (r := L.ARGS) (Offset.contains _ h₁ (by omega) (by omega))
      (fun R hR => hd R hR) (by decide)
  exact ⟨(k 120 (by omega) (by omega)).trans hk.pw, (k 124 (by omega) (by omega)).trans hk.pwl,
    (k 128 (by omega) (by omega)).trans hk.salt, (k 132 (by omega) (by omega)).trans hk.sl,
    (k 136 (by omega) (by omega)).trans hk.r, (k 140 (by omega) (by omega)).trans hk.b,
    (k 144 (by omega) (by omega)).trans hk.blen, (k 148 (by omega) (by omega)).trans hk.v,
    (k 152 (by omega) (by omega)).trans hk.vlen, (k 156 (by omega) (by omega)).trans hk.scr,
    (k 164 (by omega) (by omega)).trans hk.out, (k 168 (by omega) (by omega)).trans hk.ol⟩

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT, L.ARGS]
  esp : t.gpr .esp = L.B + BitVec.ofNat 32 80
  cs : ∀ r ∈ calleeSaved, r ≠ .esp → t.gpr r = g r
  kept : Kept L t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.FR, L.BB, L.VV, L.SC, L.OUT]

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6, arg s 7, arg s 8, arg s 9, arg s 10,
    arg s 11, arg s 12, s.gpr .esp - BitVec.ofNat 32 116⟩

theorem lay_esp (s : State) :
    (lay s).B + BitVec.ofNat 32 116 = s.gpr .esp := BitVec.sub_add_cancel _ _

theorem lay_B {s : State} (h : 116 ≤ (s.gpr .esp).toNat) : (lay s).B.toNat = (s.gpr .esp).toNat - 116 :=
  sub_toNat h

theorem lay_args {s : State} (h : 116 ≤ (s.gpr .esp).toNat) (h' : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (lay s).A + BitVec.ofNat 64 120 = argAddr s 0 := by
  rw [Lay.A, ← addr_B (by rw [lay_B h]; omega)]
  simp only [lay, argAddr]
  congr 1
  bv_omega

theorem lay_ret {s : State} (h : 116 ≤ (s.gpr .esp).toNat) (h' : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (lay s).A + BitVec.ofNat 64 116 = (s.gpr .esp).setWidth 64 := by
  rw [Lay.A, ← addr_B (by rw [lay_B h]; omega), lay_esp s]

theorem lay_stk {s : State} (h : 116 ≤ (s.gpr .esp).toNat) :
    (lay s).A = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116 := by
  apply BitVec.eq_of_toNat_eq
  have := (s.gpr .esp).isLt
  rw [Lay.A, toNat_setWidth64, lay_B h, Offset.toNat_sub_ofNat, toNat_setWidth64]
  omega

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptX86.pre s) : (lay s).Ok := by
  obtain ⟨h116, h56, -, -, pb, pv, pc, po, pa, sb, sv, sc, so, sa, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    rp, rs, rb, rv, rc, ro, -, kp, ks, kb, kv, kc, ko, -, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval,
    olb, slen⟩ := h
  have ea : (lay s).ARGS = ⟨argAddr s 0, 52⟩ := by simp only [Lay.ARGS, lay_args h116 h56]
  have er : (lay s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by simp only [Lay.RET, lay_ret h116 h56]
  have ek : (lay s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 116, 116⟩ := by
    simp only [Lay.STK, lay_stk h116]
  exact ⟨pb, pv, pc, po, ea ▸ pa, sb, sv, sc, so, ea ▸ sa, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co,
    ea ▸ ca, ea ▸ oa, er ▸ rp, er ▸ rs, er ▸ rb, er ▸ rv, er ▸ rc, er ▸ ro, ek ▸ kp, ek ▸ ks, ek ▸ kb,
    ek ▸ kv, ek ▸ kc, ek ▸ ko, np, ns, nb, nv, nc, no, by rw [lay_B h116]; omega, rpos, bmod, vmod, hval,
    olb, slen⟩

end VG.Proof.Scrypt.X86.Whole
