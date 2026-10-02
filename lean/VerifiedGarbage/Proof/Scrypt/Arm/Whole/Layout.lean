import VerifiedGarbage.Impl.Scrypt.Arm.Scrypt
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.Arm.Target

/-!
# scrypt on 32-bit ARM: where everything is

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Layout.lean`): the contract the
proof is written against (`scryptArm`), the function's buffers, its stack
arguments (`ARGS`, 36 bytes at the stack pointer) and the 40 bytes of stack
below the stack pointer the calls use (`STK`), and the save area in `scratch`
(`SV`, from `scratch + 128 (r + 15)`), which holds our caller's `r4`–`r11` and
our return address (`Saved`). `Ctx` is what holds between the calls.
-/

namespace VG.Proof.Scrypt

open VG.Arm in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. 32-bit ARM contract for
`vg_scrypt(password = r0, password_len = r1, salt = r2, salt_len = r3, r, b,
blen, v, vlen, scratch, slen, out, out_len)`, the last nine on the stack,
with 40 bytes of stack below the stack pointer. -/
def scryptArm : Contract Arm.isa where
  pre s :=
    let r := (stackArg s 0).toNat
    let pwR : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let saltR : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let bR : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat * 128⟩
    let vR : Region := ⟨State.addr (stackArg s 3), (stackArg s 4).toNat * 128⟩
    let scR : Region := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat * 128⟩
    let outR : Region := ⟨State.addr (stackArg s 7), (stackArg s 8).toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 36⟩
    let stack : Region := ⟨State.addr s.sp - BitVec.ofNat 64 40, 40⟩
    40 ≤ s.sp.toNat ∧ s.sp.toNat + 36 ≤ 2 ^ 32 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 5).toNat + (stackArg s 6).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 32 ∧
    0 < r ∧ (stackArg s 2).toNat % r = 0 ∧ (stackArg s 4).toNat % r = 0 ∧
    Spec.Scrypt.valid ((stackArg s 4).toNat / r) r ((stackArg s 2).toNat / r) (stackArg s 8).toNat ∧
    (stackArg s 8).toNat ≤ (2 ^ 32 - 1) * 32 ∧ (stackArg s 6).toNat = r + 16
  post s s' :=
    let r := (stackArg s 0).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Scrypt.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) ((stackArg s 4).toNat / r) r
      ((stackArg s 2).toNat / r) (stackArg s 8).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (State.addr (stackArg s 7)) (stackArg s 8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧
    stackArg s₁ 5 = stackArg s₂ 5 ∧ stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧
    stackArg s₁ 8 = stackArg s₂ 8 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (s₁.gpr .r1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (State.addr (s₁.gpr .r2)) (s₁.gpr .r3).toNat) (stackArg s₁ 0).toNat
        ((stackArg s₁ 2).toNat / (stackArg s₁ 0).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (stackArg s₁ 0).toNat ((stackArg s₁ 4).toNat / (stackArg s₁ 0).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (s₂.gpr .r1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (State.addr (s₂.gpr .r2)) (s₂.gpr .r3).toNat) (stackArg s₂ 0).toNat
        ((stackArg s₂ 2).toNat / (stackArg s₂ 0).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (stackArg s₂ 0).toNat ((stackArg s₂ 4).toNat / (stackArg s₂ 0).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm

/-- The arguments and the stack pointer on entry. -/
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
  sp : BitVec 32

namespace Lay

variable (L : Lay)

abbrev PW : Region := ⟨State.addr L.pw, L.pwl.toNat⟩
abbrev SALT : Region := ⟨State.addr L.salt, L.sl.toNat⟩
abbrev BB : Region := ⟨State.addr L.b, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨State.addr L.v, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨State.addr L.scr, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨State.addr L.out, L.ol.toNat⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨State.addr L.sp, 36⟩
/-- The stack the calls use. -/
abbrev STK : Region := ⟨State.addr L.sp - BitVec.ofNat 64 40, 40⟩
/-- The save area. -/
abbrev SVA : Addr := State.addr L.scr + BitVec.ofNat 64 (128 * (L.r.toNat + 15))
abbrev SV : Region := ⟨L.SVA, 36⟩

/-- `p` and `N`. -/
abbrev pp : Nat := L.blen.toNat / L.r.toNat
abbrev NN : Nat := L.vlen.toNat / L.r.toNat

/-- The save area's address, as the code computes it. -/
abbrev svb : BitVec 32 := L.scr + L.r <<< 7 + 1920

/-- What the contract says of where the buffers and the stack are, and of
the parameters. -/
structure Ok : Prop where
  pb : L.PW.Disjoint L.BB
  pv : L.PW.Disjoint L.VV
  pc : L.PW.Disjoint L.SC
  po : L.PW.Disjoint L.OUT
  sb : L.SALT.Disjoint L.BB
  sv : L.SALT.Disjoint L.VV
  sc : L.SALT.Disjoint L.SC
  so : L.SALT.Disjoint L.OUT
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
  nS : 40 ≤ L.sp.toNat
  nA : L.sp.toNat + 36 ≤ 2 ^ 32
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

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (by decide))

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

/-- The stack the calls use misses every writable buffer. -/
theorem stk_in {r : Region} (hr : InBuf L r) : L.STK.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.kb.sub_right hs, h.kv.sub_right hs, h.kc.sub_right hs, h.ko.sub_right hs]

/-- Our stack arguments miss every writable buffer. -/
theorem args_in {r : Region} (hr : InBuf L r) : L.ARGS.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.ba.symm.sub_right hs, h.va.symm.sub_right hs, h.ca.symm.sub_right hs, h.oa.symm.sub_right hs]

/-- The password misses every writable buffer. -/
theorem pw_in {r : Region} (hr : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.pb.sub_right hs, h.pv.sub_right hs, h.pc.sub_right hs, h.po.sub_right hs]

/-- So does the salt. -/
theorem salt_in {r : Region} (hr : InBuf L r) : L.SALT.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := hr.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [h.sb.sub_right hs, h.sv.sub_right hs, h.sc.sub_right hs, h.so.sub_right hs]

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

/-- The save area is in `scratch`. -/
theorem sv_sc : Region.Sub L.SV L.SC := by
  have := h.slen
  exact Offset.sub_base _ (by rw [this]; omega)

/-- The save area as the code computes it. -/
theorem svb_toNat : L.svb.toNat = L.scr.toNat + 128 * (L.r.toNat + 15) := by
  have := h.nc; have := h.slen; have := h.rpos
  have e : (L.r <<< 7).toNat = L.r.toNat * 128 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  simp only [Lay.svb, BitVec.toNat_add, e, show (1920 : BitVec 32).toNat = 1920 from rfl]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem svb_addr {k : Nat} (hk : k < 36) :
    State.addr (L.svb + BitVec.ofNat 32 k) = L.SVA + BitVec.ofNat 64 k := by
  have := h.nc; have := h.slen; have hs := h.svb_toNat
  have e : State.addr L.svb = L.SVA := by
    apply BitVec.eq_of_toNat_eq
    have := L.scr.isLt
    rw [toNat_addr, hs, Lay.SVA, BitVec.toNat_add, toNat_addr, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 128 * (L.r.toNat + 15)) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [addr_add (by omega), e]

/-- A word of our stack arguments, as `ldr t, [sp, #off]` reads it. -/
theorem arg_addr {k : Nat} (hk : k + 4 ≤ 36) :
    State.addr (L.sp + BitVec.ofNat 32 k) = State.addr L.sp + BitVec.ofNat 64 k :=
  addr_add (by have := h.nA; omega)

end Lay.Ok

/-! ## What the calls cannot change -/

/-- Our stack arguments, as `ldr t, [sp, #off]` reads them. -/
structure Args (L : Lay) (m : Mem) : Prop where
  r : m.readW (State.addr L.sp + BitVec.ofNat 64 0) 32 = L.r
  b : m.readW (State.addr L.sp + BitVec.ofNat 64 4) 32 = L.b
  blen : m.readW (State.addr L.sp + BitVec.ofNat 64 8) 32 = L.blen
  v : m.readW (State.addr L.sp + BitVec.ofNat 64 12) 32 = L.v
  vlen : m.readW (State.addr L.sp + BitVec.ofNat 64 16) 32 = L.vlen
  scr : m.readW (State.addr L.sp + BitVec.ofNat 64 20) 32 = L.scr
  slen : m.readW (State.addr L.sp + BitVec.ofNat 64 24) 32 = L.slen
  out : m.readW (State.addr L.sp + BitVec.ofNat 64 28) 32 = L.out
  ol : m.readW (State.addr L.sp + BitVec.ofNat 64 32) 32 = L.ol

/-- The save area holds `g`'s `r4`–`r11` and `lr`. -/
structure Saved (L : Lay) (g : Reg → BitVec 32) (m : Mem) : Prop where
  r4 : m.readW (L.SVA + BitVec.ofNat 64 0) 32 = g .r4
  r5 : m.readW (L.SVA + BitVec.ofNat 64 4) 32 = g .r5
  r6 : m.readW (L.SVA + BitVec.ofNat 64 8) 32 = g .r6
  r7 : m.readW (L.SVA + BitVec.ofNat 64 12) 32 = g .r7
  r8 : m.readW (L.SVA + BitVec.ofNat 64 16) 32 = g .r8
  r9 : m.readW (L.SVA + BitVec.ofNat 64 20) 32 = g .r9
  r10 : m.readW (L.SVA + BitVec.ofNat 64 24) 32 = g .r10
  r11 : m.readW (L.SVA + BitVec.ofNat 64 28) 32 = g .r11
  lr : m.readW (L.SVA + BitVec.ofNat 64 32) 32 = g .lr

/-- Our stack arguments survive changes to memory that miss them. -/
theorem Args.frame {L : Lay} {m m' : Mem} {rs : List Region} (hk : Args L m)
    (hf : Frame rs m m') (ha : ∀ R ∈ rs, L.ARGS.Disjoint R) : Args L m' := by
  have ka : ∀ d, d + 4 ≤ 36 → m'.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 =
      m.readW (State.addr L.sp + BitVec.ofNat 64 d) 32 := fun d hd =>
    hf.readW (r := L.ARGS) (Offset.contains_base _ (by omega) (by omega))
      (fun R hR => ha R hR) (by decide)
  exact ⟨(ka 0 (by omega)).trans hk.r, (ka 4 (by omega)).trans hk.b, (ka 8 (by omega)).trans hk.blen,
    (ka 12 (by omega)).trans hk.v, (ka 16 (by omega)).trans hk.vlen, (ka 20 (by omega)).trans hk.scr,
    (ka 24 (by omega)).trans hk.slen, (ka 28 (by omega)).trans hk.out, (ka 32 (by omega)).trans hk.ol⟩

/-- So does the save area. -/
theorem Saved.frame {L : Lay} {g : Reg → BitVec 32} {m m' : Mem} {rs : List Region} (hk : Saved L g m)
    (hf : Frame rs m m') (hs : ∀ R ∈ rs, L.SV.Disjoint R) : Saved L g m' := by
  have ks : ∀ d, d + 4 ≤ 36 → m'.readW (L.SVA + BitVec.ofNat 64 d) 32 =
      m.readW (L.SVA + BitVec.ofNat 64 d) 32 := fun d hd =>
    hf.readW (r := L.SV) (Offset.contains_base _ (by omega) (by omega))
      (fun R hR => hs R hR) (by decide)
  exact ⟨(ks 0 (by omega)).trans hk.r4, (ks 4 (by omega)).trans hk.r5, (ks 8 (by omega)).trans hk.r6,
    (ks 12 (by omega)).trans hk.r7, (ks 16 (by omega)).trans hk.r8, (ks 20 (by omega)).trans hk.r9,
    (ks 24 (by omega)).trans hk.r10, (ks 28 (by omega)).trans hk.r11, (ks 32 (by omega)).trans hk.lr⟩

/-! ## Between the calls -/

/-- The state between the calls: `g` holds the registers on entry, `m₀` the
memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.sp
  r5 : t.gpr .r5 = L.b + BitVec.ofNat 32 (L.blen.toNat * 128)
  r6 : t.gpr .r6 = L.r
  r7 : t.gpr .r7 = L.scr
  r8 : t.gpr .r8 = L.pw
  r9 : t.gpr .r9 = L.pwl
  args : Args L t.mem
  saved : Saved L g t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.BB, L.VV, L.SC, L.OUT]

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
    stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, s.sp⟩

theorem lay_args (s : State) : (lay s).ARGS = ⟨stackArgAddr s 0, 36⟩ := by
  simp only [Lay.ARGS, lay, stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptArm.pre s) : (lay s).Ok := by
  obtain ⟨h40, h36, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea := lay_args s
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, h40, h36, rpos, bmod, vmod, hval, olb, slen⟩

end VG.Proof.Scrypt.Arm.Whole
