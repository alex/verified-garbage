import VerifiedGarbage.Impl.Scrypt.X86_64.Scrypt
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scrypt on x86-64: where everything is

Untrusted: everything here is checked by Lean. The contract the proof is
written against (`scryptX86_64`), the function's buffers and the 88 bytes of
stack below its return address, from `B` up (`Lay`): the 32 bytes the calls
use, then the frame (56 bytes, from `B + 32`: PBKDF2's two stack arguments,
the next block, then the password, its length, `r` and `b`). Our own stack
arguments are at `B + 96`. `Ctx` is what holds between the frame's push and
pop: the permissions, `rsp`, the callee-saved registers, the words the
calls cannot change (`Kept`), and that memory changed only in the writable
buffers and the stack. `call_ok` runs a call of verified code in such a
state.
-/

namespace VG.Proof.Scrypt

open VG.X86_64 in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. x86-64 contract for
`vg_scrypt(password = rdi, password_len = rsi, salt = rdx, salt_len = rcx,
r = r8, b = r9, blen, v, vlen, scratch, slen, out, out_len)`, the last seven
on the stack, with 88 bytes of stack below the return address. -/
def scryptX86_64 : Contract X86_64.isa where
  pre s :=
    let blen := stackArg s 0
    let v := stackArg s 1
    let vlen := stackArg s 2
    let sc := stackArg s 3
    let slen := stackArg s 4
    let out := stackArg s 5
    let ol := stackArg s 6
    let r := (s.gpr .r8).toNat
    let pwR : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let saltR : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let bR : Region := ⟨s.gpr .r9, blen.toNat * 128⟩
    let vR : Region := ⟨v, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 56⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 88, 88⟩
    88 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    ret.Disjoint pwR ∧ ret.Disjoint saltR ∧ ret.Disjoint bR ∧ ret.Disjoint vR ∧ ret.Disjoint scR ∧
    ret.Disjoint outR ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + blen.toNat * 128 ≤ 2 ^ 64 ∧ v.toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ blen.toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r (blen.toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .r8).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((stackArg s 2).toNat / r) r
      ((stackArg s 0).toNat / r) (stackArg s 6).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 5) (stackArg s 6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
    stackArg s₁ 6 = stackArg s₂ 6 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat) (s₁.gpr .r8).toNat
        ((stackArg s₁ 0).toNat / (s₁.gpr .r8).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .r8).toNat ((stackArg s₁ 2).toNat / (s₁.gpr .r8).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat) (s₂.gpr .r8).toNat
        ((stackArg s₂ 0).toNat / (s₂.gpr .r8).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .r8).toNat ((stackArg s₂ 2).toNat / (s₂.gpr .r8).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64

/-- The arguments and the lowest byte of the stack used (`rsp - 88` on entry). -/
structure Lay where
  pw : Addr
  pwl : BitVec 64
  salt : Addr
  sl : BitVec 64
  r : BitVec 64
  b : Addr
  blen : BitVec 64
  v : Addr
  vlen : BitVec 64
  scr : Addr
  slen : BitVec 64
  out : Addr
  ol : BitVec 64
  B : Addr

namespace Lay

variable (L : Lay)

abbrev PW : Region := ⟨L.pw, L.pwl.toNat⟩
abbrev SALT : Region := ⟨L.salt, L.sl.toNat⟩
abbrev BB : Region := ⟨L.b, L.blen.toNat * 128⟩
abbrev VV : Region := ⟨L.v, L.vlen.toNat * 128⟩
abbrev SC : Region := ⟨L.scr, L.slen.toNat * 128⟩
abbrev OUT : Region := ⟨L.out, L.ol.toNat⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 96, 56⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 88⟩
/-- The frame. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 32, 56⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 88, 8⟩

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
  np : L.pw.toNat + L.pwl.toNat ≤ 2 ^ 64
  ns : L.salt.toNat + L.sl.toNat ≤ 2 ^ 64
  nb : L.b.toNat + L.blen.toNat * 128 ≤ 2 ^ 64
  nv : L.v.toNat + L.vlen.toNat * 128 ≤ 2 ^ 64
  nc : L.scr.toNat + L.slen.toNat * 128 ≤ 2 ^ 64
  no : L.out.toNat + L.ol.toNat ≤ 2 ^ 64
  nB : L.B.toNat + 152 ≤ 2 ^ 64
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

theorem within_fr (B : Addr) {d n : Nat} (h₁ : 32 ≤ d) (h₂ : d + n ≤ 88) :
    Within ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B + BitVec.ofNat 64 32, 56⟩ :=
  ⟨d - 32, by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h₁], by simp only; omega⟩

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

/-- The stack and the stack arguments do not wrap around. -/
theorem nB' : L.B.toNat + 152 ≤ 2 ^ 64 := h.nB

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_buf {d n : Nat} (h₁ : d + n ≤ 88) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hr
  · exact (h.kv.sub_left hs).sub_right hr
  · exact (h.kc.sub_left hs).sub_right hr
  · exact (h.ko.sub_left hs).sub_right hr

/-- A range in our stack arguments is disjoint from one in a writable buffer. -/
theorem args_buf {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 152) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.ARGS := Offset.sub _ h₁ (by omega)
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.ba.symm.sub_left hs).sub_right hr
  · exact (h.va.symm.sub_left hs).sub_right hr
  · exact (h.ca.symm.sub_left hs).sub_right hr
  · exact (h.oa.symm.sub_left hs).sub_right hr

end Lay.Ok

/-! ## What the calls cannot change -/

/-- The words in the frame and our stack arguments that stay as they are
between the frame's push and pop. -/
structure Kept (L : Lay) (m : Mem) : Prop where
  pw : m.readW (L.B + BitVec.ofNat 64 56) 64 = L.pw
  pwl : m.readW (L.B + BitVec.ofNat 64 64) 64 = L.pwl
  r : m.readW (L.B + BitVec.ofNat 64 72) 64 = L.r
  b : m.readW (L.B + BitVec.ofNat 64 80) 64 = L.b
  blen : m.readW (L.B + BitVec.ofNat 64 96) 64 = L.blen
  v : m.readW (L.B + BitVec.ofNat 64 104) 64 = L.v
  vlen : m.readW (L.B + BitVec.ofNat 64 112) 64 = L.vlen
  scr : m.readW (L.B + BitVec.ofNat 64 120) 64 = L.scr
  out : m.readW (L.B + BitVec.ofNat 64 136) 64 = L.out
  ol : m.readW (L.B + BitVec.ofNat 64 144) 64 = L.ol

/-- The kept words survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {m m' : Mem} {rs : List Region} (hk : Kept L m) (hf : Frame rs m m')
    (hd : ∀ d, (56 ≤ d ∧ d + 8 ≤ 88) ∨ (96 ≤ d ∧ d + 8 ≤ 152) → ∀ R ∈ rs,
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R) : Kept L m' := by
  have k : ∀ d, (56 ≤ d ∧ d + 8 ≤ 88) ∨ (96 ≤ d ∧ d + 8 ≤ 152) →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 56 (by omega)).trans hk.pw, (k 64 (by omega)).trans hk.pwl, (k 72 (by omega)).trans hk.r,
    (k 80 (by omega)).trans hk.b, (k 96 (by omega)).trans hk.blen, (k 104 (by omega)).trans hk.v,
    (k 112 (by omega)).trans hk.vlen, (k 120 (by omega)).trans hk.scr,
    (k 136 (by omega)).trans hk.out, (k 144 (by omega)).trans hk.ol⟩

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` are the registers on
entry, `m₀` the memory. (No instruction loads MXCSR: see `abiPreserved_of_exec`.) -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.FR, L.BB, L.VV, L.SC, L.OUT]
  rsp : t.gpr .rsp = L.B + BitVec.ofNat 64 32
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  kept : Kept L t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

/-- `B + 32 - 8 = B + 24`. -/
theorem sub8 (B : Addr) : B + BitVec.ofNat 64 32 - 8 = B + BitVec.ofNat 64 24 := by
  bv_omega

/-- The stack a call from `rsp = B + 32` uses, if it nests calls at most four deep. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 32) :
    Region.Sub (below (B + BitVec.ofNat 64 32) m) ⟨B, 32⟩ := by
  have : B + BitVec.ofNat 64 32 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (32 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 32) (a := m) (b := 32) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 32 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-- The regions a callee may be given. -/
abbrev Lay.regions (L : Lay) : List Region := [L.PW, L.SALT, L.ARGS, L.FR, L.BB, L.VV, L.SC, L.OUT]

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

theorem covers {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem} {t : State}
    (hc : Ctx L g m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; simpa using hR, hw⟩
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- A call of verified code (see `WP.call`), which nests calls at most three
times more and is given regions within ours to read, and within the
writable buffers to write: afterwards `Ctx` holds again, memory changed only
within what it writes and the 32 bytes below `rsp`, and the callee's
postcondition holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 3) {t : State} (hc : Ctx L g m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g m₀ s' → Frame (wr ++ [⟨L.B, 32⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.call hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost => ?_
  have hf' : Frame (wr ++ [⟨L.B, 32⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact below_call_sub _ (by omega)
  have hnB := hL.nB
  -- The regions the call may change miss the kept words.
  have hdisj : ∀ d, (56 ≤ d ∧ d + 8 ≤ 88) ∨ (96 ≤ d ∧ d + 8 ≤ 152) → ∀ R ∈ wr ++ [⟨L.B, 32⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R := by
    intro d hdd R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨R', hR', hs⟩ := (hwsub R hR).sub
      rcases hdd with hdd | hdd
      · exact hL.stk_buf (by omega) hR' hs
      · exact hL.args_buf (by omega) (by omega) hR' hs
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hc.kept.frame hf' hdisj, hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨R', hR', hs⟩ := (hwsub r hr).sub
      rcases hR' with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 32) (k := 88) (by omega)
      simpa using this

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, stackArg s 0, stackArg s 1,
    stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    s.gpr .rsp - BitVec.ofNat 64 88⟩

theorem lay_ret (s : State) : (lay s).B + BitVec.ofNat 64 88 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (lay s).B + BitVec.ofNat 64 96 = stackArgAddr s 0 := by
  simp only [lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptX86_64.pre s) : (lay s).Ok := by
  obtain ⟨h88, h64, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    rp, rs, rb, rv, rc, ro, kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval,
    olb, slen⟩ := h
  have e : (lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, lay_ret]
  have ea : (lay s).ARGS = ⟨stackArgAddr s 0, 56⟩ := by simp only [Lay.ARGS, lay_args]
  have nB : (lay s).B.toNat + 152 ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat (s.gpr .rsp) 88]
    omega
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    e ▸ rp, e ▸ rs, e ▸ rb, e ▸ rv, e ▸ rc, e ▸ ro, kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, nB,
    rpos, bmod, vmod, hval, olb, slen⟩

/-! ## The frame's push -/

/-- The registers the frame's push stores. -/
abbrev pushRs : List Reg := [.r9, .r8, .rsi, .rdi, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 7) = sp - BitVec.ofNat 64 88 + BitVec.ofNat 64 32 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 4) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 88 + BitVec.ofNat 64 (80 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem arg_slot (s : State) (i : Nat) (hi : i < 7) :
    stackArgAddr s i = (lay s).B + BitVec.ofNat 64 (96 + 8 * i) := by
  simp only [stackArgAddr, lay]
  have : 8 * (i + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : Proof.Scrypt.scryptX86_64.pre s) :
    Ctx (lay s) s.gpr s.mem (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 7 ≤ _; have := h.1; omega
  have hL := lay_ok h
  have hnB := hL.nB
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 4), (pushed pushRs s).mem.readW ((lay s).B + BitVec.ofNat 64 (80 - 8 * j)) 64 =
      s.gpr (pushRs[j]'(by show j < 7; omega)) := fun j hj => by
    rw [← hw j (by show j < 7; omega)]; simp only [lay]; rw [push_slot _ j hj]; rfl
  have hfr : (⟨s.gpr .rsp - BitVec.ofNat 64 (8 * pushRs.length), 8 * pushRs.length⟩ : Region) =
      (lay s).FR := by
    simp only [List.length_cons, List.length_nil, Lay.FR, lay]; rw [push_base]
  rw [hfr] at hf
  have ha : ∀ i, i < 7 → (pushed pushRs s).mem.readW ((lay s).B + BitVec.ofNat 64 (96 + 8 * i)) 64 =
      stackArg s i := fun i hi => by
    rw [stackArg, arg_slot s i hi]
    refine hf.readW (Region.contains_self _ _) (fun R hR => ?_) (by decide)
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨by rw [pushed_rd, h.2.2.1, ← lay_args]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    ⟨hw' 3 (by omega), hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega),
      ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 5 (by omega),
      ha 6 (by omega)⟩, ?_⟩
  · rw [pushed_wr, hfr, h.2.2.2.1]; rfl
  · rw [pushed_rsp]; simp only [List.length_cons, List.length_nil, lay]; rw [push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(lay s).STK, by simp, Offset.sub_base _ (by omega)⟩

end VG.Proof.Scrypt.X86_64.Whole
