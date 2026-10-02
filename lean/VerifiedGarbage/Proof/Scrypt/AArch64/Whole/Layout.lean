import VerifiedGarbage.Impl.Scrypt.AArch64.Scrypt
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# scrypt on AArch64: where everything is

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Scrypt/X86_64/Whole/Layout.lean`): the contract the proof is written
against (`scryptAArch64`), the function's buffers and the 96 bytes of stack
below the stack pointer, from `B` up (`Lay`): the 16 bytes the calls use,
the 64-byte frame (from `B + 16`: the next block, then the password, its
length, `r`, `b`, `blen` and `v`), then the frame holding our return address
(`B + 80`). Our stack arguments are at `B + 96`. `Ctx` is what holds between
the frames' pushes and pops, and `call_ok` runs a call of verified code in
such a state.
-/

namespace VG.Proof.Scrypt

open VG.AArch64 in
/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it. AArch64 contract for
`vg_scrypt(password = x0, password_len = x1, salt = x2, salt_len = x3, r = x4,
b = x5, blen = x6, v = x7, vlen, scratch, slen, out, out_len)`, the last five
on the stack, with 96 bytes of stack below the stack pointer. -/
def scryptAArch64 : Contract AArch64.isa where
  pre s :=
    let vlen := stackArg s 0
    let sc := stackArg s 1
    let slen := stackArg s 2
    let out := stackArg s 3
    let ol := stackArg s 4
    let r := (s.gpr .x4).toNat
    let pwR : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let saltR : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let bR : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat * 128⟩
    let vR : Region := ⟨s.gpr .x7, vlen.toNat * 128⟩
    let scR : Region := ⟨sc, slen.toNat * 128⟩
    let outR : Region := ⟨out, ol.toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let stack : Region := ⟨s.sp - BitVec.ofNat 64 96, 96⟩
    96 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 64 ∧
    s.rd = [pwR, saltR, args] ∧ s.wr = [bR, vR, scR, outR] ∧
    pwR.Disjoint bR ∧ pwR.Disjoint vR ∧ pwR.Disjoint scR ∧ pwR.Disjoint outR ∧
    saltR.Disjoint bR ∧ saltR.Disjoint vR ∧ saltR.Disjoint scR ∧ saltR.Disjoint outR ∧
    bR.Disjoint vR ∧ bR.Disjoint scR ∧ bR.Disjoint outR ∧ bR.Disjoint args ∧
    vR.Disjoint scR ∧ vR.Disjoint outR ∧ vR.Disjoint args ∧
    scR.Disjoint outR ∧ scR.Disjoint args ∧ outR.Disjoint args ∧
    stack.Disjoint pwR ∧ stack.Disjoint saltR ∧ stack.Disjoint bR ∧ stack.Disjoint vR ∧
    stack.Disjoint scR ∧ stack.Disjoint outR ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + vlen.toNat * 128 ≤ 2 ^ 64 ∧
    sc.toNat + slen.toNat * 128 ≤ 2 ^ 64 ∧ out.toNat + ol.toNat ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .x6).toNat % r = 0 ∧ vlen.toNat % r = 0 ∧
    Spec.Scrypt.valid (vlen.toNat / r) r ((s.gpr .x6).toNat / r) ol.toNat ∧
    ol.toNat ≤ (2 ^ 32 - 1) * 32 ∧ slen.toNat = r + 16
  post s s' :=
    let r := (s.gpr .x4).toNat
    Spec.Scrypt.scrypt (Spec.Scrypt.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
      (Spec.Scrypt.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ((stackArg s 0).toNat / r) r
      ((s.gpr .x6).toNat / r) (stackArg s 4).toNat =
      some (Spec.Scrypt.bytesAt s'.mem (stackArg s 3) (stackArg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    stackArg s₁ 4 = stackArg s₂ 4 ∧ s₁.sp = s₂.sp ∧
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat)
        (Spec.Scrypt.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat) (s₁.gpr .x4).toNat
        ((s₁.gpr .x6).toNat / (s₁.gpr .x4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₁.gpr .x4).toNat ((stackArg s₁ 0).toNat / (s₁.gpr .x4).toNat)) =
    (Spec.Scrypt.blocks (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat)
        (Spec.Scrypt.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat) (s₂.gpr .x4).toNat
        ((s₂.gpr .x6).toNat / (s₂.gpr .x4).toNat)).flatMap
      (Spec.Scrypt.roMixIndices (s₂.gpr .x4).toNat ((stackArg s₂ 0).toNat / (s₂.gpr .x4).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64

/-- The arguments, and the lowest byte of the stack used (`sp - 96` on
entry). -/
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
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 96, 40⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, 96⟩
/-- The frames: our words, and our return address. -/
abbrev FR : Region := ⟨L.B + BitVec.ofNat 64 16, 64⟩
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 80, 16⟩

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
  nB : L.B.toNat + 136 ≤ 2 ^ 64
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

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

/-- A range in the stack is disjoint from one in a writable buffer. -/
theorem stk_buf {d n : Nat} (h₁ : d + n ≤ 96) {R : Region}
    (hR : R = L.BB ∨ R = L.VV ∨ R = L.SC ∨ R = L.OUT) {r : Region} (hr : Region.Sub r R) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, n⟩ L.STK := Offset.sub_base _ h₁
  rcases hR with rfl | rfl | rfl | rfl
  · exact (h.kb.sub_left hs).sub_right hr
  · exact (h.kv.sub_left hs).sub_right hr
  · exact (h.kc.sub_left hs).sub_right hr
  · exact (h.ko.sub_left hs).sub_right hr

/-- A range in our stack arguments is disjoint from one in a writable buffer. -/
theorem args_buf {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 136) {R : Region}
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

/-- The words in the frames and our stack arguments that stay as they are
between the frames' pushes and pops, with our return address `lr`. -/
structure Kept (L : Lay) (lr : BitVec 64) (m : Mem) : Prop where
  pw : m.readW (L.B + BitVec.ofNat 64 24) 64 = L.pw
  pwl : m.readW (L.B + BitVec.ofNat 64 32) 64 = L.pwl
  r : m.readW (L.B + BitVec.ofNat 64 40) 64 = L.r
  b : m.readW (L.B + BitVec.ofNat 64 48) 64 = L.b
  blen : m.readW (L.B + BitVec.ofNat 64 56) 64 = L.blen
  v : m.readW (L.B + BitVec.ofNat 64 64) 64 = L.v
  lr : m.readW (L.B + BitVec.ofNat 64 80) 64 = lr
  vlen : m.readW (L.B + BitVec.ofNat 64 96) 64 = L.vlen
  scr : m.readW (L.B + BitVec.ofNat 64 104) 64 = L.scr
  out : m.readW (L.B + BitVec.ofNat 64 120) 64 = L.out
  ol : m.readW (L.B + BitVec.ofNat 64 128) 64 = L.ol

/-- The kept words survive changes to memory that miss them. -/
theorem Kept.frame {L : Lay} {lr : BitVec 64} {m m' : Mem} {rs : List Region} (hk : Kept L lr m)
    (hf : Frame rs m m')
    (hd : ∀ d, (24 ≤ d ∧ d + 8 ≤ 96) ∨ (96 ≤ d ∧ d + 8 ≤ 136) → ∀ R ∈ rs,
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R) : Kept L lr m' := by
  have k : ∀ d, (24 ≤ d ∧ d + 8 ≤ 96) ∨ (96 ≤ d ∧ d + 8 ≤ 136) →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d hdd => hf.readW (Region.contains_self _ _) (hd d hdd) (by decide)
  exact ⟨(k 24 (by omega)).trans hk.pw, (k 32 (by omega)).trans hk.pwl, (k 40 (by omega)).trans hk.r,
    (k 48 (by omega)).trans hk.b, (k 56 (by omega)).trans hk.blen, (k 64 (by omega)).trans hk.v,
    (k 80 (by omega)).trans hk.lr, (k 96 (by omega)).trans hk.vlen, (k 104 (by omega)).trans hk.scr,
    (k 120 (by omega)).trans hk.out, (k 128 (by omega)).trans hk.ol⟩

/-! ## Between the frames' pushes and pops -/

/-- The state between the frames' pushes and pops: `g` and `vv` are the
registers on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.B + BitVec.ofNat 64 16
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  kept : Kept L (g .x30) t.mem
  frame : Frame [L.BB, L.VV, L.SC, L.OUT, L.STK] m₀ t.mem

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

theorem covers {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {rd wr : List Region}
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · obtain ⟨R, hR, hw⟩ := hsub r hr
    refine ⟨R, ?_, hw⟩
    rw [hc.rd, hc.wr]
    simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr]
    rcases hwsub r hr with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

/-- The stack a call from `sp = B + 16` uses, if it pushes at most one frame. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 16) :
    Region.Sub (below (B + BitVec.ofNat 64 16) m) ⟨B, 16⟩ := by
  have : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (16 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 16) (a := m) (b := 16) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-- A call of verified code (see `WP.callFV`), which pushes at most one frame
and is given regions within ours to read, and within the writable buffers to
write: afterwards `Ctx` holds again, memory changed only within what it
writes and the 16 bytes below `sp`, and the callee's postcondition holds. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1) {t : State} (hc : Ctx L g vv m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.regions, Within r R) (hwsub : ∀ r ∈ wr, InBuf L r)
    {Q : State → Prop}
    (hQ : ∀ s', Ctx L g vv m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      k.post (t.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨hcov, hcovw⟩ := covers hc hsub hwsub
  refine WP.callFV hv hpre hcov hcovw (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.sp]
      exact below_call_sub _ (by omega)
  have hnB := hL.nB
  -- The regions the call may change miss the kept words.
  have hdisj : ∀ d, (24 ≤ d ∧ d + 8 ≤ 96) ∨ (96 ≤ d ∧ d + 8 ≤ 136) → ∀ R ∈ wr ++ [⟨L.B, 16⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ R := by
    intro d hdd R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨R', hR', hs⟩ := (hwsub R hR).sub
      rcases hdd with hdd | hdd
      · exact hL.stk_buf (by omega) hR' hs
      · exact hL.args_buf (by omega) (by omega) hR' hs
    · simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (by omega) (by omega)
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'), fun r hr => (hvs r hr).trans (hc.vs r hr),
    hc.kept.frame hf' hdisj, hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hpost
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨R', hR', hs⟩ := (hwsub r hr).sub
    rcases hR' with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
    · exact ⟨_, by simp, hs⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Region.sub_prefix (by omega)⟩

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    s.sp - BitVec.ofNat 64 96⟩

theorem lay_top (s : State) : (lay s).B + BitVec.ofNat 64 96 = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (lay s).B + BitVec.ofNat 64 96 = stackArgAddr s 0 := by
  simp only [lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : Proof.Scrypt.scryptAArch64.pre s) : (lay s).Ok := by
  obtain ⟨h96, h40, -, -, pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ba, vc, vo, va, co, ca, oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, rpos, bmod, vmod, hval, olb, slen⟩ := h
  have ea : (lay s).ARGS = ⟨stackArgAddr s 0, 40⟩ := by simp only [Lay.ARGS, lay_args]
  have nB : (lay s).B.toNat + 136 ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat s.sp 96]
    omega
  exact ⟨pb, pv, pc, po, sb, sv, sc, so, bv, bc, bo, ea ▸ ba, vc, vo, ea ▸ va, co, ea ▸ ca, ea ▸ oa,
    kp, ks, kb, kv, kc, ko, np, ns, nb, nv, nc, no, nB, rpos, bmod, vmod, hval, olb, slen⟩

end VG.Proof.Scrypt.AArch64.Whole
