import VerifiedGarbage.Impl.Pbkdf2.Whole.Arm
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Init
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the functions it calls, and its parts

Untrusted: everything here is checked by Lean. As on x86
(`Proof/Pbkdf2/Whole/X86/Common.lean`): `FnsOK F` is what the proof knows
of the functions `pbkdf2` calls (the hash function's streaming functions,
`VG.Proof.Hmac.Generic.Arm.HashOK`, and HMAC's `init` and `finalize` and
PBKDF2's `iterate`, sound for their shared contracts with 16 bytes of
stack). Then the precondition of `pbkdf2` (`Pre`, from the shared contract
with 24 bytes of stack), the parts of its `scratch`, and what every piece
of it keeps (`KR`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Hmac.Generic.Arm (Hash scrAt)
open VG.Proof.Hmac.Generic.Arm (HashOK SavedRegs saveR)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open VG.Proof.MdStream.Arm (Upd)
open Spec.Sha256 (bytesAt)

/-- The functions `pbkdf2` calls, verified. -/
structure FnsOK (F : Fns) where
  hH : HashOK F.H
  Wi : Nat
  Wf : Nat
  Wt : Nat
  hi : Sound F.hiC (Spec.Hmac.initContract hH.SH Wi Arm.abi 16)
  hf : Sound F.hfC (Spec.Hmac.finalizeContract hH.SH Wf Arm.abi 16)
  it : Sound F.itC (Spec.Pbkdf2.iterateContract hH.SH Wt Arm.abi 16)
  hiSt : armStack F.hiC ≤ 16
  hfSt : armStack F.hfC ≤ 16
  itSt : armStack F.itC ≤ 16
  hWi : Wi ≤ F.W
  hWf : Wf ≤ F.W
  hWt : Wt ≤ F.W
  hWH : F.H.W ≤ F.W
  /-- The digest is no longer than a block (so that the digest of a long
  password is a key `init` takes). -/
  hDB : F.H.D ≤ F.H.B
  /-- The streaming state holds a block. -/
  hBS : F.H.B ≤ F.H.S
  /-- Our buffers fit in the `8 S` bytes after the working space. -/
  fits : 40 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S
  /-- And `scratch` is within reach of an immediate offset. -/
  reach : (F.W + F.H.S) * 8 ≤ 4096
  /-- The immediates the code compares and adds. -/
  encB1 : encodable (BitVec.ofNat 32 (F.H.B + 1)) = true
  encB : encodable (BitVec.ofNat 32 F.H.B) = true
  encB4 : encodable (BitVec.ofNat 32 (F.H.B + 4)) = true
  encD : encodable (BitVec.ofNat 32 F.H.D) = true

variable {F : Fns}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : BitVec 32 := s₀.gpr .r0
abbrev pwl : Nat := (s₀.gpr .r1).toNat
abbrev salt : BitVec 32 := s₀.gpr .r2
abbrev sl : Nat := (s₀.gpr .r3).toNat
/-- The iteration count. -/
abbrev cc : Nat := (stackArg s₀ 0).toNat
abbrev out : BitVec 32 := stackArg s₀ 1
abbrev ol : Nat := (stackArg s₀ 2).toNat
abbrev scr : BitVec 32 := stackArg s₀ 3
abbrev pwR : Region := ⟨State.addr (pw s₀), pwl s₀⟩
abbrev saltR : Region := ⟨State.addr (salt s₀), sl s₀⟩
abbrev outR : Region := ⟨State.addr (out s₀), ol s₀⟩
abbrev scR (F : Fns) : Region := ⟨State.addr (scr s₀), (F.W + F.H.S) * 8⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev stkR : Region := stk s₀
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := State.addr (scr s₀) + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨State.addr (scr s₀), k⟩

end

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

/-- The size of `scratch`. -/
abbrev _root_.VG.Impl.Pbkdf2.Whole.Arm.Fns.L8 (F : Fns) : Nat := (F.W + F.H.S) * 8

/-- The precondition. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  sp24 : 24 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 16 ≤ 2 ^ 32
  rd : s₀.rd = [pwR s₀, saltR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scR s₀ F]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR s₀ F)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR s₀ F)
  o_s : (outR s₀).Disjoint (scR s₀ F)
  o_a : (outR s₀).Disjoint (argR s₀)
  s_a : (scR s₀ F).Disjoint (argR s₀)
  b_pw : (stkR s₀).Disjoint (pwR s₀)
  b_sa : (stkR s₀).Disjoint (saltR s₀)
  b_o : (stkR s₀).Disjoint (outR s₀)
  b_s : (stkR s₀).Disjoint (scR s₀ F)
  b_a : (stkR s₀).Disjoint (argR s₀)
  npw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 32
  nsa : (salt s₀).toNat + sl s₀ ≤ 2 ^ 32
  no : (out s₀).toNat + ol s₀ ≤ 2 ^ 32
  nsc : (scr s₀).toNat + F.L8 ≤ 2 ^ 32
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * F.H.D

theorem pre_of (hF : FnsOK F) {s₀ : State}
    (h : (Spec.Pbkdf2.pbkdf2Contract hF.hH.SH (F.W + F.H.S) Arm.abi 24).pre s₀) : Pre F s₀ := by
  sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  have hD := hF.hH.hD
  rw [hD] at h21
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-! ## The layout of `scratch` -/

/-- The sizes, as facts about natural numbers. -/
structure Sizes (F : Fns) : Prop where
  B : 0 < F.H.B ∧ F.H.B ≤ 128
  S : 0 < F.H.S ∧ F.H.S ≤ 256
  D : 0 < F.H.D ∧ F.H.D ≤ F.H.F ∧ F.H.F ≤ 64
  W : F.H.W ≤ F.W
  DB : F.H.D ≤ F.H.B
  BS : F.H.B ≤ F.H.S
  fits : 40 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S
  reach : F.L8 ≤ 4096
  encB1 : encodable (BitVec.ofNat 32 (F.H.B + 1)) = true
  encB : encodable (BitVec.ofNat 32 F.H.B) = true
  encB4 : encodable (BitVec.ofNat 32 (F.H.B + 4)) = true
  encD : encodable (BitVec.ofNat 32 F.H.D) = true

theorem FnsOK.sizes (hF : FnsOK F) : Sizes F :=
  ⟨⟨hF.hH.hB0, hF.hH.hBB⟩, ⟨hF.hH.hS0, hF.hH.hSB⟩, ⟨hF.hH.hD0, hF.hH.hDF, hF.hH.hF⟩, hF.hWH, hF.hDB, hF.hBS,
    hF.fits, hF.reach, hF.encB1, hF.encB, hF.encB4, hF.encD⟩

/-- Where the parts of `scratch` are. -/
theorem layout : F.L.buf = 8 * F.W + 36 ∧ F.st0O = 8 * F.W + 36 ∧ F.st1O = 8 * F.W + 36 + F.H.S ∧
    F.stSO = 8 * F.W + 36 + 2 * F.H.S ∧ F.stWO = 8 * F.W + 36 + 3 * F.H.S ∧
    F.uO = 8 * F.W + 36 + 4 * F.H.S ∧ F.tO = 8 * F.W + 36 + 4 * F.H.S + F.H.D ∧
    F.hkO = 8 * F.W + 36 + 4 * F.H.S + 2 * F.H.D ∧ F.intO = 8 * F.W + 36 + 4 * F.H.S + 2 * F.H.D + F.H.F := by
  dsimp only [Fns.st0O, Fns.st1O, Fns.stSO, Fns.stWO, Fns.uO, Fns.tO, Fns.hkO, Fns.intO, Fns.L, Hash.buf]
  omega

theorem end_le (hz : Sizes F) : F.intO + 4 ≤ F.L8 := by
  have := layout (F := F); have := hz.fits; simp only [Fns.L8]; omega

/-- The save area of our caller's registers. -/
abbrev svR (F : Fns) (s₀ : State) : Region := saveR F.L (scr s₀)

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < F.L8) : State.addr (dO s₀ o) = A s₀ o := by
  have := hp.nsc; exact addr_add (by omega)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (sR s₀ o n) (scR s₀ F) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := hz.reach; exact Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (lowR s₀ k) (sR s₀ b n) := by
  have := hz.reach; exact Offset.base_disjoint _ hk (by omega)

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (lowR s₀ k) (scR s₀ F) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (svR F s₀) (scR s₀ F) := by
  have := end_le hz; have := layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 36 ≤ F.L8; omega)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 36 ≤ o) (hon : o + n ≤ F.L8) : (svR F s₀).Disjoint (sR s₀ o n) := by
  have := hz.reach; exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega)) (by simp only [Fns.L]; omega) (by omega)

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (svR F s₀).Disjoint (lowR s₀ k) := by
  have := hz.reach; have := end_le hz; have := layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 36) (by simp only [Fns.L]; omega)
    (by simp only [Fns.L]; omega)).symm

omit hz in
theorem sc_mem : scR s₀ F ∈ s₀.wr := by rw [hp.wr]; simp

theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.L8) :
    InRegions s.wr (A s₀ o) n := by
  have := hz.reach
  exact ⟨scR s₀ F, by rw [hwr]; exact sc_mem hp, Offset.contains_base _ h (by omega)⟩

end

/-! ## What every piece keeps -/

/-- The regions everything writes: `out`, `scratch` and the stack below the stack pointer. -/
abbrev wrs (F : Fns) (s₀ : State) : List Region := [outR s₀, scR s₀ F, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = salt s₀
  r6 : s.gpr .r6 = s₀.gpr .r3
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs F.L (scr s₀) s₀ s.mem
  frame : Frame (wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r5, .r6, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

/-- The 24 bytes below the stack pointer, while `KR` holds. -/
theorem KR.stkE {s₀ s : State} (h : KR F s₀ s) : stk s = stkR s₀ := by
  show (⟨State.addr s.sp - 24, 24⟩ : Region) = ⟨State.addr s₀.sp - 24, 24⟩; rw [h.sp]

/-- `KR` survives changes to other registers, and to memory in `out`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (svR F s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs F s₀, Region.Sub r r') :
    KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r6,
    (hg _ (by simp)).trans h.r11, h.saved.frame F.L hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR F s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd {s₀ s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A write to a part of `scratch` after the save area. -/
theorem KR.write {s₀ s s' : State} (hz : Sizes F) (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {o n : Nat} (ho : 8 * F.W + 36 ≤ o)
    (hon : o + n ≤ F.L8) (hf : Frame [sR s₀ o n] s.mem s'.mem) : KR F s₀ s' :=
  h.keep hrd hwr hsp hg hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sv_disj hz ho hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after the save area, or
the working space, and the stack below the stack pointer. -/
theorem KR.call {s₀ s s' : State} (hp : Pre F s₀) (hz : Sizes F) (h : KR F s₀ s) {ws : List Region}
    (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨
      ∃ o n, r = sR s₀ o n ∧ 8 * F.W + 36 ≤ o ∧ o + n ≤ F.L8) : KR F s₀ s' := by
  have hL := end_le hz; have := layout (F := F)
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact sv_low hz hk
      · exact sv_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.b_s.sub_right (sv_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact ⟨scR s₀ F, by simp, low_sub (F := F) (by omega)⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

/-! ## The stack arguments and the inputs, while `KR` holds -/

section
variable {s₀ : State} (hp : Pre F s₀)
include hp

theorem argR_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨stackArgAddr s₀ i, 4⟩ (argR s₀) := by
  have e : stackArgAddr s₀ i = State.addr s₀.sp + BitVec.ofNat 64 (4 * i) := addr_add (by have := hp.spf; omega)
  have e0 : stackArgAddr s₀ 0 = State.addr s₀.sp := by simp [stackArgAddr]
  show Region.Sub ⟨stackArgAddr s₀ i, 4⟩ ⟨stackArgAddr s₀ 0, 16⟩
  rw [e, e0]
  exact Offset.sub_base _ (by omega)

theorem KR.stackArg {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 4) : stackArg s i = stackArg s₀ i := by
  have ea : stackArgAddr s i = stackArgAddr s₀ i := by simp only [stackArgAddr, hk.sp]
  show s.mem.readW (stackArgAddr s i) 32 = s₀.mem.readW (stackArgAddr s₀ i) 32
  rw [ea]
  refine hk.frame.readW (r := ⟨stackArgAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.o_a.symm.sub_left (argR_sub hp hi))
  · exact (hp.s_a.symm.sub_left (argR_sub hp hi))
  · exact (hp.b_a.symm.sub_left (argR_sub hp hi))

theorem argIn {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
  rw [hk.rd, hk.wr, hp.rd, hp.wr, hk.sp]
  have e : State.addr (s₀.sp + BitVec.ofNat 32 (4 * i)) = State.addr s₀.sp + BitVec.ofNat 64 (4 * i) :=
    addr_add (by have := hp.spf; omega)
  have e0 : stackArgAddr s₀ 0 = State.addr s₀.sp := by simp [stackArgAddr]
  refine ⟨argR s₀, by simp, ?_⟩
  show Region.Contains ⟨stackArgAddr s₀ 0, 16⟩ _ 4
  rw [e, e0]
  exact Offset.contains_base _ (by omega) (by omega)

/-- `ldr d, [sp, #4 i]`: stack argument `i`, while `KR` holds. -/
theorem wp_arg {s : State} (hk : KR F s₀ s) {d : Reg} {i : Nat} (hi : i < 4) {is : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' d (stackArg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp d (4 * i) :: is)) s Q :=
  VG.Proof.MdStream.Arm.wp_ldrSp (a := State.addr (s.sp + BitVec.ofNat 32 (4 * i))) (by omega) rfl
    (argIn hp hk hi) fun s' u => k s' (by rw [← hk.stackArg hp hi]; exact u)

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : KR F s₀ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep hk.frame hd hn

theorem KR.pwBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem (State.addr (pw s₀)) (pwl s₀) = bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.b_pw.symm) (by have := hp.npw; omega)

theorem KR.saltBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem (State.addr (salt s₀)) (sl s₀) = bytesAt s₀.mem (State.addr (salt s₀)) (sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.b_sa.symm) (by have := hp.nsa; omega)

end

/-! ## One instruction at a time -/

/-- `s'` is `s` with registers `d` set to `v` and `r12` changed. -/
structure Upd12 (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → r ≠ .r12 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem KR.upd12 {s₀ s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd12 s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r (fun e => hd (e ▸ hr)) (by
    simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    u.mem

/-- `d ← scratch + o` (through `r12`), while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : KR F s₀ s) {d : Reg} {o : Nat} (ho : o < 2 ^ 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd12 s s' d (dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (scrAt d o ++ rest)) s Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine Hmac.Generic.Arm.wp_movw fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _)
    fun s₂ u₂ => k s₂ ⟨?_, fun r h₁ h₂ => by rw [u₂.other r h₁, u₁.other r h₂], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
  rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hk.r11, Hmac.Generic.Arm.movw_ofNat ho]

/-- `adc d, n, #y`. -/
theorem wp_adc {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → s'.c = s.c → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0))) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _) rfl)

/-- `subs d, n, op2`, with its carry: whether `n ≥ op2`. -/
theorem wp_subsC {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

/-- `mov d, op2`, keeping the carry. -/
theorem wp_movC {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {o : Op2} {v : BitVec 32}
    (ho : o.eval s = some v) (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d v) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _) rfl)

/-- `subs r12, x, #k; mov r12, #0; adc r12, r12, #0; cmp r12, #0`: `Z` is
whether `x < k`, and only `r12` and the flags change. -/
theorem wp_lt {is : List Instr} {s : State} {Q : State → Prop} {x : Reg} {k : BitVec 32}
    (hk : encodable k = true)
    (h : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → s'.z = decide ((s.gpr x).toNat < k.toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs .r12 x (.imm k) :: .mov .r12 (.imm 0) :: .adc .r12 .r12 (.imm 0) :: .cmp .r12 (.imm 0) :: is))
      s Q := by
  refine wp_subsC (VG.Proof.MdStream.Arm.op2_imm hk) fun s₁ u₁ c₁ => wp_movC
    (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ c₂ => wp_adc (VG.Proof.MdStream.Arm.op2_imm (by decide))
    fun s₃ u₃ c₃ => VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ f₄ z₄ =>
      h s₄ (fun r hr => by rw [f₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr]) (by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem])
        (by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [f₄.sp, u₃.sp, u₂.sp, u₁.sp]) ?_
  rw [z₄, u₃.gpr, u₂.gpr, c₂, c₁]
  by_cases hlt : (s.gpr x).toNat < k.toNat
  · simp [hlt, show ¬ (k.toNat ≤ (s.gpr x).toNat) by omega]
  · simp [hlt, show k.toNat ≤ (s.gpr x).toNat by omega]

end VG.Proof.Pbkdf2.Whole.Arm
