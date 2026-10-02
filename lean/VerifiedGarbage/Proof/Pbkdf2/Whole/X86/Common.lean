import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Contract
import VerifiedGarbage.Proof.Hmac.Generic.X86.Init
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the functions it calls, and its parts

`FnsOK F` is what the proof knows of the functions `pbkdf2` calls: the hash
function's streaming functions (`VG.Proof.Hmac.Generic.X86.HashOK`), and
HMAC's `init` and `finalize` and PBKDF2's `iterate`, sound for their shared
contracts with 48 bytes of stack (`Sound`), with some working space each, at
most the `8 W` bytes they get. Then the precondition of `pbkdf2` (`Pre`), the
parts of its `scratch`, and what every piece of it keeps (`KR`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Hmac.Generic.X86 (Hash at_)
open VG.Proof.Hmac.Generic.X86 (HashOK SavedRegs saveR)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open Spec.Sha256 (bytesAt)

/-- The functions `pbkdf2` calls, verified. -/
structure FnsOK (F : Fns) where
  hH : HashOK F.H
  Wi : Nat
  Wf : Nat
  Wt : Nat
  hi : Sound F.hiC (Spec.Hmac.initContract hH.SH Wi X86.abi 48)
  hf : Sound F.hfC (Spec.Hmac.finalizeContract hH.SH Wf X86.abi 48)
  it : Sound F.itC (Spec.Pbkdf2.iterateContract hH.SH Wt X86.abi 48)
  hiSp : NoSp F.hiC
  hfSp : NoSp F.hfC
  itSp : NoSp F.itC
  hiSU : stackUse F.hiC ≤ 48
  hfSU : stackUse F.hfC ≤ 48
  itSU : stackUse F.itC ≤ 48
  hWi : Wi ≤ F.W
  hWf : Wf ≤ F.W
  hWt : Wt ≤ F.W
  hWH : F.H.W ≤ F.W
  hW : F.W ≤ 512
  /-- The digest is no longer than a block (so that the digest of a long
  password is a key `init` takes). -/
  hDB : F.H.D ≤ F.H.B
  /-- The streaming state holds a block. -/
  hBS : F.H.B ≤ F.H.S
  /-- Our buffers fit in the `8 S` bytes after the working space. -/
  fits : 20 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S

variable {F : Fns}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev pw : BitVec 32 := arg s₀ 0
abbrev pwl : Nat := (arg s₀ 1).toNat
abbrev salt : BitVec 32 := arg s₀ 2
abbrev sl : Nat := (arg s₀ 3).toNat
/-- The iteration count. -/
abbrev cc : Nat := (arg s₀ 4).toNat
abbrev out : BitVec 32 := arg s₀ 5
abbrev ol : Nat := (arg s₀ 6).toNat
abbrev scr : BitVec 32 := arg s₀ 7
abbrev pwR : Region := ⟨(pw s₀).setWidth 64, pwl s₀⟩
abbrev saltR : Region := ⟨(salt s₀).setWidth 64, sl s₀⟩
abbrev outR : Region := ⟨(out s₀).setWidth 64, ol s₀⟩
abbrev scR (F : Fns) : Region := ⟨(scr s₀).setWidth 64, (F.W + F.H.S) * 8⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 32⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 76
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨(scr s₀).setWidth 64, k⟩

end

/-- The size of `scratch`. -/
abbrev _root_.VG.Impl.Pbkdf2.Whole.X86.Fns.L8 (F : Fns) : Nat := (F.W + F.H.S) * 8

/-- The precondition. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  sp76 : 76 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 36 ≤ 2 ^ 32
  rd : s₀.rd = [pwR s₀, saltR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scR s₀ F]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR s₀ F)
  pw_a : (pwR s₀).Disjoint (argR s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR s₀ F)
  sa_a : (saltR s₀).Disjoint (argR s₀)
  o_s : (outR s₀).Disjoint (scR s₀ F)
  o_a : (outR s₀).Disjoint (argR s₀)
  s_a : (scR s₀ F).Disjoint (argR s₀)
  r_pw : (retR s₀).Disjoint (pwR s₀)
  r_sa : (retR s₀).Disjoint (saltR s₀)
  r_o : (retR s₀).Disjoint (outR s₀)
  r_s : (retR s₀).Disjoint (scR s₀ F)
  r_a : (retR s₀).Disjoint (argR s₀)
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

theorem pre_of (hF : FnsOK F) {s₀ : State} (h : (pbkN hF.hH.SH (F.W + F.H.S)).pre s₀) : Pre F s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hD := hF.hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩ : Region) = stkR s₀ := by
    rw [stkR, below_eq h0]
  rw [hD] at h28
  rw [e] at h18 h19 h20 h21 h22
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩

/-! ## The layout of `scratch` -/

/-- The sizes, as facts about natural numbers. -/
structure Sizes (F : Fns) : Prop where
  B : 0 < F.H.B ∧ F.H.B ≤ 128
  S : 0 < F.H.S ∧ F.H.S ≤ 256
  D : 0 < F.H.D ∧ F.H.D ≤ F.H.F ∧ F.H.F ≤ 64
  W : F.H.W ≤ F.W ∧ F.W ≤ 512
  DB : F.H.D ≤ F.H.B
  BS : F.H.B ≤ F.H.S
  fits : 20 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S

theorem FnsOK.sizes (hF : FnsOK F) : Sizes F :=
  ⟨⟨hF.hH.hB0, hF.hH.hBB⟩, ⟨hF.hH.hS0, hF.hH.hSB⟩, ⟨hF.hH.hD0, hF.hH.hDF, hF.hH.hF⟩, ⟨hF.hWH, hF.hW⟩, hF.hDB, hF.hBS, hF.fits⟩

/-- Where the parts of `scratch` are. -/
theorem layout : F.L.buf = 8 * F.W + 16 ∧ F.st0O = 8 * F.W + 16 ∧ F.st1O = 8 * F.W + 16 + F.H.S ∧
    F.stSO = 8 * F.W + 16 + 2 * F.H.S ∧ F.stWO = 8 * F.W + 16 + 3 * F.H.S ∧
    F.uO = 8 * F.W + 16 + 4 * F.H.S ∧ F.tO = 8 * F.W + 16 + 4 * F.H.S + F.H.D ∧
    F.hkO = 8 * F.W + 16 + 4 * F.H.S + 2 * F.H.D ∧ F.intO = 8 * F.W + 16 + 4 * F.H.S + 2 * F.H.D + F.H.F := by
  dsimp only [Fns.st0O, Fns.st1O, Fns.stSO, Fns.stWO, Fns.uO, Fns.tO, Fns.hkO, Fns.intO, Fns.L, Hash.buf]
  omega

theorem end_le (hz : Sizes F) : F.intO + 4 ≤ F.L8 := by
  have := layout (F := F); have := hz.fits; simp only [Fns.L8]; omega

theorem L8_le (hz : Sizes F) : F.L8 ≤ 8 * 512 + 8 * 256 := by
  have := hz.W; have := hz.S; simp only [Fns.L8]; omega

/-- The save area of our caller's registers. -/
abbrev svR (F : Fns) (s₀ : State) : Region := saveR F.L (scr s₀)

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < F.L8) : (dO s₀ o).setWidth 64 = A s₀ o := by
  have := hp.nsc; exact Hmac.Generic.X86.setWidth_add (by omega)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc; exact Hmac.Generic.X86.toNat_add_ofNat (by omega)

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (sR s₀ o n) (scR s₀ F) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (lowR s₀ k) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.base_disjoint _ hk (by omega)

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (lowR s₀ k) (scR s₀ F) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (svR F s₀) (scR s₀ F) := by
  have := end_le hz; have := layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 16 ≤ F.L8; omega)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8) : (svR F s₀).Disjoint (sR s₀ o n) := by
  have := L8_le hz; exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega)) (by simp only [Fns.L]; omega) (by omega)

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (svR F s₀).Disjoint (lowR s₀ k) := by
  have := L8_le hz; have := end_le hz; have := layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 16) (by simp only [Fns.L]; omega)
    (by simp only [Fns.L]; omega)).symm

omit hz in
theorem sc_mem : scR s₀ F ∈ s₀.wr := by rw [hp.wr]; simp

theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.L8) :
    InRegions s.wr (A s₀ o) n := by
  have := L8_le hz
  exact ⟨scR s₀ F, by rw [hwr]; exact sc_mem hp, Offset.contains_base _ h (by omega)⟩

end

/-! ## What every piece keeps -/

/-- The regions everything writes: `out`, `scratch` and the stack below `esp`. -/
abbrev wrs (F : Fns) (s₀ : State) : List Region := [outR s₀, scR s₀ F, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  saved : SavedRegs F.L (scr s₀) s₀ s.mem
  frame : Frame (wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

/-- The 76 bytes below `esp`, while `KR` holds. -/
theorem KR.stkE {s₀ s : State} (h : KR F s₀ s) : VG.Proof.Pbkdf2.Whole.X86.stk s = stkR s₀ := by
  rw [VG.Proof.Pbkdf2.Whole.X86.stk, h.esp]

/-- `KR` survives changes to other registers, and to memory in `out`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (svR F s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs F s₀, Region.Sub r r') :
    KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    h.saved.frame F.L hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR F s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd {s₀ s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : VG.Proof.Sha256.X86.Stream.Upd s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A write to a part of `scratch` after the save area. -/
theorem KR.write {s₀ s s' : State} (hz : Sizes F) (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8)
    (hf : Frame [sR s₀ o n] s.mem s'.mem) : KR F s₀ s' :=
  h.keep hrd hwr hg hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sv_disj hz ho hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after the save area, or
the working space, and the stack below `esp`. -/
theorem KR.call {s₀ s s' : State} (hp : Pre F s₀) (hz : Sizes F) (h : KR F s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨
      ∃ o n, r = sR s₀ o n ∧ 8 * F.W + 16 ≤ o ∧ o + n ≤ F.L8) : KR F s₀ s' := by
  have hL := end_le hz; have := layout (F := F)
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
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

/-! ## The arguments, the return address and the inputs, while `KR` holds -/

section
variable {s₀ : State} (hp : Pre F s₀)
include hp

omit hp in
theorem argR_eq : argR s₀ = ⟨addr (E s₀) 4, 32⟩ := rfl

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := hp.b_a

theorem KR.argEq {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 8) : arg s i = arg s₀ i := by
  have hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨addr (E s₀) 4, 32⟩ r := by
    rw [← argR_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.b_a.symm
  exact Hmac.Generic.X86.arg_keep rfl hk.esp (n := 32) (by have := hp.spf; omega) hk.frame hd (by omega)

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = E s₀) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [show s.ea (at_ .esp (4 + 4 * i)) = addr (s.gpr .esp) (4 + 4 * i) from rfl, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 8) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.wr]
  exact ⟨argR s₀, by simp, by
    rw [argR_eq]; exact Hmac.Generic.X86.arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

/-- An argument, read from memory while `KR` holds. -/
theorem KR.readArg {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 8) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have := hk.argEq hp hi
  simp only [arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by
    rw [Hmac.Generic.X86.argAddr_eq, Hmac.Generic.X86.argAddr_eq, hk.esp]] at this

/-- `mov d, [esp + 4 + 4 i]`: argument `i`, while `KR` holds. -/
theorem wp_arg {s : State} (hk : KR F s₀ s) {d : Reg} {i : Nat} (hi : i < 8) {is : List Instr}
    {Q : State → Prop} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (Fns.argM i) :: is)) s Q :=
  VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ i) (argW hk.esp i) (argIn hp hk.rd hk.wr hi)
    fun s' u => k s' (by rw [hk.readArg hp hi] at u; exact u)

/-- The return address, while `KR` holds. -/
theorem KR.ret {s : State} (hk : KR F s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_o
    · exact hp.r_s
    · rw [stkR, below_eq hp.sp76]
      exact (Offset.below_disjoint _ (by omega)).symm) (by decide)

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : KR F s₀ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep hk.frame hd hn

theorem KR.pwBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem ((pw s₀).setWidth 64) (pwl s₀) = bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.b_pw.symm) (by have := hp.npw; omega)

theorem KR.saltBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem ((salt s₀).setWidth 64) (sl s₀) = bytesAt s₀.mem ((salt s₀).setWidth 64) (sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.b_sa.symm) (by have := hp.nsa; omega)

end

/-- `d ← scratch + o`, while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : KR F s₀ s) {d : Reg} {o : Nat} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Hmac.Generic.X86.scr, List.cons_append, List.nil_append]
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂ u₂ =>
    k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, hk.ebp]

end VG.Proof.Pbkdf2.Whole.X86
