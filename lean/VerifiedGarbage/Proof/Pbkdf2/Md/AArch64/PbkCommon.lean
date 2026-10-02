import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Common

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s parts

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/PbkCommon.lean`): the precondition of
`pbkdf2` (`Pre`), the parts of its `scratch`, and what every piece of it keeps
(`KR`): our caller's registers (those we save in `scratch`, and `x25`–`x28`,
which nothing we run writes), `out`, `c - 1` and `out_len` in `scratch`, and
that everything written is in `out`, `scratch` or the 16 bytes below the stack
pointer.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (Sizes)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (stk SavedRegs SavedRegs.frame saveR)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self)
open Spec.Sha256 (bytesAt)

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .x0
abbrev pwl : Nat := (s₀.gpr .x1).toNat
abbrev salt : Addr := s₀.gpr .x2
abbrev sl : Nat := (s₀.gpr .x3).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .x4).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .x5
abbrev ol : Nat := (s₀.gpr .x6).toNat
abbrev scr : Addr := s₀.gpr .x7
abbrev pwR : Region := ⟨pw s₀, pwl s₀⟩
abbrev saltR : Region := ⟨salt s₀, sl s₀⟩
abbrev outR : Region := ⟨out s₀, ol s₀⟩
abbrev scR : Region := ⟨scr s₀, (H.W + H.S) * 8⟩
abbrev stkR : Region := stk s₀
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- Our caller's registers, `out`, `c - 1` and `out_len`. -/
abbrev hdrR : Region := sR s₀ H.sv 80
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨scr s₀, 8 * H.W⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  rd : s₀.rd = [pwR s₀, saltR s₀]
  wr : s₀.wr = [outR s₀, scR (H := H) s₀]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR (H := H) s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR (H := H) s₀)
  o_s : (outR s₀).Disjoint (scR (H := H) s₀)
  stk_pw : (stkR s₀).Disjoint (pwR s₀)
  stk_sa : (stkR s₀).Disjoint (saltR s₀)
  stk_o : (stkR s₀).Disjoint (outR s₀)
  stk_s : (stkR s₀).Disjoint (scR (H := H) s₀)
  pwnw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 64
  sanw : (salt s₀).toNat + sl s₀ ≤ 2 ^ 64
  onw : (out s₀).toNat + ol s₀ ≤ 2 ^ 64
  snw : (scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * H.D

theorem pre_of (hH : HashOK H) {s₀ : State} (h : (pbkG hH.SH (H.W + H.S)).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have hD := hH.hD
  simp only [hD] at h17
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- The sizes, as facts about natural numbers. -/
structure PSizes (H : Hash) : Prop where
  z : Sizes H.P H.D H.W
  W : H.W ≤ 256

theorem _root_.VG.Proof.Pbkdf2.Md.AArch64.HashOK.psizes (hH : HashOK H) : PSizes H := ⟨hH.sizes, hH.W⟩

theorem PSizes.N (hz : PSizes H) : 0 < H.P.N ∧ H.P.N ≤ 64 := hz.z.dims.N
theorem PSizes.B_le (hz : PSizes H) : H.P.B ≤ 128 := by rcases hz.z.B with h | h <;> omega
theorem PSizes.B_ge (hz : PSizes H) : 64 ≤ H.P.B := by rcases hz.z.B with h | h <;> omega

/-! ## The parts of `scratch` -/

/-- Where the parts of `scratch` are. -/
theorem layout : H.sv = 8 * H.W ∧ H.outO = 8 * H.W + 56 ∧ H.cO = 8 * H.W + 64 ∧ H.olO = 8 * H.W + 72 ∧
    H.st0O = 8 * H.W + 80 ∧ H.st1O = 8 * H.W + 80 + H.S ∧ H.stSO = 8 * H.W + 80 + 2 * H.S ∧
    H.stWO = 8 * H.W + 80 + 3 * H.S ∧ H.uO = 8 * H.W + 80 + 4 * H.S ∧
    H.tO = 8 * H.W + 80 + 4 * H.S + H.D ∧ H.hkO = 8 * H.W + 80 + 4 * H.S + 2 * H.D ∧
    H.intO = 8 * H.W + 80 + 4 * H.S + 2 * H.D + H.P.N ∧ H.S = H.P.N + H.P.B := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [Hash.sv, Hash.st0O, Hash.st1O, Hash.stSO, Hash.stWO, Hash.uO, Hash.tO,
      Hash.hkO, Hash.intO] <;> omega

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)

include hz in
/-- The parts of `scratch`, as offsets: they end before its end, and below
4096 (every offset is an immediate). -/
theorem end_le : H.intO + 4 ≤ (H.W + H.S) * 8 ∧ H.intO + 4 ≤ 4096 := by
  have := hz.N; have := hz.z.DN; have := hz.B_le; have := hz.B_ge; have := hz.W; have := layout (H := H)
  omega

include hz in
theorem L_lt : (H.W + H.S) * 8 < 2 ^ 64 := by
  have := hz.W; have := hz.N; have := hz.B_le; show (H.W + (H.P.N + H.P.B)) * 8 < 2 ^ 64; omega

theorem part_sub {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) : Region.Sub (sR s₀ o n) (scR (H := H) s₀) :=
  Offset.sub_base _ h

include hz in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ (H.W + H.S) * 8)
    (hb : b + n ≤ (H.W + H.S) * 8) : Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L_lt hz; exact Offset.disjoint _ h (by omega) (by omega)

include hz in
theorem low_disj {b n : Nat} (hb : 8 * H.W ≤ b) (hbn : b + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (sR s₀ b n) (lowR (H := H) s₀) := by
  have := L_lt hz; exact Offset.disjoint_base _ hb (by omega)

theorem low_sub : Region.Sub (lowR (H := H) s₀) (scR (H := H) s₀) :=
  Region.sub_prefix (by show 8 * H.W ≤ (H.W + H.S) * 8; omega)

include hp hz in
theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) :
    InRegions s.wr (A s₀ o) n := by
  have := L_lt hz
  exact ⟨scR (H := H) s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ h (by omega)⟩

include hp in
theorem sc_mem : scR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

include hp in
theorem out_mem : outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's registers,
`out`, `c - 1` and `out_len` in `scratch`, and everything written is in
`out`, `scratch` or the 16 bytes below the stack pointer. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.hh (scr s₀) s₀ s.mem
  outW : s.mem.readW (A s₀ H.outO) 64 = out s₀
  cW : s.mem.readW (A s₀ H.cO) 64 = BitVec.ofNat 64 (cc s₀ - 1)
  olW : s.mem.readW (A s₀ H.olO) 64 = s₀.gpr .x6
  frame : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x23, .x25, .x26, .x27, .x28]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem hdr_sub {s₀ : State} {o : Nat} (h₁ : H.sv ≤ o) (h₂ : o + 8 ≤ H.sv + 80) :
    Region.Sub ⟨A s₀ o, 8⟩ (hdrR (H := H) s₀) := Offset.sub _ h₁ h₂

theorem save_hdr {s₀ : State} : Region.Sub (saveR H.hh (scr s₀)) (hdrR (H := H) s₀) :=
  Offset.sub _ (Nat.le_refl _) (by show 8 * H.W + 56 ≤ 8 * H.W + 80; omega)

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (hdrR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ s' := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (by revert hr; decide +revert)).trans (h.cs r hr),
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left save_hdr, ?_, ?_, ?_,
    h.frame.trans (hf.sub hsub)⟩
  · rw [← h.outW]
    exact hf.readW (r := ⟨A s₀ H.outO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.outO]) (by simp [Hash.outO])))
      (by decide)
  · rw [← h.cW]
    exact hf.readW (r := ⟨A s₀ H.cO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.cO]) (by simp [Hash.cO])))
      (by decide)
  · rw [← h.olW]
    exact hf.readW (r := ⟨A s₀ H.olO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.olO]) (by simp [Hash.olO])))
      (by decide)

omit hp hz in
theorem KR.same {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h)
    (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : KR (H := H) s₀ s) {d : Reg} {v : BitVec 64}
    (u : VG.Proof.MdStream.AArch64.Upd s s' d v) (hd : d ∉ kregs) : KR (H := H) s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

omit hp in
/-- A write into a part of `scratch` after its header keeps `KR`. -/
theorem KR.write {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {o n : Nat}
    (ho : H.st0O ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by simpa [Hash.st0O] using ho)) (by
        have := (end_le hz).1; simp only [Hash.st0O] at ho; omega) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

omit hz in
theorem stk_sc {s : State} (h : KR (H := H) s₀ s) {R : Region} (hR : Region.Sub R (scR (H := H) s₀)) :
    (below s.sp 16).Disjoint R := by
  rw [h.sp]; exact hp.stk_s.sub_right hR

/-- What a call leaves, writing parts of `scratch` after its header, or its
working space, and the 16 bytes below the stack pointer. -/
theorem KR.call {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) {ws : List Region}
    (hf : Frame (ws ++ [below s.sp 16]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    KR (H := H) s₀ s' := by
  have := (end_le hz).1; have := layout (H := H)
  have hst : H.sv + 80 = H.st0O := by simp [Hash.st0O]
  refine h.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr).1 (kregs_pres r hr).2) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (low_disj hz (Nat.le_refl _) (by omega)).sub_right (Region.sub_prefix hk)
      · exact part_disj hz (Or.inl (by rw [hst]; exact h₁)) (by rw [hst]; omega) h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (stk_sc hp h (part_sub (by rw [hst]; omega))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega)⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.sp]
      exact ⟨_, by simp, fun _ h => h⟩

omit hp hz in
/-- The regions only read are the same as on entry. -/
theorem KR.bytes {s : State} (h : KR (H := H) s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep h.frame hd hn

omit hz in
theorem KR.pwBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (pw s₀) (pwl s₀) = bytesAt s₀.mem (pw s₀) (pwl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.stk_pw.symm) (by have := hp.pwnw; omega)

omit hz in
theorem KR.saltBytes {s : State} (h : KR (H := H) s₀ s) :
    bytesAt s.mem (salt s₀) (sl s₀) = bytesAt s₀.mem (salt s₀) (sl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.stk_sa.symm) (by have := hp.sanw; omega)

omit hz in
theorem in_wr {s : State} (h : KR (H := H) s₀ s) : scR (H := H) s₀ ∈ s.wr := by rw [h.wr]; exact sc_mem hp

omit hz in
/-- The parts of `scratch` the functions we call get, as covered regions. -/
theorem cov_part {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  sub_of_off (in_wr hp h) hon

omit hz in
theorem cov_low {s : State} (h : KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (in_wr hp h) hn

/-- A part of `scratch`, readable. -/
theorem in_rw {s : State} (h : KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    InRegions (s.rd ++ s.wr) (A s₀ o) n :=
  VG.Proof.Hmac.Generic.Common.InRegions.right' ⟨_, in_wr hp h, Offset.contains_base _ hon
    (by have := L_lt hz; omega)⟩

end

end VG.Proof.Pbkdf2.Md.AArch64.Pbk
