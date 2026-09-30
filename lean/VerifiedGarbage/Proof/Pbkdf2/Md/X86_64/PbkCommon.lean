import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Contract
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Init

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s parts

Untrusted: everything here is checked by Lean. The precondition of `pbkdf2`
(`Pre`), the parts of its `scratch`, what every piece of it keeps (`KR`),
and the calls of the functions it calls: the hash function's streaming
functions (`VG.Proof.Hmac.Generic.X86_64.HashOK`), HMAC's `init` and
`finalize`, and `iterate`, whose proofs it takes as hypotheses.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Sizes pbkG)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Hmac.Generic.X86_64 (initG finG After SavedRegs ne_rsp callEntry_bytes SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .rdi
abbrev pwl : Nat := (s₀.gpr .rsi).toNat
abbrev salt : Addr := s₀.gpr .rdx
abbrev sl : Nat := (s₀.gpr .rcx).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .r8).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .r9
abbrev ol : Nat := (stackArg s₀ 0).toNat
abbrev scr : Addr := stackArg s₀ 1
abbrev pwR : Region := ⟨pw s₀, pwl s₀⟩
abbrev saltR : Region := ⟨salt s₀, sl s₀⟩
abbrev outR : Region := ⟨out s₀, ol s₀⟩
abbrev scR : Region := ⟨scr s₀, (H.W + H.S) * 8⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - BitVec.ofNat 64 24, 24⟩
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- Our caller's registers, `out` and `c - 1`. -/
abbrev hdrR : Region := sR s₀ H.sv 64
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨scr s₀, 8 * H.W⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  sp₁ : 24 ≤ (s₀.gpr .rsp).toNat
  sp₂ : (s₀.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s₀.rd = [pwR s₀, saltR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scR (H := H) s₀]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR (H := H) s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR (H := H) s₀)
  o_s : (outR s₀).Disjoint (scR (H := H) s₀)
  o_a : (outR s₀).Disjoint (argR s₀)
  s_a : (scR (H := H) s₀).Disjoint (argR s₀)
  ret_pw : (retR s₀).Disjoint (pwR s₀)
  ret_sa : (retR s₀).Disjoint (saltR s₀)
  ret_o : (retR s₀).Disjoint (outR s₀)
  ret_s : (retR s₀).Disjoint (scR (H := H) s₀)
  ret_a : (retR s₀).Disjoint (argR s₀)
  stk_pw : (stkR s₀).Disjoint (pwR s₀)
  stk_sa : (stkR s₀).Disjoint (saltR s₀)
  stk_o : (stkR s₀).Disjoint (outR s₀)
  stk_s : (stkR s₀).Disjoint (scR (H := H) s₀)
  stk_a : (stkR s₀).Disjoint (argR s₀)
  pwnw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 64
  sanw : (salt s₀).toNat + sl s₀ ≤ 2 ^ 64
  onw : (out s₀).toNat + ol s₀ ≤ 2 ^ 64
  snw : (scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * H.D

theorem pre_of (hH : HashOK H) {s₀ : State} (h : (pbkG hH.SH (H.W + H.S)).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  have hD := hH.hD
  simp only [hD] at h26
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

/-- The sizes, as facts about natural numbers. -/
structure PSizes (H : Hash) : Prop where
  z : Sizes H
  W : H.W ≤ 256

theorem _root_.VG.Proof.Pbkdf2.Md.X86_64.HashOK.psizes (hH : HashOK H) : PSizes H := ⟨hH.sizes, hH.hW⟩

/-! ## The parts of `scratch` -/

/-- Where the parts of `scratch` are. -/
theorem layout : H.sv = 8 * H.W ∧ H.outO = 8 * H.W + 48 ∧ H.cO = 8 * H.W + 56 ∧ H.st0O = 8 * H.W + 64 ∧
    H.st1O = 8 * H.W + 64 + H.S ∧ H.stSO = 8 * H.W + 64 + 2 * H.S ∧ H.stWO = 8 * H.W + 64 + 3 * H.S ∧
    H.uO = 8 * H.W + 64 + 4 * H.S ∧ H.tO = 8 * H.W + 64 + 4 * H.S + H.D ∧
    H.hkO = 8 * H.W + 64 + 4 * H.S + 2 * H.D ∧ H.intO = 8 * H.W + 64 + 4 * H.S + 2 * H.D + H.P.N ∧
    H.S = H.P.N + H.P.B := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [Hash.sv, Hash.st0O, Hash.st1O, Hash.stSO, Hash.stWO, Hash.uO, Hash.tO,
      Hash.hkO, Hash.intO] <;> omega

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)

include hz in
/-- The parts of `scratch`, as offsets: they end before its end. -/
theorem end_le : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  have := hz.z.N; have := hz.z.D; have := hz.z.B; have := layout (H := H)
  omega

include hz in
theorem L_lt : (H.W + H.S) * 8 < 2 ^ 64 := by
  have := hz.W; have := hz.z.N; have := hz.z.B_le; show (H.W + (H.P.N + H.P.B)) * 8 < 2 ^ 64; omega

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

theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  fun x h₁ h₂ => Offset.base_disjoint_below (s₀.gpr .rsp) (n := 24) (k := 8) (by omega) x h₂ h₁

/-- The 8 · (depth + 1) bytes below `rsp` that a call of depth at most 2 uses. -/
theorem below_stk {n : Nat} (hn : n ≤ 24) : Region.Sub (below (s₀.gpr .rsp) n) (stkR s₀) :=
  below_sub hn (by omega)

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's registers,
`out` and `c - 1` in `scratch`, and everything written is in `out`,
`scratch` or the stack. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.hh (scr s₀) s₀ s.mem
  outW : s.mem.readW (A s₀ H.outO) 64 = out s₀
  cW : s.mem.readW (A s₀ H.cO) 64 = BitVec.ofNat 64 (cc s₀ - 1)
  frame : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s.mem

/-- Registers `KR` fixes. -/
abbrev kregs : List Reg := [.r15, .rsp]

theorem hdr_sub {s₀ : State} {o : Nat} (h₁ : H.sv ≤ o) (h₂ : o + 8 ≤ H.sv + 64) :
    Region.Sub ⟨A s₀ o, 8⟩ (hdrR (H := H) s₀) := Offset.sub _ h₁ h₂

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (hdrR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [outR s₀, scR (H := H) s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ s' := by
  have hs : Region.Sub (VG.Proof.Hmac.Generic.X86_64.saveR H.hh (scr s₀)) (hdrR (H := H) s₀) := Offset.sub _ (Nat.le_refl _) (by
    show 8 * H.W + 48 ≤ 8 * H.W + 64; omega)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, h15.trans h.r15,
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left hs, ?_, ?_, h.frame.trans (hf.sub hsub)⟩
  · rw [← h.outW]
    exact hf.readW (r := ⟨A s₀ H.outO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.outO]) (by simp [Hash.outO])))
      (by decide)
  · rw [← h.cW]
    exact hf.readW (r := ⟨A s₀ H.cO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (hdr_sub (by simp [Hash.cO]) (by simp [Hash.cO])))
      (by decide)

omit hp in
/-- A write into a part of `scratch` after its header keeps `KR`. -/
theorem KR.write {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {o n : Nat}
    (ho : H.st0O ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by simpa [Hash.st0O] using ho)) (by
        have := end_le hz; simp only [Hash.st0O] at ho; omega) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after its header, or its
working space, and the stack below `rsp`. -/
theorem KR.call {s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    KR (H := H) s₀ s' := by
  have := end_le hz; have := layout (H := H)
  have hst : H.sv + 64 = H.st0O := by simp [Hash.st0O]
  refine h.keep hrd hwr (hcs _ (by simp [calleeSaved])) (hcs _ (by simp [calleeSaved])) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (low_disj hz (Nat.le_refl _) (by omega)).sub_right (Region.sub_prefix hk)
      · exact part_disj hz (Or.inl (by rw [hst]; exact h₁)) (by rw [hst]; omega) h₂
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ((hp.stk_s.sub_left (below_stk hn)).sub_right (part_sub (by rw [hst]; omega))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega)⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ⟨_, by simp, below_stk hn⟩

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

omit hp hz in
theorem KR.readW {s : State} (h : KR (H := H) s₀ s) {R : Region} {a : Addr} (hc : R.Contains a 8)
    (hd : ∀ r ∈ [outR s₀, scR (H := H) s₀, stkR s₀], R.Disjoint r) :
    s.mem.readW a 64 = s₀.mem.readW a 64 :=
  h.frame.readW hc hd (by decide)

omit hz in
theorem KR.ret {s : State} (h : KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
  h.readW (R := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
    · exact stk_ret.symm)

omit hz in
/-- `out_len`, on the stack. -/
theorem KR.olW {s : State} (h : KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 :=
  h.readW (R := argR s₀) (contains_pre (by decide)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.stk_a.symm)

end

end VG.Proof.Pbkdf2.Md.X86_64.Pbk
