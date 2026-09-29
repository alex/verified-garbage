import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Impl.MlKem.X86.Encode
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_encode12`

Untrusted: everything here is checked by Lean. Pair `k` of coefficients is
the 24-bit number `f[2k] + 2¹² f[2k+1]`, whose bytes are bytes `3k … 3k+2`
of the encoding (`encode12_group`).
-/

namespace VG.Proof.MlKem.X86.Encode12

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev oP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev oA : Addr := (oP s₀).setWidth 64
abbrev oR : Region := ⟨oA s₀, 384⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 4 * 2⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The encoding. -/
abbrev L : List Byte := encode12 (polyAt s₀.mem (fA s₀))
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * 2 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA s₀)]
  wr : s₀.wr = [oR s₀, aR s₀]
  f_o : (polyRegion (fA s₀)).Disjoint (oR s₀)
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  o_a : (oR s₀).Disjoint (aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_o : (retR s₀).Disjoint (oR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_o : (stkR s₀).Disjoint (oR s₀)
  stk_a : (stkR s₀).Disjoint (aR s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + 384 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)

theorem Pre.of {s₀ : State} (h : (encode12Contract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (8 * k)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (3 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (128 - k)
  frame : Frame [oR s₀] (P0 s₀).mem s.mem
  out : ∀ j < 3 * k, s.mem (oA s₀ + BitVec.ofNat 64 j) = (L s₀)[j]!

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem f_keep {s : State} (hf : Frame [oR s₀] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (fA s₀) i = coeffAt s₀.mem (fA s₀) i := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  refine coeffAt_congr (fun j hj => ?_) hi
  rw [hf.bytes (R := polyRegion (fA s₀)) (by simpa using hp.f_o) (polyLen _) hj,
    hf₁.bytes (R := polyRegion (fA s₀)) (by simpa [← hp.stk_eq] using hp.stk_f.symm) (polyLen _) hj]

end Pre

theorem init_piece :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) (Inv · 0) (.block enc12Init) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₁ := P0_argAddr s₀ 1
    have i₀ := P0_argIn (s₀ := s₀) (n := 2) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₁ := P0_argIn (s₀ := s₀) (n := 2) (i := 1) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 2) (i := 0) (by omega) fit hp.stk_a
    have v₁ := P0_arg hp.sp (n := 2) (i := 1) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
    apply WP.of_runBlock
    simp (config := {decide := true}) only [enc12Init, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀, i₁, v₀, v₁,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, rfl, rfl, by simp, by simp, by simp, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]


theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) {s : State} (h : Inv s₀ k s) :
    WP isa (.block enc12Body) s fun s' => Inv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 128)) := by
  have ff := hp.f_fit
  have fo := hp.o_fit
  have e0 : (fP s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (fA s₀) (2 * k) := by
    rw [ea_add (by omega)]; congr 2; omega
  have e1 : (fP s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4).setWidth 64 =
      coeffAddr (fA s₀) (2 * k + 1) := by
    rw [ea_add (by omega)]; congr 2; omega
  have o0 : (oP s₀ + BitVec.ofNat 32 (3 * k) + BitVec.ofNat 32 0).setWidth 64 =
      oA s₀ + BitVec.ofNat 64 (3 * k) := by rw [ea_add (by omega), Nat.add_zero]
  have o1 : (oP s₀ + BitVec.ofNat 32 (3 * k) + BitVec.ofNat 32 1).setWidth 64 =
      oA s₀ + BitVec.ofNat 64 (3 * k + 1) := ea_add (by omega)
  have o2 : (oP s₀ + BitVec.ofNat 32 (3 * k) + BitVec.ofNat 32 2).setWidth 64 =
      oA s₀ + BitVec.ofNat 64 (3 * k + 2) := ea_add (by omega)

  have inF : ∀ i < 256, InRegions (s.rd ++ s.wr) (coeffAddr (fA s₀) i) 4 := fun i hi =>
    ⟨polyRegion (fA s₀), by rw [h.rd, pushed_rd, hp.rd]; simp, coeff_contains _ hi⟩
  have outO : ∀ t < 3, InRegions s.wr (oA s₀ + BitVec.ofNat 64 (3 * k + t)) 1 := fun t ht =>
    ⟨oR s₀, by rw [h.wr, P0_wr, hp.wr]; simp, contains_at (by omega) fo⟩
  have i0 := inF (2 * k) (by omega)
  have i1 := inF (2 * k + 1) (by omega)
  have w0 := outO 0 (by omega)
  have w1 := outO 1 (by omega)
  have w2 := outO 2 (by omega)
  simp only [Nat.add_zero] at w0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [enc12Body, at_, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, execShift, readSrc, State.ea, State.load32, State.store8, State.setReg, arithFlags,
    State.setFlags, Reg8.reg, Option.map_some, Option.bind_some, h.esi, h.edi, e0, e1, o0, o1, o2,
    i0, i1, w0, w1, w2, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have ha := hp.f_red (2 * k) (by show 2 * k < 256; omega)
  have hb := hp.f_red (2 * k + 1) (by show 2 * k + 1 < 256; omega)
  rw [← coeffAt_eq, ← coeffAt_eq, hp.f_keep h.frame (by omega), hp.f_keep h.frame (by omega)]
  generalize ea : coeffAt s₀.mem (fA s₀) (2 * k) = a at ha
  generalize eb : coeffAt s₀.mem (fA s₀) (2 * k + 1) = b at hb
  rw [q_eq] at ha hb
  have hw : (a + b.rotateRight 20).toNat = a.toNat + 4096 * b.toNat := by
    rw [BitVec.toNat_add, rotr_small b (by decide) (by decide) (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have byte : ∀ t < 3, (L s₀)[3 * k + t]! = BitVec.ofNat 8 ((a + b.rotateRight 20).toNat / 2 ^ (8 * t)) := by
    intro t ht
    rw [encode12_group _ (by omega) ht, polyAt_val hp.f_red (by show 2 * k < 256; omega),
      polyAt_val hp.f_red (by show 2 * k + 1 < 256; omega), ea, eb, hw]
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, ptr_next _ _ 8, ptr_next _ _ 3, by rw [h.ecx]; exact cnt_next hk,
    ?_, ?_⟩, by simp only [eval, h.ecx]; exact cnt_ne hk (by decide)⟩
  · have c : ∀ t < 3, (oR s₀).Contains (oA s₀ + BitVec.ofNat 64 (3 * k + t)) (8 / 8) :=
      fun t ht => contains_at (by omega) fo
    exact ((h.frame.writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _ (c 2 (by omega))
  · refine bytes_extend (by omega) h.out ?_ ?_ ?_
    · have := byte 0 (by omega)
      rw [Nat.add_zero] at this
      rw [this, setWidth8_eq]; simp
    · rw [byte 1 (by omega), setWidth8_eq, toNat_shr]
    · rw [byte 2 (by omega), setWidth8_eq, toNat_shr, toNat_shr, Nat.div_div_eq_div_mul]

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Inv s₀ 128) s₀ s')
    Impl.MlKem.X86.encode12 :=
  Piece.leafLoop (fun s₀ => [oR s₀]) (fun k s₀ s => Inv s₀ k s) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_o, hp.ret_o⟩)
    (fun _ _ _ _ hq => hq.1) init_piece
    (Piece.countLoop (by decide) (fun k s₀ s => Inv s₀ k s) [.esp, .esi, .edi, .ecx] (fun _ hk _ _ hp h => step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, fP, fP, hq.2.1]
        · rw [h.edi, h'.edi, oP, oP, hq.2.2]
        · rw [h.ecx, h'.ecx]) (by taint_decide))
    fun _ _ _ h => ⟨h.frame, h.esp, h.rd, h.wr⟩

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.encode12 (encode12Contract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact bytesAt_eq! (encode12_length _) fun j hj => hinv.out j (by omega)
  · let st := satState satMem [⟨0, 1024⟩] [⟨0x400, 384⟩, ⟨0x5004, 8⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      reduced_below (fun a ha => ?_) 0 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (show satMem a = 0
         simp only [satMem]
         rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
end VG.Proof.MlKem.X86.Encode12
