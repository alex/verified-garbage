import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Impl.MlKem.X86.Encode
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_decode12`

Bytes `3k … 3k+2` are the 12-bit fields of coefficients `2k` and `2k+1`
(`decode12_even`, `decode12_odd`), each reduced with one conditional
subtraction.
-/

namespace VG.Proof.MlKem.X86.Decode12

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev bP : BitVec 32 := arg s₀ 0
abbrev fP : BitVec 32 := arg s₀ 1
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, 384⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 4 * 2⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The input bytes. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) 384
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * 2 ≤ 2 ^ 32
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [polyRegion (fA s₀), aR s₀]
  b_f : (bR s₀).Disjoint (polyRegion (fA s₀))
  b_a : (bR s₀).Disjoint (aR s₀)
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  b_fit : (bP s₀).toNat + 384 ≤ 2 ^ 32
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32

theorem Pre.of {s₀ : State} (h : (decode12Contract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The value of coefficient `i`. -/
abbrev V (s₀ : State) (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decode12 (B s₀))[i]!).val

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = bP s₀ + BitVec.ofNat 32 (3 * k)
  edi : s.gpr .edi = fP s₀ + BitVec.ofNat 32 (8 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (128 - k)
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < 2 * k, coeffAt s.mem (fA s₀) i = V s₀ i

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem b_keep {s : State} (hf : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem) {j : Nat} (hj : j < 384) :
    s.mem (bA s₀ + BitVec.ofNat 64 j) = (B s₀).getD j 0 := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  have l : (bR s₀).len ≤ 2 ^ 64 := by show 384 ≤ 2 ^ 64; decide
  rw [bytesAt_getD _ _ hj, hf.bytes (R := bR s₀) (by simpa using hp.b_f) l hj,
    hf₁.bytes (R := bR s₀) (by simpa [← hp.stk_eq] using hp.stk_b.symm) l hj]

end Pre

theorem init_piece :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) (Inv · 0) (.block dec12Init) := by
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
    simp (config := {decide := true}) only [dec12Init, enc12Init, at_, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀,
      i₁, v₀, v₁, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, rfl, rfl, by simp, by simp, by simp, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) {s : State} (h : Inv s₀ k s) :
    WP isa (.block dec12Body) s fun s' => Inv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 128)) := by
  have fb := hp.b_fit
  have ff := hp.f_fit
  have e0 : (bP s₀ + BitVec.ofNat 32 (3 * k) + BitVec.ofNat 32 0).setWidth 64 =
      bA s₀ + BitVec.ofNat 64 (3 * k) := by rw [ea_add (by omega), Nat.add_zero]
  have e1 : (bP s₀ + BitVec.ofNat 32 (3 * k) + BitVec.ofNat 32 1).setWidth 64 =
      bA s₀ + BitVec.ofNat 64 (3 * k + 1) := ea_add (by omega)
  have e2 : (bP s₀ + BitVec.ofNat 32 (3 * k) + BitVec.ofNat 32 2).setWidth 64 =
      bA s₀ + BitVec.ofNat 64 (3 * k + 2) := ea_add (by omega)
  have o0 : (fP s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (fA s₀) (2 * k) := by rw [ea_add (by omega)]; congr 2; omega
  have o1 : (fP s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4).setWidth 64 =
      coeffAddr (fA s₀) (2 * k + 1) := by rw [ea_add (by omega)]; congr 2; omega
  have inB : ∀ t < 3, InRegions (s.rd ++ s.wr) (bA s₀ + BitVec.ofNat 64 (3 * k + t)) 1 := fun t ht =>
    ⟨bR s₀, by rw [h.rd, pushed_rd, hp.rd]; simp, contains_at (by omega) fb⟩
  have outF : ∀ i < 256, InRegions s.wr (coeffAddr (fA s₀) i) 4 := fun i hi =>
    ⟨polyRegion (fA s₀), by rw [h.wr, P0_wr, hp.wr]; simp, coeff_contains _ hi⟩
  have i0 := inB 0 (by omega)
  have i1 := inB 1 (by omega)
  have i2 := inB 2 (by omega)
  have w0 := outF (2 * k) (by omega)
  have w1 := outF (2 * k + 1) (by omega)
  simp only [Nat.add_zero] at i0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [dec12Body, csub, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, execShift, readSrc, State.ea, State.load8, State.store32, State.setReg,
    arithFlags, State.setFlags, Option.map_some, Option.bind_some, h.esi, h.edi, e0, e1, e2, o0, o1,
    i0, i1, i2, w0, w1, ite_true, ite_false, Option.some.injEq, exists_eq_left', List.cons_append,
    List.nil_append]
  rw [hp.b_keep h.frame (by omega), hp.b_keep h.frame (by omega), hp.b_keep h.frame (by omega)]
  have hB : (B s₀).length = 384 := bytesAt_length _ _ _
  have v0 : V s₀ (2 * k) = BitVec.ofNat 32 ((((B s₀).getD (3 * k) 0).toNat +
      256 * (((B s₀).getD (3 * k + 1) 0).toNat % 16)) % q) := by
    rw [V, decode12_even _ hB (by omega), val_ofNat]
  have v1 : V s₀ (2 * k + 1) = BitVec.ofNat 32 ((((B s₀).getD (3 * k + 1) 0).toNat / 16 +
      16 * ((B s₀).getD (3 * k + 2) 0).toNat) % q) := by
    rw [V, decode12_odd _ hB (by omega), val_ofNat]
  generalize (B s₀).getD (3 * k) 0 = b0 at v0 v1 ⊢
  generalize (B s₀).getD (3 * k + 1) 0 = b1 at v0 v1 ⊢
  generalize (B s₀).getD (3 * k + 2) 0 = b2 at v0 v1 ⊢
  have l0 := b0.isLt
  have l1 := b1.isLt
  have l2 := b2.isLt
  have x0 : (b0.setWidth 32 + (b1.setWidth 32 &&& 15).rotateRight 24).toNat =
      b0.toNat + 256 * (b1.toNat % 16) := by
    have hm : (b1.setWidth 32 &&& 15).toNat = b1.toNat % 16 := by
      rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [hm]; omega), hm, toNat_byte32,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have x1 : (b1.setWidth 32 >>> 4 + (b2.setWidth 32).rotateRight 28).toNat =
      b1.toNat / 16 + 16 * b2.toNat := by
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [toNat_byte32]; omega), toNat_shr,
      toNat_byte32, toNat_byte32, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [csub_eq (b0.setWidth 32 + (b1.setWidth 32 &&& 15).rotateRight 24) _ (by rw [x0, q_eq]; omega),
    csub_eq (b1.setWidth 32 >>> 4 + (b2.setWidth 32).rotateRight 28) _ (by rw [x1, q_eq]; omega), x0, x1,
    ← v0, ← v1]
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, ptr_next _ _ 3, ptr_next _ _ 8, by rw [h.ecx]; exact cnt_next hk,
    ?_, ?_⟩, by simp only [eval, h.ecx]; exact cnt_ne hk (by decide)⟩
  · exact (h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; omega))
  · rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact coef_extend2 (by omega) h.coef


theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Inv s₀ 128) s₀ s')
    Impl.MlKem.X86.decode12 :=
  Piece.leafLoop (fun s₀ => [polyRegion (fA s₀)]) (fun k s₀ s => Inv s₀ k s)
    (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1) init_piece
    (Piece.countLoop (by decide) (fun k s₀ s => Inv s₀ k s) [.esp, .esi, .edi, .ecx]
      (fun _ hk _ _ hp h => step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, bP, bP, hq.2.1]
        · rw [h.edi, h'.edi, fP, fP, hq.2.2]
        · rw [h.ecx, h'.ecx]) (by taint_decide))
    fun _ _ _ h => ⟨h.frame, h.esp, h.rd, h.wr⟩

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.decode12 (decode12Contract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact polyIs_of_coeffAt fun i hi => hinv.coef i (by rw [n_eq] at hi; omega)
  · let st := satState satMem [⟨0, 384⟩] [⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
end VG.Proof.MlKem.X86.Decode12
