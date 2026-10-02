import VerifiedGarbage.Proof.MlKem.X86.CheckEk
import VerifiedGarbage.Proof.MlKem.EkCheck
import VerifiedGarbage.Impl.MlKem1024.X86.CheckEk
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_check_ek`

As `vg_mlkem768_check_ek` (`Proof/MlKem/X86/CheckEk.lean`, whose `ok`, `mask`
and lemmas on them this uses): after `t` groups, `ebx` is all ones if both
fields of every group so far are less than `q`, and 0 otherwise; the modulus
check is that for all 512 groups (`ekCheck1024`).
-/

namespace VG.Proof.MlKem1024.X86.CheckEk

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.CheckEk (ok mask sbb_mask ok_succ mask_succ mask_and1)

section
variable (s₀ : State)
abbrev eP : BitVec 32 := arg s₀ 0
abbrev eA : Addr := (eP s₀).setWidth 64
abbrev eR : Region := ⟨eA s₀, 1568⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 4 * 1⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (eA s₀) 1568
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * 1 ≤ 2 ^ 32
  rd : s₀.rd = [eR s₀, aR s₀]
  wr : s₀.wr = []
  ret_e : (retR s₀).Disjoint (eR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_e : (stkR s₀).Disjoint (eR s₀)
  stk_a : (stkR s₀).Disjoint (aR s₀)
  e_fit : (eP s₀).toNat + 1568 ≤ 2 ^ 32

theorem Pre.of {s₀ : State} (h : (Spec.MlKem1024.checkEkContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0

/-- After `t` groups. -/
structure Inv (s₀ : State) (t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = eP s₀ + BitVec.ofNat 32 (3 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (512 - t)
  ebx : s.gpr .ebx = mask (ok (K s₀) t)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem byte {j : Nat} (hj : j < 1568) : (P0 s₀).mem (eA s₀ + BitVec.ofNat 64 j) = (K s₀).getD j 0 := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf
  rw [bytesAt_getD _ _ hj, hf.bytes (R := eR s₀) (by simpa [← hp.stk_eq] using hp.stk_e.symm)
    (by show 1568 ≤ 2 ^ 64; decide) hj]

end Pre

theorem init_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (Inv · 0) (.block ekInit512) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have i₀ := P0_argIn (s₀ := s₀) (n := 1) (i := 0) (by omega) fit (by simp [hp.rd])
    have v₀ := P0_arg hp.sp (n := 1) (i := 0) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero] at a₀
    apply WP.of_runBlock
    simp (config := {decide := true}) only [ekInit512, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, i₀, v₀, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, rfl, by simp, by simp, ?_⟩
    simp only [ite_true, mask]
    rw [ite_eq_left (show ok (K s₀) 0 from fun g hg => absurd hg (Nat.not_lt_zero g))]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem step {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 512) {s : State} (h : Inv s₀ t s) :
    WP isa (.block ekBody) s fun s' => Inv s₀ (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < 512)) := by
  have fe := hp.e_fit
  have eb : ∀ o < 3, (eP s₀ + BitVec.ofNat 32 (3 * t) + BitVec.ofNat 32 o).setWidth 64 =
      eA s₀ + BitVec.ofNat 64 (3 * t + o) := fun o ho => ea_add (by omega)
  have e0 := eb 0 (by omega)
  have e1 := eb 1 (by omega)
  have e2 := eb 2 (by omega)
  have inE : ∀ o < 3, InRegions (s.rd ++ s.wr) (eA s₀ + BitVec.ofNat 64 (3 * t + o)) 1 := fun o ho =>
    ⟨eR s₀, List.mem_append_left _ (by rw [h.rd, pushed_rd, hp.rd]; simp), contains_at (by omega) fe⟩
  have i0 := inE 0 (by omega)
  have i1 := inE 1 (by omega)
  have i2 := inE 2 (by omega)
  have v : ∀ o < 3, s.mem (eA s₀ + BitVec.ofNat 64 (3 * t + o)) = (K s₀).getD (3 * t + o) 0 :=
    fun o ho => by rw [h.mem, hp.byte (by omega)]
  have v0 := v 0 (by omega)
  have v1 := v 1 (by omega)
  have v2 := v 2 (by omega)
  simp only [Nat.add_zero] at e0 i0 v0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ekBody, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, e1, e2, i0, i1, i2, v0, v1, v2, sbb_mask, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  have x0 : (BitVec.setWidth 32 ((K s₀).getD (3 * t) 0) +
      (BitVec.setWidth 32 ((K s₀).getD (3 * t + 1) 0) &&& 15).rotateRight 24).toNat = field0 (K s₀) t := by
    have l0 := ((K s₀).getD (3 * t) 0).isLt
    have l1 := ((K s₀).getD (3 * t + 1) 0).isLt
    have hm : (BitVec.setWidth 32 ((K s₀).getD (3 * t + 1) 0) &&& 15).toNat =
        ((K s₀).getD (3 * t + 1) 0).toNat % 16 := by
      rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [hm]; omega), hm, toNat_byte32,
      Nat.mod_eq_of_lt (by omega), field0]
    omega
  have x1 : (BitVec.setWidth 32 ((K s₀).getD (3 * t + 1) 0) >>> 4 +
      (BitVec.setWidth 32 ((K s₀).getD (3 * t + 2) 0)).rotateRight 28).toNat = field1 (K s₀) t := by
    have l1 := ((K s₀).getD (3 * t + 1) 0).isLt
    have l2 := ((K s₀).getD (3 * t + 2) 0).isLt
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [toNat_byte32]; omega), toNat_shr,
      toNat_byte32, toNat_byte32, Nat.mod_eq_of_lt (by omega), field1]
    omega
  simp only [x0, x1, show Q.toNat = 3329 from rfl, h.ebx, mask_succ]
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, h.mem, ?_, ?_, by simp⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, ite_false, ite_true]
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · simp only [eval, h.ecx]
    exact cnt_ne ht (by omega)

/-- The end: the result in `eax`. -/
structure Fin (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = if ok (K s₀) 512 then 1 else 0

theorem end_piece : Piece Pre Pub (Inv · 512) Fin (.block ekEnd) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [ekEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.map_some,
    Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨by simp [h.esp], h.rd, h.wr, h.mem, ?_⟩
  simp only [ite_true]
  rw [h.ebx, mask_and1]

theorem loop_piece : Piece Pre Pub (Inv · 0) (Inv · 512) (.loop (.block ekBody) .ne) :=
  Piece.countLoop (by decide) (fun t s₀ s => Inv s₀ t s) [.esp, .esi, .ecx]
    (fun t ht s₀ s hp h => step hp ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
      · rw [h.esi, h'.esi, eP, eP, hq.2]
      · rw [h.ecx, h'.ecx]) (by taint_decide)

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem1024.X86.checkEk :=
  Piece.leaf (fun _ => []) (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ _ r hr => absurd hr (by simp)) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq init_piece (Piece.seq loop_piece end_piece)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨by rw [h.mem]; exact Frame.refl _ _, h.esp, h.rd, h.wr⟩ |> fun e => ⟨e, h⟩)

theorem ok_iff {s₀ : State} : ekCheck mlKem1024 (K s₀) = true ↔ ok (K s₀) 512 :=
  ekCheck1024 _ (bytesAt_length _ _ _)

/-- All-zero memory. -/
def satMem : Mem := fun _ => 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.checkEk (Spec.MlKem1024.checkEkContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hinv.eax]
    by_cases e : ok (K s₀) 512
    · rw [ite_eq_left e]; exact (ite_eq_left (ok_iff.mpr e)).symm
    · rw [ite_eq_right e]; exact (ite_eq_right fun h => e (ok_iff.mp h)).symm
  · let st := satState satMem [⟨0, 1568⟩, ⟨0x5004, 4⟩] []
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.CheckEk
