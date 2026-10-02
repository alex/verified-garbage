import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.EkCheck
import VerifiedGarbage.Impl.MlKem.X86.CheckEk
import VerifiedGarbage.Proof.MlKem.X86.TopKem
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): the encapsulation key check

`checkEkN (128k)`, for a parameter set `p` with `k = p.k`: after `t` groups,
`ebx` is all ones if both fields of every group so far are less than `q`, and
0 otherwise (`mask`); the modulus check is that for all `128k` groups
(`ekCheck_iff`). Each parameter set's contract implies `Pre p`
(`Proof/MlKem/X86/CheckEk.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.CheckEk

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev eP : BitVec 32 := arg s₀ 0
abbrev eA : Addr := (eP s₀).setWidth 64
end

section
variable (p : Params) (s₀ : State)
abbrev eR : Region := ⟨eA s₀, p.ekLen⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 4 * 1⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (eA s₀) p.ekLen
end

structure Pre (p : Params) (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * 1 ≤ 2 ^ 32
  rd : s₀.rd = [eR p s₀, aR s₀]
  wr : s₀.wr = []
  ret_e : (retR s₀).Disjoint (eR p s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_e : (stkR s₀).Disjoint (eR p s₀)
  stk_a : (stkR s₀).Disjoint (aR s₀)
  e_fit : (eP s₀).toNat + p.ekLen ≤ 2 ^ 32

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0

/-- Both fields of every group before `t` are less than `q`. -/
def ok (L : List Byte) (t : Nat) : Prop := ∀ g < t, field0 L g < q ∧ field1 L g < q

instance (L : List Byte) (t : Nat) : Decidable (ok L t) := by unfold ok; infer_instance

/-- All ones if `ok`, 0 otherwise. -/
def mask (p : Prop) [Decidable p] : BitVec 32 := if p then 0xffffffff else 0

variable {p : Params}

/-- After `t` groups. -/
structure Inv (p : Params) (s₀ : State) (t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = eP s₀ + BitVec.ofNat 32 (3 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (128 * p.k - t)
  ebx : s.gpr .ebx = mask (ok (K p s₀) t)

theorem sbb_mask (x : BitVec 32) (c : Bool) :
    x - x - (BitVec.ofBool c).setWidth 32 = if c then 0xffffffff else 0 := by
  rw [BitVec.sub_self]; cases c <;> rfl

theorem ok_succ (L : List Byte) (t : Nat) :
    ok L (t + 1) ↔ ok L t ∧ field0 L t < q ∧ field1 L t < q :=
  ⟨fun h => ⟨fun g hg => h g (by omega), h t (by omega)⟩, fun ⟨h, h'⟩ g hg => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | rfl
    · exact h g hg
    · exact h'⟩

theorem mask_succ (L : List Byte) (t : Nat) :
    mask (ok L t) &&& (if decide (field0 L t < 3329) then 0xffffffff else 0) &&&
      (if decide (field1 L t < 3329) then 0xffffffff else 0) = mask (ok L (t + 1)) := by
  have e : ok L (t + 1) ↔ ok L t ∧ field0 L t < 3329 ∧ field1 L t < 3329 := by rw [ok_succ, q_eq]
  simp only [mask]
  by_cases h : ok L t <;> by_cases h0 : field0 L t < 3329 <;> by_cases h1 : field1 L t < 3329 <;>
    simp only [h, h0, h1, e, decide_true, decide_false, ite_true, ite_false, and_self, and_true,
      and_false] <;> decide

namespace Pre
variable {s₀ : State} (hp : Pre p s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem byte {j : Nat} (hj : j < p.ekLen) : (P0 s₀).mem (eA s₀ + BitVec.ofNat 64 j) = (K p s₀).getD j 0 := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf
  rw [bytesAt_getD _ _ hj, hf.bytes (R := eR p s₀) (by simpa [← hp.stk_eq] using hp.stk_e.symm)
    (by show p.ekLen ≤ 2 ^ 64; have := hp.e_fit; omega) hj]

end Pre

theorem init_piece : Piece (Pre p) Pub (fun s₀ s => s = P0 s₀) (Inv p · 0) (.block (ekInitN (128 * p.k))) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_rfl)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have i₀ := P0_argIn (s₀ := s₀) (n := 1) (i := 0) (by omega) fit (by simp [hp.rd])
    have v₀ := P0_arg hp.sp (n := 1) (i := 0) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero] at a₀
    apply WP.of_runBlock
    simp (config := {decide := true}) only [ekInitN, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, i₀, v₀, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, rfl, by simp, by simp, ?_⟩
    simp only [ite_true, mask]
    rw [ite_eq_left (show ok (K p s₀) 0 from fun g hg => absurd hg (Nat.not_lt_zero g))]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem step {s₀ : State} (hp : Pre p s₀) {t : Nat} (ht : t < 128 * p.k) {s : State} (h : Inv p s₀ t s) :
    WP isa (.block ekBody) s fun s' => Inv p s₀ (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < 128 * p.k)) := by
  have fe := hp.e_fit
  have hE : p.ekLen = 384 * p.k + 32 := rfl
  have eb : ∀ o < 3, (eP s₀ + BitVec.ofNat 32 (3 * t) + BitVec.ofNat 32 o).setWidth 64 =
      eA s₀ + BitVec.ofNat 64 (3 * t + o) := fun o ho => ea_add (by omega)
  have e0 := eb 0 (by omega)
  have e1 := eb 1 (by omega)
  have e2 := eb 2 (by omega)
  have inE : ∀ o < 3, InRegions (s.rd ++ s.wr) (eA s₀ + BitVec.ofNat 64 (3 * t + o)) 1 := fun o ho =>
    ⟨eR p s₀, List.mem_append_left _ (by rw [h.rd, pushed_rd, hp.rd]; simp), contains_at (by omega) fe⟩
  have i0 := inE 0 (by omega)
  have i1 := inE 1 (by omega)
  have i2 := inE 2 (by omega)
  have v : ∀ o < 3, s.mem (eA s₀ + BitVec.ofNat 64 (3 * t + o)) = (K p s₀).getD (3 * t + o) 0 :=
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
  have x0 : (BitVec.setWidth 32 ((K p s₀).getD (3 * t) 0) +
      (BitVec.setWidth 32 ((K p s₀).getD (3 * t + 1) 0) &&& 15).rotateRight 24).toNat = field0 (K p s₀) t := by
    have l0 := ((K p s₀).getD (3 * t) 0).isLt
    have l1 := ((K p s₀).getD (3 * t + 1) 0).isLt
    have hm : (BitVec.setWidth 32 ((K p s₀).getD (3 * t + 1) 0) &&& 15).toNat =
        ((K p s₀).getD (3 * t + 1) 0).toNat % 16 := by
      rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [hm]; omega), hm, toNat_byte32,
      Nat.mod_eq_of_lt (by omega), field0]
    omega
  have x1 : (BitVec.setWidth 32 ((K p s₀).getD (3 * t + 1) 0) >>> 4 +
      (BitVec.setWidth 32 ((K p s₀).getD (3 * t + 2) 0)).rotateRight 28).toNat = field1 (K p s₀) t := by
    have l1 := ((K p s₀).getD (3 * t + 1) 0).isLt
    have l2 := ((K p s₀).getD (3 * t + 2) 0).isLt
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

theorem mask_and1 (p : Prop) [Decidable p] : mask p &&& 1 = if p then 1 else 0 := by
  unfold mask
  by_cases e : p
  · rw [ite_eq_left e, ite_eq_left e]; decide
  · rw [ite_eq_right e, ite_eq_right e]; decide

/-- The end: the result in `eax`. -/
structure Fin (p : Params) (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = if ok (K p s₀) (128 * p.k) then 1 else 0

theorem end_piece : Piece (Pre p) Pub (Inv p · (128 * p.k)) (Fin p) (.block ekEnd) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [ekEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.map_some,
    Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨by simp [h.esp], h.rd, h.wr, h.mem, ?_⟩
  simp only [ite_true]
  rw [h.ebx, mask_and1]

theorem loop_piece (hk : 0 < p.k) : Piece (Pre p) Pub (Inv p · 0) (Inv p · (128 * p.k)) (.loop (.block ekBody) .ne) :=
  Piece.countLoop (by omega) (fun t s₀ s => Inv p s₀ t s) [.esp, .esi, .ecx]
    (fun t ht s₀ s hp h => step hp ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
      · rw [h.esi, h'.esi, eP, eP, hq.2]
      · rw [h.ecx, h'.ecx]) (by taint_decide)

theorem piece (hk : 0 < p.k) (hsp : NoSp (.seq (.block (ekInitN (128 * p.k)))
      (.seq (.loop (.block ekBody) .ne) (.block ekEnd)))) :
    Piece (Pre p) Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin p s₀) s₀ s') (checkEkN (128 * p.k)) :=
  Piece.leaf (fun _ => []) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ _ r hr => absurd hr (by simp)) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq init_piece (Piece.seq (loop_piece hk) end_piece)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨by rw [h.mem]; exact Frame.refl _ _, h.esp, h.rd, h.wr⟩ |> fun e => ⟨e, h⟩)

theorem ok_iff {s₀ : State} : ekCheck p (K p s₀) = true ↔ ok (K p s₀) (128 * p.k) :=
  ekCheck_iff p _ (bytesAt_length _ _ _)

end VG.Proof.MlKem.X86.CheckEk
