import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Rotation
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Store
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64.Key (keyKept)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .x19 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .x20 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .x21 = BitVec.ofNat 64 j
  pointer : s.gpr .x22 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.AArch64.Key.rotation (.block Impl.TripleDes.AArch64.Key.storeRound)) s
      (fun s' => isa.eval (.nonzero .x .x4) s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ (keyKept ++ [.x21, .x22]),
      r ≠ .x4 ∧ r ≠ .x19 ∧ r ≠ .x20 := by decide
  have reg₁ : ∀ r ∈ (keyKept ++ [.x21, .x22]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have write₁ : InRegions s₁.wr (s₁.gpr .x22) 8 := by
    rw [h₁.wr, hs.wr, reg₁ .x22 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .x21 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .x22 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .x19 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .x20 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .x22 (by decide), hs.pointer]
    change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega)
  · intro i hi hi16
    rw [hmem, keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_using [hi, he])
        (by omega_using [hi16]) (by omega_using [hj])) (by decide), hs.keys i (by omega_using [hi, he]) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · intro r hr
    have incl : ∀ r ∈ keyKept,
        r ∈ (keyKept ++ [.x19, .x20]) ∧
        r ∈ (keyKept ++ [.x21, .x22]) := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.AArch64.Key.rotation (.block Impl.TripleDes.AArch64.Key.storeRound)) s
      (fun s' => (isa.eval (.nonzero .x .x4) s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval (.nonzero .x .x4) s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simpa only [idx, ne_eq, not_true_eq_false, decide_false] using h.1
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simpa only [idx, ne_eq, not_false_eq_true, decide_true] using h.1
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : Addr) (s : State)
    (hw : ∀ j < 16, InRegions s.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (hc : s.gpr .x19 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .x20 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .x21 = 0) (hptr : s.gpr .x22 = base) :
    WP isa (.loop (.seq Impl.TripleDes.AArch64.Key.rotation
      (.block Impl.TripleDes.AArch64.Key.storeRound)) (.nonzero .x .x4)) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.AArch64.Key.rotation
      (.block Impl.TripleDes.AArch64.Key.storeRound)) (c := .nonzero .x .x4)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.AArch64.Key
