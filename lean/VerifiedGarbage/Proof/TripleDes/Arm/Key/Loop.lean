import VerifiedGarbage.Proof.TripleDes.Arm.Key.Rotation
import VerifiedGarbage.Proof.TripleDes.Arm.Key.Store
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm
open VG.Proof.TripleDes.Arm.Key (keyKept)
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

theorem pointer_fit (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j : Nat) (hj : j < 16) : (base + BitVec.ofNat 32 (8 * j)).toNat + 8 ≤ 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_using [hj] : 8 * j < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [fit, hj] : base.toNat + 8 * j < 2 ^ 32)]
  omega_using [fit, hj]

structure LoopState (key : BitVec 64) (base : BitVec 32) (origin : State) (j : Nat) (s : State) : Prop where
  c : s.gpr .r10 = (keyPrefix key j).1.setWidth 32
  d : s.gpr .r11 = (keyPrefix key j).2.1.setWidth 32
  counter : s.gpr .r9 = BitVec.ofNat 32 j
  pointer : s.gpr .r8 = base + BitVec.ofNat 32 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (State.addr base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨State.addr base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : BitVec 32) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (State.addr (base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.Arm.Key.rotation (.block Impl.TripleDes.Arm.Key.storeRound)) s
      (fun s' => isa.eval .ne s' = some (decide (j ≠ 15)) ∧ LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have unused : ∀ r ∈ (keyKept ++ [.r9, .r8]),
      r ≠ .r4 ∧ r ≠ .r10 ∧ r ≠ .r11 := by decide
  have reg₁ : ∀ r ∈ (keyKept ++ [.r9, .r8]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.reg r (unused r hr).1 (unused r hr).2.1 (unused r hr).2.2
  have fit₁ : (s₁.gpr .r8).toNat + 8 ≤ 2 ^ 32 := by
    rw [reg₁ .r8 (by decide), hs.pointer]
    exact pointer_fit base fit j hj
  have write₁ : ∀ t < 2, InRegions s₁.wr
      (State.addr (s₁.gpr .r8 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [h₁.wr, hs.wr, reg₁ .r8 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .r9 (by decide)).trans hs.counter) fit₁ write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (State.addr base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.mem, reg₁ .r8 (by decide), hs.pointer, addr_add (by omega_using [fit, hj])]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.rd.trans hs.rd),
    h₂.wr.trans (h₁.wr.trans hs.wr), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .r10 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .r11 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .r8 (by decide), hs.pointer]
    change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · intro i hi hi16
    rw [hmem, keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep (State.addr base) (by omega_using [hi, he])
        (by omega_using [hi16]) (by omega_using [hj])) (by decide), hs.keys i (by omega_using [hi, he]) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · intro r hr
    have incl : ∀ r ∈ keyKept,
        r ∈ (keyKept ++ [.r10, .r11]) ∧
        r ∈ (keyKept ++ [.r9, .r8]) := by decide
    exact (h₂.reg r (incl r hr).1).trans ((reg₁ r (incl r hr).2).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base (State.addr base) (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : BitVec 32) (origin : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32)
    (hw : ∀ j < 16, ∀ t < 2, InRegions origin.wr
      (State.addr (base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.Arm.Key.rotation (.block Impl.TripleDes.Arm.Key.storeRound)) s
      (fun s' => (isa.eval .ne s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin fit hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
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

theorem loop_ok (key : BitVec 64) (base : BitVec 32) (s : State)
    (fit : base.toNat + 128 ≤ 2 ^ 32)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (State.addr (base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4)
    (hc : s.gpr .r10 = (keyInitial key).1.setWidth 32)
    (hd : s.gpr .r11 = (keyInitial key).2.1.setWidth 32)
    (hcount : s.gpr .r9 = 0) (hptr : s.gpr .r8 = base) :
    WP isa (.loop (.seq Impl.TripleDes.Arm.Key.rotation
      (.block Impl.TripleDes.Arm.Key.storeRound)) .ne) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.Arm.Key.rotation
      (.block Impl.TripleDes.Arm.Key.storeRound)) (c := .ne)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s fit hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

end VG.Proof.TripleDes.Arm.Key
