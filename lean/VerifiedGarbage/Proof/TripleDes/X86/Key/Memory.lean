import VerifiedGarbage.Proof.TripleDes.X86.Key.Store

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)

def scheduleRegion (base : BitVec 32) : Region := ⟨addr32 base, 128⟩

theorem pointer_fit (base : BitVec 32) (fit : base.toNat + 128 ≤ 2 ^ 32)
    (j : Nat) (hj : j < 16) : (base + BitVec.ofNat 32 (8 * j)).toNat + 8 ≤ 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 8 * j < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : base.toNat + 8 * j < 2 ^ 32)]
  omega

theorem schedule_contains (base : BitVec 32) (j : Nat) (hj : j < 16) :
    (scheduleRegion base).Contains (addr32 base + BitVec.ofNat 64 (8 * j)) 8 :=
  Offset.contains_base _ (by omega) (by omega)

theorem work_slot (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (k : Nat) (hk : k = 4 ∨ k = 5) :
    (workRegion s).Contains (wordAddr (s.gpr .ebp) k) 4 := by
  change (workRegion s).Contains (addr (s.gpr .ebp) (4 * k)) 4
  rw [addr_eq (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem keyStore_read (s : State) (k : BitVec 64) (p : Addr)
    (hsep : ∀ j ∈ [4, 5], Mem.Sep p 8 (wordAddr (s.gpr .ebp) j) 4) :
    (keyStoreMem s k).readW p 64 = (s.mem.writeW (wordAddr (roundKeyPtr s) 0) k).readW p 64 := by
  rw [keyStoreMem, Mem.readW_writeW_sep (hsep 5 (by decide)) (by decide),
    Mem.readW_writeW_sep (hsep 4 (by decide)) (by decide)]

theorem keyStore_frame (s : State) (base : BitVec 32) (j : Nat) (hj : j < 16)
    (fit : base.toNat + 128 ≤ 2 ^ 32) (scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (ptr : roundKeyPtr s = base + BitVec.ofNat 32 (8 * j)) (k : BitVec 64) :
    Frame [scheduleRegion base, workRegion s] s.mem (keyStoreMem s k) := by
  have hc : (scheduleRegion base).Contains (wordAddr (roundKeyPtr s) 0) 8 := by
    rw [ptr]
    have ha : wordAddr (base + BitVec.ofNat 32 (8 * j)) 0 =
        addr32 base + BitVec.ofNat 64 (8 * j) := by
      simpa [wordAddr, addr, addr32] using
        (VG.Proof.Rc2.X86.addr_add (x := base) (k := 8 * j) (by omega))
    rw [ha]
    exact schedule_contains base j hj
  exact (((Frame.refl _ _).writeW (by simp) k hc).writeW (by simp) _
    (work_slot s scratchFit 4 (Or.inl rfl))).writeW (by simp) _
    (work_slot s scratchFit 5 (Or.inr rfl))

end VG.Proof.TripleDes.X86.Key
