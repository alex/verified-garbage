import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr)

structure Ptrs (s s' : VG.AArch64.State) : Prop where
  x0 : s'.gpr .x0 = s.gpr .x0
  x1 : s'.gpr .x1 = s.gpr .x1
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Ptrs.refl (s : VG.AArch64.State) : Ptrs s s := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem Ptrs.trans {s t u : VG.AArch64.State} (h : Ptrs s t) (k : Ptrs t u) : Ptrs s u :=
  ⟨k.x0.trans h.x0,k.x1.trans h.x1,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem Keep.ptrs {s t : VG.AArch64.State} (h : Keep s t) : Ptrs s t :=
  ⟨congrFun h.gpr _,congrFun h.gpr _,h.rd,h.wr,h.sp⟩
theorem CoreKeep.ptrs {s t : VG.AArch64.State} (h : CoreKeep s t) : Ptrs s t :=
  ⟨h.gpr _ (by decide),h.gpr _ (by decide),h.rd,h.wr,h.sp⟩

theorem vreg_inj : ∀ i < 32, ∀ j < 32, vreg i = vreg j ↔ i = j := by decide

theorem exec_ldrq {s : VG.AArch64.State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec,addr,ho,and_self,ite_true,Option.bind_some,State.load,h,Option.map_some]

theorem exec_strq {s : VG.AArch64.State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s = some {s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t)} := by
  simp only [exec,addr,ho,and_self,ite_true,Option.bind_some,State.store,h]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.write p 16 v).read p 16 = v := by
  simpa only [Mem.readW,Mem.writeW,Nat.reduceMul,Nat.reduceDiv,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m p 16 v (by decide)

def Saved (s₀ : VG.AArch64.State) (m : Mem) : Prop :=
  ∀ i < 8, m.read (s₀.gpr .x1 + BitVec.ofNat 64 (16*i)) 16 = s₀.v (vreg (8+i))

theorem scratch_contains (s : VG.AArch64.State) {i : Nat} (hi : i < 8) :
    (⟨s.gpr .x1,512⟩ : Region).Contains (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16 :=
  Offset.contains_base _ (by omega) (by omega)

theorem state_pair_contains (s : VG.AArch64.State) {i : Nat} (hi : i < 12) :
    (⟨s.gpr .x0,200⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16 :=
  Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Sha3.AArch64.Sha3.Vector
