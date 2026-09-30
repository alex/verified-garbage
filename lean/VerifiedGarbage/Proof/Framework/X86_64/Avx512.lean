import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# x86-64: AVX-512 registers lane by lane

Untrusted: everything here is checked by Lean. The AVX-512 instructions of the
model, stated on one 128-bit lane of their operands (`State.zlane`, lanes 0
to 3) and on the doublewords of a lane.
-/

namespace VG.X86_64

/-! ## What an AVX-512 instruction leaves alone -/

@[simp] theorem State.setZ_gpr (s : State) (r : XReg) (a b c d : BitVec 128) :
    (s.setZ r a b c d).gpr = s.gpr := by
  cases s; rfl
@[simp] theorem State.setZ_mem (s : State) (r : XReg) (a b c d : BitVec 128) :
    (s.setZ r a b c d).mem = s.mem := by
  cases s; rfl
@[simp] theorem State.setZ_rd (s : State) (r : XReg) (a b c d : BitVec 128) :
    (s.setZ r a b c d).rd = s.rd := by
  cases s; rfl
@[simp] theorem State.setZ_wr (s : State) (r : XReg) (a b c d : BitVec 128) :
    (s.setZ r a b c d).wr = s.wr := by
  cases s; rfl
@[simp] theorem State.setZ_ea (s : State) (r : XReg) (a b c d : BitVec 128) (m : MemOp) :
    (s.setZ r a b c d).ea m = s.ea m := by
  cases s; rfl

@[simp] theorem ZOp.exec_gpr (o : ZOp) (s : State) : (o.exec s).gpr = s.gpr := by
  cases o <;> rfl
@[simp] theorem ZOp.exec_mem (o : ZOp) (s : State) : (o.exec s).mem = s.mem := by
  cases o <;> rfl
@[simp] theorem ZOp.exec_rd (o : ZOp) (s : State) : (o.exec s).rd = s.rd := by
  cases o <;> rfl
@[simp] theorem ZOp.exec_wr (o : ZOp) (s : State) : (o.exec s).wr = s.wr := by
  cases o <;> rfl
@[simp] theorem ZOp.exec_ea (o : ZOp) (s : State) (m : MemOp) : (o.exec s).ea m = s.ea m := by
  simp only [State.ea, ZOp.exec_gpr]

@[simp] theorem State.setMem_zlane (s : State) (m : Mem) (r : XReg) (l : Nat) :
    (s.setMem m).zlane r l = s.zlane r l := by
  cases s; rfl
@[simp] theorem State.setMem_zmmHi (s : State) (m : Mem) : (s.setMem m).zmmHi = s.zmmHi := by
  cases s; rfl

theorem State.store512_eq (s : State) (a : Addr) (v : BitVec 512) :
    s.store512 a v = if InRegions s.wr a 64 then some (s.setMem (s.mem.writeW a v)) else none := by
  rw [State.store512]; rfl

/-! ## Lanes -/

/-- Lane `i` of four values. -/
def pick4 (a b c d : BitVec 128) (i : Nat) : BitVec 128 :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

theorem State.zlane_setZ (s : State) (d r : XReg) (l0 l1 l2 l3 : BitVec 128) {i : Nat} (hi : i < 4) :
    (s.setZ d l0 l1 l2 l3).zlane r i = if r = d then pick4 l0 l1 l2 l3 i else s.zlane r i := by
  simp only [State.zlane, State.lane, State.setZ, pick4]
  by_cases h : r = d
  · subst h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp only [ite_true, show ¬ (2 < 2) by decide, ite_false, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hj]
    · simp only [ite_true, show ¬ (3 < 2) by decide, ite_false, show (3 : Nat) ≠ 0 by decide,
        show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      simp [hj]
  · simp [h]

theorem pick4_lanes (f : Nat → BitVec 128) {i : Nat} (hi : i < 4) : pick4 (f 0) (f 1) (f 2) (f 3) i = f i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem zlane_zbin (op : ZBinOp) (d a b : XReg) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.zbin op d a b).exec s).zlane r i =
      if r = d then op.sse.eval (s.zlane a i) (s.zlane b i) else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi,
    pick4_lanes (fun i => op.sse.eval (s.zlane a i) (s.zlane b i)) hi]

@[simp] theorem zlane_vprold (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vprold d a n).exec s).zlane r i = if r = d then rolDwords (s.zlane a i) n else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => rolDwords (s.zlane a i) n) hi]

@[simp] theorem zlane_vpshufd (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpshufd d a o).exec s).zlane r i = if r = d then shufDwords (s.zlane a i) o else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => shufDwords (s.zlane a i) o) hi]

@[simp] theorem zlane_vshufi32x4 (d a b : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat}
    (hi : i < 4) :
    ((ZOp.vshufi32x4 d a b n).exec s).zlane r i =
      if r = d then shuf4Lanes (s.zlane a) (s.zlane b) n i else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (shuf4Lanes (s.zlane a) (s.zlane b) n) hi]

/-- `shuf4Lanes` with a concrete selector. -/
theorem shuf4Lanes_eq (a b : Nat → BitVec 128) (n : BitVec 8) (j : Nat) :
    shuf4Lanes a b n j = (if j < 2 then a else b) (n.extractLsb' (2 * j) 2).toNat := by
  simp only [shuf4Lanes]; split <;> rfl

/-- The 512 bits of a register, as lanes. -/
theorem State.zmm_extract (s : State) (r : XReg) {l q : Nat} (hl : l < 4) (hq : q < 4) :
    (s.zmm r).extractLsb' (8 * (16 * l + 4 * q)) (8 * 4) = dword (s.zlane r l) q := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.zmm, State.ymm, State.zlane, State.lane, dword, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, decide_eq_true hj, Bool.true_and]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · simp only [show 8 * (16 * 0 + 4 * q) + j < 256 by omega, show 8 * (16 * 0 + 4 * q) + j < 128 by omega,
      ite_true, show (0 : Nat) < 2 by decide]
    exact congrArg _ (by omega)
  · simp only [show 8 * (16 * 1 + 4 * q) + j < 256 by omega, show ¬ 8 * (16 * 1 + 4 * q) + j < 128 by omega,
      ite_true, ite_false, show (1 : Nat) < 2 by decide, show (1 : Nat) ≠ 0 by decide]
    exact congrArg _ (by omega)
  · simp only [show ¬ 8 * (16 * 2 + 4 * q) + j < 256 by omega, ite_false, show ¬ (2 : Nat) < 2 by decide,
      BitVec.getLsbD_extractLsb', decide_eq_true (show 32 * q + j < 128 by omega), Bool.true_and]
    exact congrArg _ (by omega)
  · simp only [show ¬ 8 * (16 * 3 + 4 * q) + j < 256 by omega, ite_false, show ¬ (3 : Nat) < 2 by decide,
      BitVec.getLsbD_extractLsb', decide_eq_true (show 32 * q + j < 128 by omega), Bool.true_and]
    exact congrArg _ (by omega)

/-! ## Doublewords -/

theorem dword_rolDwords (a : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 4) :
    dword (rolDwords a n) i = (dword a i).rotateLeft (n.toNat % 32) := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [rolDwords]

end VG.X86_64
