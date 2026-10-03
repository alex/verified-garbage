import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector

def lane (s : State) (e : Nat) : Low := fun r => vdword (s.v r) e

theorem lane_xor (a b : BitVec 128) (e : Nat) : vdword (a ^^^ b) e = vdword a e ^^^ vdword b e := by
  simp only [vdword,BitVec.extractLsb'_xor]
theorem lane_and (a b : BitVec 128) (e : Nat) : vdword (a &&& b) e = vdword a e &&& vdword b e := by
  simp only [vdword,BitVec.extractLsb'_and]
theorem lane_not (a : BitVec 128) {e : Nat} (he : e < 2) : vdword (~~~a) e = ~~~vdword a e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_not,hi,decide_true,Bool.true_and,
    show 64*e+i < 128 by omega]

theorem lane_setV (s : State) (d : VReg) (v : BitVec 128) (e : Nat) :
    lane (s.setV d v) e = put (lane s e) d (vdword v e) := by
  funext r
  simp only [lane,put,RegUpd.v_setV]
  split <;> rfl

theorem op_lane (s : State) (op : Op) {e : Nat} (he : e < 2) :
    lane (opState s op) e = opLow (lane s e) op := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact op_low s op
  · cases op <;> simp only [opState,lane_setV,opLow,lane_xor,lane_and,lane_not _ (by decide : 1 < 2),
      VArr.map2,vdword_ofVDwords_1,lane]

/-- The SHA3 instructions operate independently on both 64-bit lanes. -/
theorem ops_lanes (ops : List Op) (s : State) :
    WP isa (.block (ops.map Op.instr)) s fun t => Keep s t ∧
      ∀ e < 2,lane t e = runLow ops (lane s e) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil_iff.mpr ⟨Keep.refl _,fun _ _ => rfl⟩
  | cons op ops ih =>
    refine VG.Proof.Sha3.AArch64.WP.cons (op_exec s op)
      (WP.mono (ih (opState s op)) fun t ⟨ht,hl⟩ => ⟨(op_keep s op).trans ht,?_⟩)
    intro e he
    rw [hl e he,op_lane s op he]
    rfl

/-- The existing register schedule's pure mathematics applies to either lane. -/
theorem core_math (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) :
    CLanes (runLow (theta++rhoPi++chi) σ) A := by
  have ht := theta_lanes σ A h
  have hd : DLanes (runLow theta σ) A := theta_d σ A h
  have hr := rho_lanes (runLow theta σ) A ht hd
  have hc := chi_lanes (runLow rhoPi (runLow theta σ)) A hr
  simpa only [runLow,List.foldl_append] using hc
end VG.Proof.Sha3.AArch64.Neon.Hw
