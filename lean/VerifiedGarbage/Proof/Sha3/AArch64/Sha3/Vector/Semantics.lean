import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

abbrev Low := VReg → BitVec 64

def low (s : VG.AArch64.State) : Low := fun r => vdword (s.v r) 0

/-- Canonical state, with no assumption about the upper vector lanes. -/
def Lanes (s : VG.AArch64.State) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), low s (vreg i) = A[i]

/-- Scalar and memory fields untouched by a vector-only block. -/
structure Keep (s s' : VG.AArch64.State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : VG.AArch64.State) : Keep s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s₀ s₁ s₂ : VG.AArch64.State} (h : Keep s₀ s₁) (k : Keep s₁ s₂) : Keep s₀ s₂ :=
  ⟨k.gpr.trans h.gpr, k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

/-- A property of the first 25 numbers, one at a time. -/
theorem forall_lt_25 {P : Nat → Prop}
    (h : P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 ∧ P 10 ∧ P 11 ∧ P 12 ∧
      P 13 ∧ P 14 ∧ P 15 ∧ P 16 ∧ P 17 ∧ P 18 ∧ P 19 ∧ P 20 ∧ P 21 ∧ P 22 ∧ P 23 ∧ P 24) :
    ∀ i < 25, P i := by
  intro i hi
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  match i, hi with
  | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3 | 4, _ => exact h4
  | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7 | 8, _ => exact h8 | 9, _ => exact h9
  | 10, _ => exact h10 | 11, _ => exact h11 | 12, _ => exact h12 | 13, _ => exact h13
  | 14, _ => exact h14 | 15, _ => exact h15 | 16, _ => exact h16 | 17, _ => exact h17
  | 18, _ => exact h18 | 19, _ => exact h19 | 20, _ => exact h20 | 21, _ => exact h21
  | 22, _ => exact h22 | 23, _ => exact h23 | 24, _ => exact h24
  | _ + 25, h => exact absurd h (by omega)

def put (σ : Low) (d : VReg) (w : BitVec 64) : Low := fun r => if r = d then w else σ r

def opLow (σ : Low) : Op → Low
  | .xor d n m => put σ d (σ n ^^^ σ m)
  | .eor3 d n m a => put σ d (σ n ^^^ σ m ^^^ σ a)
  | .rax1 d n m => put σ d (σ n ^^^ (σ m).rotateLeft 1)
  | .xar d n m k => put σ d ((σ n ^^^ σ m).rotateRight k.val)
  | .bcax d n m a => put σ d (σ n ^^^ (σ m &&& ~~~(σ a)))

def opState (s : VG.AArch64.State) : Op → VG.AArch64.State
  | .xor d n m => s.setV d (s.v n ^^^ s.v m)
  | .eor3 d n m a => s.setV d (s.v n ^^^ s.v m ^^^ s.v a)
  | .rax1 d n m => s.setV d (VArr.d2.map2 (fun _ x y => x ^^^ y.rotateLeft 1) (s.v n) (s.v m))
  | .xar d n m k => s.setV d (VArr.d2.map2 (fun _ x y => (x ^^^ y).rotateRight k.val) (s.v n) (s.v m))
  | .bcax d n m a => s.setV d (s.v n ^^^ (s.v m &&& ~~~(s.v a)))

theorem op_exec (s : VG.AArch64.State) (op : Op) : exec op.instr s = some (opState s op) := by
  cases op <;> simp only [Op.instr, exec_vop, VOp.eval, opState, Option.map_some]
  rename_i k
  simp only [k.isLt, ite_true, Option.map_some]

theorem op_keep (s : VG.AArch64.State) (op : Op) : Keep s (opState s op) := by
  cases op <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem low_setV (s : VG.AArch64.State) (d : VReg) (v : BitVec 128) :
    low (s.setV d v) = put (low s) d (vdword v 0) := by
  funext r
  simp only [low, put, RegUpd.v_setV]
  split <;> rfl

theorem op_low (s : VG.AArch64.State) (op : Op) : low (opState s op) = opLow (low s) op := by
  cases op <;> simp only [opState, low_setV, opLow, low_xor, low_and, low_not,
    VArr.map2, vdword_ofVDwords_0, low]

def runLow (ops : List Op) (σ : Low) : Low := ops.foldl opLow σ

theorem ops_ok (ops : List Op) (s : VG.AArch64.State) :
    WP isa (.block (ops.map Op.instr)) s fun s' => Keep s s' ∧ low s' = runLow ops (low s) := by
  induction ops generalizing s with
  | nil => exact wp_nil ⟨Keep.refl s, rfl⟩
  | cons op ops ih =>
    refine WP.cons (op_exec s op) ((ih (opState s op)).mono fun s' h => ?_)
    refine ⟨(op_keep s op).trans h.1, ?_⟩
    simpa only [runLow, List.foldl_cons, op_low] using h.2

end VG.Proof.Sha3.AArch64.Sha3.Vector
