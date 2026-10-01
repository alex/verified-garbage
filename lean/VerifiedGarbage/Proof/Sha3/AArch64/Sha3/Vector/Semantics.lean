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
