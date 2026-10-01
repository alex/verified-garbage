import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

/-- The scalar/memory fields preserved by all rounds. -/
structure CoreKeep (s s' : VG.AArch64.State) : Prop where
  gpr : ∀ r, r ≠ .x16 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem CoreKeep.refl (s : VG.AArch64.State) : CoreKeep s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem CoreKeep.trans {s₀ s₁ s₂ : VG.AArch64.State}
    (h : CoreKeep s₀ s₁) (k : CoreKeep s₁ s₂) : CoreKeep s₀ s₂ :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

theorem Keep.core {s s' : VG.AArch64.State} (h : Keep s s') : CoreKeep s s' :=
  ⟨fun r _ => congrFun h.gpr r, h.mem, h.rd, h.wr, h.sp⟩

def movkValue (w : BitVec 64) (v : BitVec 16) (hw : Nat) : BitVec 64 :=
  (w &&& ~~~((65535 : BitVec 64) <<< (16 * hw))) ||| (v.setWidth 64 <<< (16 * hw))

def constantLow (v : BitVec 64) : BitVec 64 :=
  let w := (v.extractLsb' 0 16).setWidth 64 <<< (16 * 0)
  let w := if v.extractLsb' 16 16 = 0 then w else movkValue w (v.extractLsb' 16 16) 1
  let w := if v.extractLsb' 32 16 = 0 then w else movkValue w (v.extractLsb' 32 16) 2
  if v.extractLsb' 48 16 = 0 then w else movkValue w (v.extractLsb' 48 16) 3

/-- A finite, kernel-checked fact about the 24 public round constants. -/
theorem constantLow_RC : ∀ r < 24, constantLow (Spec.Sha3.RC r) = Spec.Sha3.RC r := by
  decide +kernel

theorem constant_ok (v : BitVec 64) (s : VG.AArch64.State) :
    WP isa (.block (constant v)) s fun s' =>
      CoreKeep s s' ∧ s'.v = s.v ∧ s'.gpr .x16 = constantLow v := by
  by_cases h1 : v.extractLsb' 16 16 = 0 <;>
    by_cases h2 : v.extractLsb' 32 16 = 0 <;>
    by_cases h3 : v.extractLsb' 48 16 = 0
  all_goals
    simp only [constant, h1, h2, h3, ite_true, ite_false,
      List.cons_append, List.nil_append]
    repeat' apply WP.cons rfl
    apply wp_nil
    refine ⟨⟨?_, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
    · intro r hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · simp only [constantLow, h1, h2, h3, ite_true, ite_false, movkValue,
        RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]

end VG.Proof.Sha3.AArch64.Sha3.Vector
