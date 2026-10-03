import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.Framework.Block

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word)
abbrev Rows := Vector Word 24

theorem vreg_inj (a b : Fin 24) : vreg a = vreg b ↔ a = b :=
  (show ∀ a b : Fin 24, vreg a = vreg b ↔ a = b by decide) a b

theorem vreg_ne (a : Fin 24) : vreg a ≠ .v31 :=
  (show ∀ a : Fin 24, vreg a ≠ .v31 by decide) a

theorem vreg_ne30 (a : Fin 24) : vreg a ≠ .v30 :=
  (show ∀ a : Fin 24, vreg a ≠ .v30 by decide) a

def Holds (vs : Nat → Rows) (s : State) : Prop :=
  ∀ k : Fin 24, ∀ j, j < 4 → vword (s.v (vreg k)) j = (vs j)[k]

structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Same.trans {s₀ s₁ s₂ : State} (h : Same s₀ s₁) (h' : Same s₁ s₂) : Same s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

structure RoundSame (s s' : State) : Prop extends Same s s' where
  v30 : s'.v .v30 = s.v .v30

theorem RoundSame.trans {s₀ s₁ s₂ : State} (h : RoundSame s₀ s₁) (h' : RoundSame s₁ s₂) :
    RoundSame s₀ s₂ := ⟨h.toSame.trans h'.toSame, h'.v30.trans h.v30⟩

def step (vs : Nat → Rows) : Op → Nat → Rows
  | .add d a b => fun j => (vs j).set d ((vs j)[a] + (vs j)[b])
  | .xorRol d a b n => fun j => (vs j).set d (((vs j)[a] ^^^ (vs j)[b]).rotateLeft n)
  | .permute d n => fun j => (vs j).set d ((vs ((j + n.val) % 4))[d])

theorem get_set (v : Rows) (d k : Fin 24) (x : Word) :
    (v.set d x)[k] = if k = d then x else v[k] := by
  simp only [Vector.getElem_set, Fin.getElem_fin, Fin.ext_iff, eq_comm]

theorem op_ok (op : Op) {vs : Nat → Rows} {s : State} (h : Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block op.code) s fun s' => Holds (step vs op) s' ∧ RoundSame s s' := by
  cases op with
  | add d a b =>
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, step, get_set, vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, h a j hj, h b j hj]
    · exact h k j hj
  | xorRol d a b n =>
    by_cases h16 : n.val = 16
    · apply WP.of_runBlock
      simp only [Op.code, h16, ite_true, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
      simp only [RegUpd.v_setV, vreg_ne, ite_false, step, get_set, vreg_inj]
      split
      · rw [VG.Proof.ChaCha20.AArch64.Neon4.vword_rev32h_rol16 _ hj, VG.Proof.ChaCha20.AArch64.Neon.vword_xor, h a j hj, h b j hj, h16]
      · exact h k j hj
    by_cases h8 : n.val = 8
    · apply WP.of_runBlock
      simp (config := {decide := true}) only [Op.code, h8, ite_true, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
        by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
      simp only [RegUpd.v_setV, vreg_ne, ite_false, step, get_set, vreg_inj]
      split
      · rw [ht, VG.Proof.ChaCha20.AArch64.Neon4.vword_tbl_rol8 _ hj, VG.Proof.ChaCha20.AArch64.Neon.vword_xor, h a j hj, h b j hj, h8]
      · exact h k j hj
    have hn : n.val < 32 := n.isLt
    have hsh : VShiftOp.ushr.ok VArr.s4.esize (32 - n.val) = true := by
      simp only [VShiftOp.ok, VArr.esize, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hsl : VShiftOp.sli.ok VArr.s4.esize n.val = true := by
      simp only [VShiftOp.ok, VArr.esize, decide_eq_true_eq]; exact hn
    apply WP.of_runBlock
    simp only [Op.code, h16, h8, ite_false, List.cons_append, List.nil_append,
      runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      hsh, hsl, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
      RegUpd.v_setV, vreg_ne, Ne.symm (vreg_ne d), ite_false]
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, vreg_ne, ite_false, step, get_set, vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, vword_map2 _ _ _ hj]
      simp only [VShiftOp.eval, VG.Proof.ChaCha20.AArch64.Neon.shr_mask _ n hn, VG.Proof.ChaCha20.AArch64.Neon.vword_xor,
        h a j hj, h b j hj, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn, BitVec.or_comm]
    · exact h k j hj

  | permute d n =>
    have hn : 4 * n.val < 16 := by omega
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      hn, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun k j hj => ?_, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩, by
      simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, step, get_set, vreg_inj]
    split
    · rw [VG.Proof.ChaCha20.AArch64.Neon.vword_ext _ n.val j n.isLt hj,
        h d ((j + n.val) % 4) (Nat.mod_lt _ (by decide))]
    · exact h k j hj

theorem ops_ok : ∀ (ops : List Op) {vs : Nat → Rows} {s : State}, Holds vs s →
    s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table →
    WP isa (.block (ops.flatMap Op.code)) s fun s' =>
      Holds (ops.foldl step vs) s' ∧ RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((op_ok op h ht).mono fun _ ⟨h', hs⟩ =>
      (ops_ok ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

theorem ror_sub (x : BitVec 32) {n : Nat} (h0 : 0 < n) (hn : n < 32) :
    x.rotateRight (32 - n) = x.rotateLeft n := by
  rw [BitVec.rotateRight_def, BitVec.rotateLeft_def, Nat.mod_eq_of_lt (show 32 - n < 32 by omega),
    Nat.mod_eq_of_lt hn, show 32 - (32 - n) = n by omega, BitVec.or_comm]

/-- `op_ok` for the code with SVE2: an XAR in place of an `xorRol` whose
destination is its first source. -/
theorem op_ok_for (sve : Bool) (op : Op) {vs : Nat → Rows} {s : State} (h : Holds vs s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block (op.codeFor sve)) s fun s' => Holds (step vs op) s' ∧ RoundSame s s' := by
  cases sve with
  | false => exact op_ok op h ht
  | true =>
    cases op with
    | add d a b =>
      rw [show Op.codeFor true (.add d a b) = (Op.add d a b).code from rfl]; exact op_ok _ h ht
    | permute d n =>
      rw [show Op.codeFor true (.permute d n) = (Op.permute d n).code from rfl]; exact op_ok _ h ht
    | xorRol d a b n =>
      by_cases hda : d = a ∧ 0 < n.val
      · obtain ⟨rfl, h0⟩ := hda
        have hn : n.val < 32 := n.isLt
        have hr : 1 ≤ 32 - n.val ∧ 32 - n.val ≤ 32 := ⟨by omega, by omega⟩
        rw [show Op.codeFor true (.xorRol d d b n) = [.vop (.xarS (vreg d) (vreg b) (32 - n.val))]
          from ite_eq_left ⟨rfl, h0⟩]
        apply WP.of_runBlock
        simp only [runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some, hr, and_self,
          ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
        refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
          by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (vreg_ne30 d), ite_false]⟩⟩
        simp only [RegUpd.v_setV, step, get_set, vreg_inj]
        split
        · rw [vword_map2 _ _ _ hj, h d j hj, h b j hj, ror_sub _ h0 hn]
        · exact h k j hj
      · rw [show Op.codeFor true (.xorRol d a b n) = (Op.xorRol d a b n).code from ite_eq_right hda]
        exact op_ok _ h ht

theorem ops_ok_for (sve : Bool) : ∀ (ops : List Op) {vs : Nat → Rows} {s : State}, Holds vs s →
    s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table →
    WP isa (.block (ops.flatMap (Op.codeFor sve))) s fun s' =>
      Holds (ops.foldl step vs) s' ∧ RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((op_ok_for sve op h ht).mono fun _ ⟨h', hs⟩ =>
      (ops_ok_for sve ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

end VG.Proof.ChaCha20.AArch64.Rows6
