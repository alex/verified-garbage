import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Prepare

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

def chiWord (a b c rc : BitVec 64) (iota : Bool) : BitVec 64 :=
  let v := (b ^^^ 0xffffffffffffffff) &&& c ^^^ a
  if iota then v ^^^ rc else v

structure CoreOther (a b c : Slot) (ta tb tc dest : VReg) (iota : Bool) (q : Slot) : Prop where
  a : isGpr a = true → q ≠ .v ta
  b : isGpr b = true → q ≠ .v tb
  c : isGpr c = true → q ≠ .v tc
  dest : q ≠ .v dest
  rc : iota = true → q ≠ .v .v31

instance (a b c : Slot) (ta tb tc dest : VReg) (iota : Bool) (q : Slot) :
    Decidable (CoreOther a b c ta tb tc dest iota q) :=
  if h : (isGpr a = true → q ≠ .v ta) ∧ (isGpr b = true → q ≠ .v tb) ∧
      (isGpr c = true → q ≠ .v tc) ∧ q ≠ .v dest ∧ (iota = true → q ≠ .v .v31) then
    isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  else isFalse (fun h' => h ⟨h'.a, h'.b, h'.c, h'.dest, h'.rc⟩)

theorem chiCore_ok (s : VG.AArch64.State) (a b c : Slot) (ta tb tc dest : VReg)
    (iota : Bool) (hs : PrepSafe a b c ta tb tc) (hd : iota = true → dest ≠ .v31) :
    WP isa (.block (chiCore a b c ta tb tc dest iota)) s fun s' =>
      vdword (s'.v dest) 0 = chiWord (value s a) (value s b) (value s c) (s.gpr .x16) iota ∧
      Keep s s' ∧ s'.gpr = s.gpr ∧
      ∀ q, CoreOther a b c ta tb tc dest iota q → value s' q = value s q := by
  have hi := preps_inputs s a b c ta tb tc hs
  apply WP.of_runBlock
  cases iota
  all_goals
    simp (config := {decide := true}) only [chiCore, List.append_assoc, List.cons_append,
      List.nil_append, prepare_step, runBlock_cons, runBlock_nil, exec_vop, VOp.eval,
      Option.map_some, isa, runStep_some, Option.some.injEq, exists_eq_left',
      RegUpd.v_setV, RegUpd.gpr_setV, prepared_gpr, hd, ite_false, ite_true]
    refine ⟨?_, ?_, ?_, ?_⟩
  next => simp only [chi_low, hi.1, hi.2.1, hi.2.2, chiWord, Bool.false_eq_true, ite_false]
  next => constructor <;> simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, RegUpd.sp_setV, prepared_gpr, prepared_mem, prepared_rd, prepared_wr, prepared_sp]
  next => trivial
  next =>
    intro q hq
    simp only [value_setV, hq.dest, ite_false, prepared_value _ _ _ _ hq.c,
      prepared_value _ _ _ _ hq.b, prepared_value _ _ _ _ hq.a]
  next => simp only [chi_xor_low, hi.1, hi.2.1, hi.2.2, vdword_ofVDwords_0, chiWord, ite_true]
  next => constructor <;> simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, RegUpd.sp_setV, prepared_gpr, prepared_mem, prepared_rd, prepared_wr, prepared_sp]
  next => trivial
  next =>
    intro q hq
    simp only [value_setV, hq.dest, hq.rc rfl, ite_false, prepared_value _ _ _ _ hq.c,
      prepared_value _ _ _ _ hq.b, prepared_value _ _ _ _ hq.a]

end VG.Proof.Sha3.AArch64.Sha3.Hybrid
