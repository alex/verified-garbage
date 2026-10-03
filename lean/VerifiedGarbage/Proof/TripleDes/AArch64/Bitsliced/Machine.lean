import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Bitslice.Vars
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The AdvSIMD machine state of a batch

The 64 state words are the 16-byte slots at `x4` (`words`), in a writable
region (`Room`). Code that only moves and XORs whole words (the S-box
outputs, the exchange of the halves) is checked on the variable domain,
doubleword lane by doubleword lane (`varsRun`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.AArch64.BitsliceNeon

/-- The state words. -/
def stateCfg : Cfg := { base := .x4, slots := 64 }

/-- State word `j`. -/
def words (s : State) (j : Nat) : BitVec 128 := s.mem.readW (vAddr (s.gpr .x4) j) 128

/-- Doubleword lane `q` of the state words. -/
def laneW (s : State) (q : Nat) : Nat → BitVec 64 := fun j => vdword (words s j) q

/-- The state words' area. -/
def stateR (s : State) : Region := ⟨s.gpr .x4, 1024⟩

/-- What a batch's code needs of the machine: the state words writable. -/
abbrev Room (s : State) : Prop := Ok stateCfg s

theorem room_congr {s s' : State} (h : Room s) (hb : s'.gpr .x4 = s.gpr .x4) (hw : s'.wr = s.wr) :
    Room s' := h.congr hb hw

theorem runBlock_cat (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_cat, h₁, Option.bind_some, h₂]

theorem eq_of_vdword {x y : BitVec 128} (h : ∀ q < 2, vdword x q = vdword y q) : x = y :=
  vec64_ext (h 0 (by decide)) (h 1 (by decide))

/-! ## Words as XORs of variables -/

/-- Slot `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List VReg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables, in doubleword lane `q`. -/
def varVals (s : State) (regs : List VReg) (q v : Nat) : BitVec 64 :=
  if v < 64 then laneW s q v else vdword (s.v (regs.getD (v - 64) .v0)) q

def varN (regs : List VReg) : Nat := 64 + regs.length

theorem varEnv_rel {s : State} (regs : List VReg) :
    Rel (fun q => VarRel (varVals s regs q) (varN regs)) stateCfg (varEnv regs) s where
  reg r a h q hq := by
    simp only [varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [varVals, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h q hq := by
    have hk' : k < 64 := hk
    simp only [varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [varVals, hk', ite_true, laneW, words, stateCfg]
  gc _ _ h := by cases h

/-- Run a block that the variable domain accepts on the state words. -/
theorem varsRun {is : List Instr} (regs : List VReg) {post : Env Nat → Bool}
    (hchk : check (vars 64) stateCfg is (varEnv regs) post = true) {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (fun q => VarRel (varVals s regs q) (varN regs)) stateCfg e' s s'
        (fun r => (is.all fun i => vdstOf i != some r) = false)
        (fun r => (is.all fun i => dstOf i != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  obtain ⟨s', hs', p⟩ := run (fun q _ => vars_sound _ _) h (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-- The all-zero or all-one word. -/
def maskX (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

theorem getLsbD_maskX (b : Bool) {P : Nat} (hP : P < 128) : (maskX b).getLsbD P = b := by
  cases b
  · simp [maskX]
  · simp only [maskX, ite_true, BitVec.getLsbD_allOnes, hP, decide_true]

end VG.Proof.TripleDes.AArch64.BitslicedNeon
