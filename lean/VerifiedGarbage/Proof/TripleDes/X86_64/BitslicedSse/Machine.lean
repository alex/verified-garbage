import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Sbox
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Transpose
import VerifiedGarbage.Proof.Framework.Bitslice.Vars
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SSE2 machine state of a batch

The 64 state words are the 16-byte slots at `rsi` (`words`), in a writable
region apart from the scratch buffer at `rcx`, which holds the circuits'
spills (`Room`). Code that only moves and XORs whole words (the S-box
outputs, the exchange of the halves) is checked on the variable domain,
quadword lane by quadword lane (`varsRun`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.X86_64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.X86_64.BitsliceSse

/-- The scratch buffer. -/
def scratchR (s : State) : Region := ⟨s.gpr .rcx, 1024⟩

/-- The circuits' spill slots, at the start of the scratch buffer. -/
def spillR (s : State) : Region := ⟨s.gpr .rcx, 256⟩

theorem spill_sub (s : State) : Region.Sub (spillR s) (scratchR s) := Region.sub_prefix (by decide)

/-- What a batch's code needs of the machine: the scratch buffer writable,
the state words writable and apart from it. -/
structure Room (s : State) : Prop where
  scratch : scratchR s ∈ s.wr
  state : Ok stateCfg s
  sep : (stateR s).Disjoint (scratchR s)

theorem Room.congr {s s' : State} (h : Room s) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hsi : s'.gpr .rsi = s.gpr .rsi) (hw : s'.wr = s.wr) : Room s' where
  scratch := by simp only [scratchR, hc, hw]; exact h.scratch
  state := h.state.congr hsi hw
  sep := by simp only [stateR, scratchR, hc, hsi]; exact h.sep

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

/-! ## Quadwords -/

open VG.X86_64.StraightY (qword_xor qword_app)

theorem eq_of_qword {x y : BitVec 128} (h : ∀ q < 2, qword x q = qword y q) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun z => z.getLsbD (i % 64)) (h (i / 64) (by omega))
  simp only [getLsbD_qword _ (Nat.mod_lt i (by decide) : i % 64 < 64), Nat.div_add_mod] at e
  exact e

theorem qword_zero (q : Nat) : qword 0 q = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [qword]

/-! ## Words as XORs of variables -/

/-- Slot `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List XReg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables, in quadword lane `q`. -/
def varVals (s : State) (regs : List XReg) (q v : Nat) : BitVec 64 :=
  if v < 64 then laneW s q v else qword (s.xmm (regs.getD (v - 64) .xmm0)) q

def varN (regs : List XReg) : Nat := 64 + regs.length

theorem varEnv_rel {s : State} (regs : List XReg) :
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
  xc _ _ h := by cases h

/-- Run a block that the variable domain accepts on the state words. -/
theorem varsRun {is : List Instr} (regs : List XReg) {post : Env Nat → Bool}
    (hchk : check (vars 64) stateCfg is (varEnv regs) post = true) {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (fun q => VarRel (varVals s regs q) (varN regs)) stateCfg e' s s'
        (fun r => (is.all fun i => xdst i != some r) = false)
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  obtain ⟨s', hs', p⟩ := run (fun q _ => vars_sound _ _) h.state (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-! ## Instructions on whole registers -/

theorem xmm_pxor (s : State) (d a : XReg) :
    ((XOp.bin .pxor d a).exec s).xmm d = s.xmm d ^^^ s.xmm a := by
  simp [XOp.exec, State.setXmm, XBinOp.eval]

/-- The all-zero or all-one quadword. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- The all-zero or all-one word. -/
def maskX (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

theorem getLsbD_maskX (b : Bool) {P : Nat} (hP : P < 128) : (maskX b).getLsbD P = b := by
  cases b
  · simp [maskX]
  · simp only [maskX, ite_true, BitVec.getLsbD_allOnes, hP, decide_true]

/-- `movq x, r` then `punpcklqdq x, x` of a mask. -/
theorem bcast_mask (s : State) (x : XReg) (r : Reg) (b : Bool) (hr : s.gpr r = maskVal b) :
    ((XOp.bin .punpcklqdq x x).exec ((XOp.movq x r).exec s)).xmm x = maskX b := by
  apply eq_of_qword; intro q hq
  simp only [XOp.exec, State.setXmm, ite_true, XBinOp.eval, hr]
  rw [qword_app _ _ hq, qword_app _ _ (by decide)]
  simp only [ite_true]
  have e : qword (maskX b) q = maskVal b := by
    cases b
    · simp only [maskVal, maskX, Bool.false_eq_true, ite_false, qword_zero]
    · simp only [maskVal, maskX, ite_true]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [getLsbD_qword _ hi]
      simp only [BitVec.getLsbD_allOnes, hi, show 64 * q + i < 128 by omega, decide_true]
  rw [e]
  split <;> rfl

end VG.Proof.TripleDes.X86_64.BitslicedSse
