import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Sbox
import VerifiedGarbage.Proof.Framework.X86_64.StraightX

/-!
# The SSE2 S-box circuits' machine code

Untrusted. The kernel checks each allocated circuit on all 64 inputs once,
and the quadword-lane evaluator (`StraightX`) with the truth-table domain
lifts that check to every bit position of every quadword of arbitrary
128-bit words. The circuits spill to the scratch buffer (`[rcx + 16k]`,
`k < spills`), read all ones from `ones`, and write no general-purpose
register.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64 VG.X86_64.StraightX VG.Bitslice VG.Impl.TripleDes.X86_64.BitsliceSse
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

def sboxCfg : Cfg := { base := .rcx, slots := spills }

def sboxEnv : Env Nat :=
  { reg := fun r => if r = ones then some (2 ^ 64 - 1)
      else ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    check (table 64 64) sboxCfg (instrs (sboxLiteral j)) sboxEnv (sboxPost j) = true := by
  decide +kernel

theorem sboxLiteral_eq : ∀ j < 8, sboxLiteral j = .block (sboxCode j)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

theorem sbox_preserves : ∀ j < 8,
    (instrs (sboxLiteral j)).all (fun op => xdst op != some ones && op.dst == none) = true := by
  decide +kernel

/-- Bit `P` of each input register, as the S-box's input. -/
def inputAt (s : State) (P : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.xmm (inReg i)).getLsbD P

theorem inputAt_bit (s : State) (P k : Nat) (hk : k < 6) :
    (inputAt s P).toNat.testBit k = (s.xmm (inReg k)).getLsbD P := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem inReg_ne_ones : ∀ k < 6, inReg k ≠ ones := by decide

/-- Every S-box output bit, for arbitrary input words and spill slots, with
all ones in `ones`. Only the spill slots change in memory, and no
general-purpose register or flag changes. -/
theorem sbox_ok (j : Nat) (hj : j < 8) {s : State} (hok : Ok sboxCfg s)
    (hones : s.xmm ones = BitVec.allOnes 128) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ P < 128, (s'.xmm (outReg i)).getLsbD P =
        (Spec.TripleDes.sBox j (inputAt s P)).getLsbD i) ∧
      s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm ones = s.xmm ones ∧ Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (fun q => TableRel p (inputAt s (64 * q + p)).toNat) sboxCfg e' s s'
        (fun r => ((sboxCode j).all fun op => xdst op != some r) = false)
        (fun r => ((sboxCode j).all fun op => op.dst != some r) = false) := by
    intro p hp
    refine run (fun q _ => table_sound hp (inputAt s (64 * q + p)).isLt) hok
      ⟨fun r a h q hq => ?_, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
        (fun _ _ h => by cases h)⟩ he
    have hc := (inputAt s (64 * q + p)).isLt
    simp only [sboxEnv] at h
    split at h
    · rename_i hr
      cases h; subst hr
      simp only [TableRel, getLsbD_qword _ hp, hones, BitVec.getLsbD_allOnes,
        Nat.testBit_two_pow_sub_one, hc, decide_true, show 64 * q + p < 128 by omega]
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      have hqr := List.find?_some hk
      have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
      simp only [beq_iff_eq] at hqr
      subst hqr
      simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
        inputAt_bit s _ k hk6, getLsbD_qword _ hp]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  have pres := sbox_preserves j hj
  rw [codeEq] at pres
  have pres' := List.all_eq_true.mp pres
  refine ⟨s', hs', fun i hi P hP => ?_, funext fun r => p₀.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h
      have := pres' op hop
      simp [h] at this),
    p₀.cf, p₀.zf, p₀.rd, p₀.wr, p₀.other ones (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h
      have := pres' op hop
      simp [h] at this), p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key (P % 64) (Nat.mod_lt _ (by decide))
  obtain rfl := Straight.run_unique hs'' hs'
  have h := p₁.rel.reg (outReg i) _ (hout i hi) (P / 64) (by omega)
  have eP : 64 * (P / 64) + P % 64 = P := Nat.div_add_mod P 64
  simp only [TableRel, outputTable, testBit_tableOf, (inputAt s _).isLt,
    decide_true, Bool.true_and, eP, getLsbD_qword _ (Nat.mod_lt _ (by decide) : P % 64 < 64)] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.X86_64.BitslicedSse
