import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.TripleDes.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Table

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]
noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])
def sboxCfg : Cfg := { base := .ebp, slots := 128, ext := .ebp, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun _ => none,
    slot := fun k => if 16 ≤ k ∧ k < 22 then some (inputTable (k - 16)) else none }
def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => e.slot (16 + j) == some (outputTable i j)
theorem sbox_check : ∀ i < 8,
    check (table 32 64) sboxCfg (fun _ => none) (instrs (sboxLiteral i))
      sboxEnv (sboxPost i) = true := by
  lit_decide

def sboxWrites : List Reg := [.eax, .ebx, .ecx, .edx]
theorem sbox_preserves : ∀ i < 8,
    [Reg.esp, .ebp, .esi, .edi].all
      (fun r => (instrs (sboxLiteral i)).all fun op => op.dst != some r) = true := by
  decide +kernel

def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p
theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k =
      (s.mem.readW (wordAddr (s.gpr .ebp) (16 + k)) 32).getLsbD p := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxLiteral_eq : ∀ i < 8, sboxLiteral i = .block (sboxCode i)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

/-- Every output bit, including allocated spills and memory operands. -/
theorem sbox_ok (i : Nat) (hi : i < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p =
        (Spec.TripleDes.sBox i (inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral i) = sboxCode i := by rw [sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.slot (16 + j) = some (outputTable i j) := by
    intro j hj
    exact beq_iff_eq.mp (List.all_eq_true.mp hpost j (List.mem_range.mpr hj))
  have key : ∀ p < 32, ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      Post (TableRel p (inputAt s p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode i).all fun op => op.dst != some r) = false) := by
    intro p hp
    have hc := (inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨(fun _ _ h => by cases h), ?_,
      (fun _ _ _ h => by cases h)⟩ he
    intro k a hk h
    simp only [sboxEnv] at h
    split at h
    · rename_i hb
      cases h
      have hk6 : k - 16 < 6 := by omega
      have heq : 16 + (k - 16) = k := by omega
      simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
        inputAt_bit s p (k - 16) hk6, heq, sboxCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.slot (16 + j) _ (by simp [sboxCfg]; omega) (hout j hj)
    have hb := p₁.base
    simp only [TableRel, outputTable, testBit_tableOf, (inputAt s p).isLt,
      decide_true, Bool.true_and, sboxCfg] at h hb
    rw [hb, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    exact h.symm
  · apply p₀.other r
    have hrest : r ∈ [Reg.esp, .ebp, .esi, .edi] := by
      revert hr; cases r <;> decide
    have h := List.all_eq_true.mp (sbox_preserves i hi) r hrest
    rw [codeEq] at h
    simp [h]
end VG.Proof.TripleDes.X86
