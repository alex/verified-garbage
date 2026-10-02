import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# DES S-box machine-code correctness

Untrusted. The kernel checks each allocated scalar circuit on all 64
inputs, then the sound truth-table evaluator lifts that check to every
bit position of arbitrary 64-bit words. This verifies both the circuits
and the allocator's output, including spills.
-/

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])

def sboxCfg : Cfg := { base := .rdx, slots := 64, ext := .rdx, exts := 0 }
def inputTable (k : Nat) : Nat := tableOf (fun c => c.testBit k) 64
def outputTable (i j : Nat) : Nat :=
  tableOf (fun c => (Spec.TripleDes.sBox i (BitVec.ofNat 6 c)).getLsbD j) 64

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => q k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => e.reg (q j) == some (outputTable i j)

theorem sbox_check : ∀ i < 8,
    check (table 64 64) sboxCfg (fun _ => none) (instrs (sboxLiteral i))
      sboxEnv (sboxPost i) = true := by
  decide +kernel

def sboxWrites : List Reg := [.rax, .rcx, .r8, .r9, .r10, .r11, .rbx, .rbp, .r14, .r15]

theorem sbox_preserves : ∀ i < 8,
    [Reg.rdi, .rsi, .rdx, .rsp, .r12, .r13].all
      (fun r => (instrs (sboxLiteral i)).all fun op => op.dst != some r) = true := by
  decide +kernel

def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.gpr (q j)).getLsbD p

theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k = (s.gpr (q k)).getLsbD p := by
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

/-- Every S-box output bit, for arbitrary input words and any readable/
writable scratch state. Only the fixed scratch region can change. -/
theorem sbox_ok (i : Nat) (hi : i < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 64, (s'.gpr (q j)).getLsbD p =
        (Spec.TripleDes.sBox i (inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral i) = sboxCode i := by rw [sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.reg (q j) = some (outputTable i j) := by
    intro j hj
    have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      Post (TableRel p (inputAt s p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode i).all fun op => op.dst != some r) = false) := by
    intro p hp
    have hc := (inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel, outputTable, testBit_tableOf, (inputAt s p).isLt,
      decide_true, Bool.true_and] at h
    rw [BitVec.ofNat_toNat] at h
    exact h.symm
  · apply p₀.other r
    have hrest : r ∈ [Reg.rdi, .rsi, .rdx, .rsp, .r12, .r13] := by
      revert hr; cases r <;> decide
    have h := List.all_eq_true.mp (sbox_preserves i hi) r hrest
    rw [codeEq] at h
    simp [h]

end VG.Proof.TripleDes.X86_64
