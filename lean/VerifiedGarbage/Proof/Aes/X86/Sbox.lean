import VerifiedGarbage.Impl.Aes.X86.Sbox
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Aes.Ct32.Bitsliced
import VerifiedGarbage.Proof.Framework.X86.Straight

/-!
# The bitsliced S-box on x86 (32-bit)

`sboxCode` only combines words bitwise, so it computes the same Boolean
function at each of the 32 bit positions: the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's S-box on the same tables (`sboxT`, proved right in
`Proof/Aes/SboxSpec.lean`). `sbox_ok` then gives, at every bit position
`p`, the S-box of the byte formed by bit `p` of the eight words in slots
`0 … 7`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (sbox)

/-- The memory of the layers: the state and the S-box's spill slots, 256
bytes at `edi`. -/
def linCfg : Cfg := { base := sb, slots := 64, ext := sb, exts := 0 }

/-- The words of the state: slots `0 … 7`. -/
abbrev Q (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) j) 32

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map inT

def sboxEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if k < 8 then some (inT k) else none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((sboxT inTs).getD j 0)

theorem sbox_check :
    check (table 32 256) linCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The registers the layers may write are `tmpRegs`. -/
theorem not_tmp (r : Reg) (hr : r ∉ tmpRegs) : r ∈ [Reg.esp, .esi, .edi] := by
  revert hr; cases r <;> decide

theorem keeps_rest {is : List Instr}
    (h : [Reg.esp, .esi, .edi].all (fun r => is.all fun i => i.dst != some r) = true)
    (r : Reg) (hr : r ∉ tmpRegs) : (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mp h r (not_tmp r hr)

/-- The S-box, at every bit position of the words in slots `0 … 7`. -/
theorem sbox_ok {s : State} (hok : Ok linCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (sbox (bsByte (Q s) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion linCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.slot j = some ((sboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 32, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (Q s) p).toNat) linCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (Q s) p).isLt
    refine run (table_sound hp hc) hok ⟨(fun r a h => by cases h), fun k a _ h => ?_,
      (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv] at h
    split at h
    · rename_i hk8
      cases h
      simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
        BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, Q, linCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (Q s) p).isLt
    have := p₁.rel.slot j _ (by simp [linCfg]; omega) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, linCfg, hb] at this
    rw [Q, hb, ← this, ← getLsbD_row _ _ hj,
      row_sboxT (by simp [inTs]) hc, row_inTs hc]
    simp
  · have : (sboxCode.all fun i => i.dst != some r) = true :=
      keeps_rest (by decide +kernel) r hr
    simp [this]

end VG.Proof.Aes.X86
