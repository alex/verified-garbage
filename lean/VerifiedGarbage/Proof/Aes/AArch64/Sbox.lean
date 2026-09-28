import VerifiedGarbage.Impl.Aes.AArch64.Sbox
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.AArch64.Straight

/-!
# The bitsliced S-box on AArch64

Untrusted: everything here is checked by Lean.

`sboxCode` only combines words bitwise (and builds all ones with `movz` and
`sub`), so it computes the same Boolean function at each of the 64 bit
positions: the kernel evaluates it once on truth tables of the 256 inputs
(`Bitslice.table`) and compares the result with the specification's S-box
on the same tables (`sboxT`, proved right in `Proof/Aes/SboxSpec.lean`).
`sbox_ok` then gives, at every bit position `p`, the S-box of the byte
formed by bit `p` of the eight words.
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (sbox)

/-- The S-box's memory: its spill slots, at `x5`. -/
def sboxCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map inT

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some ((sboxT inTs).getD j 0)

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) sboxCode sboxEnv sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The registers the layers of AES may write: the state, the S-box's
temporaries and all ones, and the linear layers' masks and temporaries. -/
def layerWrites : List Reg :=
  [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
   .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29]

/-- The registers outside `layerWrites`. -/
def layerKeep : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x30]

theorem not_layerWrites (r : Reg) (hr : r ∉ layerWrites) : r ∈ layerKeep := by
  revert hr; cases r <;> decide

/-- A block that writes none of `layerKeep` writes only `layerWrites`. -/
theorem writes_rest {is : List Instr}
    (h : layerKeep.all (fun r => is.all fun i => dstOf i != some r) = true)
    (r : Reg) (hr : r ∉ layerWrites) : (is.all fun i => dstOf i != some r) = true :=
  List.all_eq_true.mp h r (not_layerWrites r hr)

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (sbox (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  have hout : ∀ j < 8, e'.reg (q j) = some ((sboxT inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 64, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (fun k => s.gpr (q k)) p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => dstOf i != some r) = false) := by
    intro p hp
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_, (fun _ _ _ h => by cases h),
      (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    have hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    simp only [TableRel, inT, testBit_tableOf, hc, decide_true, Bool.true_and,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (fun k => s.gpr (q k)) p).isLt
    have := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel] at this
    rw [← this, ← getLsbD_row _ _ hj, row_sboxT (by simp [inTs]) hc, row_inTs hc]
    simp
  · simp [writes_rest (is := sboxCode) (by decide +kernel) r hr]

end VG.Proof.Aes.AArch64
