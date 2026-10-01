import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt bytesAt rates)
open VG.Proof.Sha3 (Rep)

abbrev rate (b : State) : Nat := (b.gpr .x6).toNat
abbrev st (b : State) : Addr := b.gpr .x0
abbrev data (b : State) : Addr := b.gpr .x3
abbrev len (b : State) : Nat := (b.gpr .x4).toNat
abbrev scratch (b : State) : Addr := b.gpr .x1
abbrev stateR (b : State) : Region := ⟨st b, 200⟩
abbrev dataR (b : State) : Region := ⟨data b, len b⟩
abbrev scratchR (b : State) : Region := ⟨scratch b, 640⟩

/-- The call-free resident prefix starts at an aligned sponge position with
at least one complete block. `x1` and `x5` both name its scratch buffer. -/
structure BulkPre (b : State) : Prop where
  rd : b.rd = [dataR b]
  wr : b.wr = [stateR b, scratchR b]
  st_scr : (stateR b).Disjoint (scratchR b)
  d_st : (dataR b).Disjoint (stateR b)
  d_scr : (dataR b).Disjoint (scratchR b)
  rate_mem : rate b ∈ rates
  enough : rate b ≤ len b
  len_upper : len b < 2^63 + rate b
  x2 : b.gpr .x2 = 0
  x5 : b.gpr .x5 = scratch b

/-- Complete blocks have been consumed, and the usual memory sponge
representation is restored before the generic streaming tail runs. -/
structure BulkResult (b : State) (consumed : Nat) (s : State) : Prop where
  c_le : consumed ≤ len b
  aligned : consumed % rate b = 0
  abi : abiPreserved b s
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  frame : Frame [stateR b, scratchR b] b.mem s.mem
  x0 : s.gpr .x0 = b.gpr .x0
  x1 : s.gpr .x1 = b.gpr .x1
  x2 : s.gpr .x2 = b.gpr .x2
  x3 : s.gpr .x3 = data b + BitVec.ofNat 64 consumed
  x4 : s.gpr .x4 = BitVec.ofNat 64 (len b - consumed)
  x5 : s.gpr .x5 = b.gpr .x5
  x6 : s.gpr .x6 = b.gpr .x6
  repr : ∀ msg, stateAt b.mem (st b) = Rep (rate b) msg →
    msg.length % rate b = 0 →
    stateAt s.mem (st b) = Rep (rate b) (msg ++ bytesAt b.mem (data b) consumed)

def BulkPost (b s : State) : Prop := ∃ consumed, BulkResult b consumed s

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
