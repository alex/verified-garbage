import VerifiedGarbage.Proof.Aes.X86.AesNi.KeySteps
import VerifiedGarbage.Proof.Aes.X86.ExpandKeyCT
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Proof.Aes.X86 (EPre keyP keyLen keyR ekSchP ekSchR ekArgR)

/-- A vector load changes no GPR, memory, or access region. -/
theorem key_load_exec (s : State) (x : XReg) (a : MemOp)
    (h : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    exec (.movdquLoad x a) s = some (s.setXmm x (s.mem.readW (s.ea a) 128)) := by
  simp only [exec, State.load128, h, ite_true, Option.map_some]

/-- A schedule vector store extends the exact little-endian word prefix. -/
theorem key_good_store (s : State) (p : Addr) (f : Nat → BitVec 32) (K n : Nat)
    (hG : Good s.mem p f K) (v : BitVec 128) (hn : n ≤ 4)
    (hv : ∀ j < n, dword v j = f (K + j)) (hK : 4 * K + 16 ≤ 240) :
    Good (s.mem.writeW (p + BitVec.ofNat 64 (4 * K)) v) p f (K + n) :=
  good_store hG v hn hv hK

/-- Every key schedule store stays within its declared writable region. -/
theorem key_store_frame (m : Mem) (p : Addr) (d : Nat) (v : BitVec 128)
    (hd : d + 16 ≤ 240) :
    Frame [⟨p, 240⟩] m (m.writeW (p + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ _).writeW (v := v) (List.mem_singleton_self _)
    (Offset.contains_base p hd (by omega))

/-- Loading an initial key lane yields its four expansion words. -/
theorem key_initial_words (m : Mem) (p : Addr) (nk off : Nat)
    (h : off + 4 ≤ nk) :
    ∀ j < 4, dword (m.readW (p + BitVec.ofNat 64 (4 * off)) 128) j = W m p nk (off + j) := by
  intro j hj
  rw [dword_readW _ _ hj, W_lt (by omega),
    show 4 * (off + j) = 4 * off + 4 * j by omega, BitVec.ofNat_add, BitVec.add_assoc]

end VG.Proof.Aes.X86.AesNi
