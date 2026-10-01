import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # Byte-wise block output on 32-bit targets -/

namespace VG.Proof.Rc2.Word32

open VG VG.WriteBytes

def outputBytes (v : Spec.Rc2.State) (n : Nat) : List Byte :=
  (List.range (2 * n)).map fun i => (Spec.Rc2.encodeBlock v).getD i 0

theorem outputBytes_length (v : Spec.Rc2.State) (n : Nat) : (outputBytes v n).length = 2 * n := by
  simp [outputBytes]

theorem encode_lo (v : Spec.Rc2.State) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.encodeBlock v).getD (2 * i) 0 = (v.getD i 0).setWidth 8 := by
  rw [Spec.Rc2.encodeBlock, getD_ofFn _ _ (by omega)]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right,
    Nat.mul_zero, BitVec.ushiftRight_zero]

theorem encode_hi (v : Spec.Rc2.State) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.encodeBlock v).getD (2 * i + 1) 0 = ((v.getD i 0) >>> 8).setWidth 8 := by
  rw [Spec.Rc2.encodeBlock, getD_ofFn _ _ (by omega)]
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  simp only [hd, hm, Nat.mul_one]

theorem outputBytes_succ (v : Spec.Rc2.State) (n : Nat) (hn : n < 4) :
    outputBytes v (n + 1) = outputBytes v n ++
      [(v.getD n 0).setWidth 8, ((v.getD n 0) >>> 8).setWidth 8] := by
  rw [outputBytes, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    List.range_succ, List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, encode_lo v n hn,
    encode_hi v n hn, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem outputBytes_write (m : Mem) (p : Addr) (v : Spec.Rc2.State) (n : Nat) (hn : n < 4) :
    writeBytes m p (outputBytes v (n + 1)) =
      ((writeBytes m p (outputBytes v n)).writeW (p + BitVec.ofNat 64 (2 * n))
        ((v.getD n 0).setWidth 8)).writeW (p + BitVec.ofNat 64 (2 * n + 1))
          (((v.getD n 0) >>> 8).setWidth 8) := by
  rw [outputBytes_succ v n hn]
  rw [show outputBytes v n ++ [(v.getD n 0).setWidth 8, ((v.getD n 0) >>> 8).setWidth 8] =
    (outputBytes v n ++ [(v.getD n 0).setWidth 8]) ++ [((v.getD n 0) >>> 8).setWidth 8] by simp]
  rw [writeBytes_snoc _ _ _ _ (by simp only [List.length_append, List.length_singleton, outputBytes_length]; omega),
    writeBytes_snoc _ _ _ _ (by rw [outputBytes_length]; omega)]
  simp only [List.length_append, List.length_singleton, outputBytes_length]

theorem outputBytes_pack (m : Mem) (p : Addr) (v : Spec.Rc2.State) :
    writeBytes m p (outputBytes v 4) = m.writeW p (pack v) := by
  change _ = m.write p 8 (pack v)
  rw [write_eq_writeBytes]
  apply congrArg (writeBytes m p)
  apply List.map_congr_left
  intro i hi
  exact encode_pack v i (List.mem_range.mp hi)

end VG.Proof.Rc2.Word32
