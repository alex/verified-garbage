import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame

/-! # H′: selecting the first digest length -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_cmpi wp_mov32i)

theorem chooseLength_ok (s : State) :
    WP isa chooseLength s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (min (s.gpr .r15).toNat 64) ∧ Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mov fun a ha _ _ => wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  have n : a.gpr .rsi = s.gpr .r15 := ha.gpr
  have ku : Keeps s u := by
    refine ⟨fun r hr => ?_, ru.trans ha.rd, wu.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [gu]; exact ha.other r hn
    · rw [mu, ha.mem]; exact Frame.refl _ _
  have flag : isa.eval .b u = some (decide ((s.gpr .r15).toNat < 65)) := by
    simp only [eval, cf, n]
    rfl
  refine WP.ite (decide ((s.gpr .r15).toNat < 65)) flag ?_ ?_
  · intro h
    have hn : (s.gpr .r15).toNat ≤ 64 := by
      have h' := of_decide_eq_true h
      omega
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [gu, n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .r15).toNat := by
      have h' := of_decide_eq_false h
      omega
    refine wp_mov32i fun t ht _ _ => WP.block_nil ?_
    refine ⟨?_, ku.trans ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩⟩
    · rw [Nat.min_eq_right hn]; exact ht.gpr
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ht.other r hn
    · rw [ht.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.X86_64.HPrime
