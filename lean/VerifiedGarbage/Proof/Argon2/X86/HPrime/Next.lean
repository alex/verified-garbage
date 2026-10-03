import VerifiedGarbage.Proof.Argon2.X86.HPrime.Hash

/-!
# Argon2 H′ on x86 (32-bit): the hash of the digest

`next_ok`: `next` replaces the 64-byte digest at `scratch + 768` with the
BLAKE2b hash of it, of the length in `edx`.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed next)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi)

theorem next_ok {B E : BitVec 32} {s : State} (c : Ctx B E s) {n : Nat}
    (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa next s fun t =>
      bytesAt t.mem (B.setWidth 64 + 768) 64 =
        finalHash b (Spec.Blake2.init b n 0) (bytesAt s.mem (B.setWidth 64 + 768) 64) ∧
      Keeps B E s t := by
  unfold next
  refine WP.seq ((init_ok c hn hn₁ hn₂).mono fun s₁ ⟨r₁, cs₁, rd₁, wr₁, f₁⟩ => ?_)
  have k₁ : Keeps B E s s₁ := Keeps.of_call (of_callee cs₁) rd₁ wr₁ f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩
  have dg : bytesAt s₁.mem (B.setWidth 64 + 768) 64 = bytesAt s.mem (B.setWidth 64 + 768) 64 := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f₁.bytes (R := ⟨B.setWidth 64 + 768, 64⟩) ?_ (by simp) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact (c.stk_sub (d := 768) (n := 64) (by decide) (by decide)).symm
  refine WP.seq ((absorbFixed_ok (k₁.ctx c) (offset := 768) (size := 64) (by have := c.fits; omega) (by decide) (by decide)
    ((k₁.ctx c).cov (by decide)) (c.stk_sub (by decide) (by decide)) r₁).mono
    fun s₂ ⟨r₂, k₂⟩ => ?_)
  rw [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, dg] at r₂
  have c₂ := (k₁.trans k₂).ctx c
  refine WP.seq (wp_movi fun s₃ u₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_)
  have c₄ : Ctx B E s₄ := c₂.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]) (by rw [u₄.wr, u₃.wr])
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine (finalize_ok c₄ (d := bytesAt s.mem (B.setWidth 64 + 768) 64) (by rw [m₄]; exact r₂)
    (by
      have len : (bytesAt s.mem (B.setWidth 64 + 768) 64).length = 64 := by simp [bytesAt]
      rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, len]; rfl) (by simp [bytesAt])).mono ?_
  rintro t ⟨d, cs, rd, wr, f⟩
  refine ⟨d, (k₁.trans k₂).trans ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cs _ (by decide) (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
  · rw [cs _ (by decide) (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
  · rw [cs _ (by decide) (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
  · rw [rd, u₄.rd, u₃.rd]
  · rw [wr, u₄.wr, u₃.wr]
  · rw [← m₄]; exact f

end VG.Proof.Argon2.X86.HPrime
