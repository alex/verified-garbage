import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Length

/-! # H′: a bounded public length comparison -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64
open VG.Proof.MdStream.AArch64 (wp_subImm wp_lsr)

structure Compared (s t : State) : Prop where
  value : t.gpr .x9 = if (s.gpr .x23).toNat < 65 then 1 else 0
  other : ∀ r, r ≠ .x9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem compare_ok (s : State) (hb : (s.gpr .x23).toNat < 2 ^ 32) :
    WP isa (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]) s (Compared s) := by
  refine wp_subImm (by decide) fun a ha => wp_lsr (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, fun r hr => (ht.other r hr).trans (ha.other r hr), ht.mem.trans ha.mem,
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  rw [ht.gpr, ha.gpr]
  exact below65 _ hb

theorem Compared.keeps {s t : State} (h : Compared s t) : Keeps s t := by
  refine ⟨fun r hr _ => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [h.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.AArch64.HPrime
