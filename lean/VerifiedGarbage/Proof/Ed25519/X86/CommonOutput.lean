import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure OutputInv (x p : BitVec 32) (src : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  frame : Frame [sub p 0 (4 * n)] s₀.mem s.mem
  words : ∀ j < n, wd s.mem p (4 * j) = wd s₀.mem x (src + 4 * j)

theorem outputWords_ok {x p : BitVec 32} {s₀ : State} (hc : Ctx x s₀)
    (hp : s₀.gpr .esi = p) {src : Nat} (hd : src + 32 ≤ 8192)
    (hfit : p.toNat + 32 ≤ 2 ^ 32)
    (hi : ∀ j < 8, InRegions s₀.wr (addr p (4 * j)) 4)
    (hs : (scR x).Disjoint (sub p 0 32)) :
    ∀ n ≤ 8, WP isa (.block (outputWords src n)) s₀ (OutputInv x p src s₀ n)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    have he : outputWords src (n + 1) = outputWords src n ++
        ([.mov .eax (.mem (sc (src + 4 * n))), .store (at_ .esi (4 * n)) .eax] : List Instr) := by
      simp only [outputWords, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [he]
    refine WP.block_append (WP.mono (outputWords_ok hc hp hd hfit hi hs n (by omega_using [hn]))
      fun u hu => ?_)
    have cu := hu.keep.ctx hc
    refine Wp.wp_ldm cu.edi (cu.inRW (by omega_using [hd, hn]) (by decide)) fun v hv => ?_
    refine Wp.wp_stm ((updKeep hv).esi.trans (hu.keep.esi.trans hp))
      (by rw [hv.wr, hu.keep.wr]; exact hi n (by omega_using [hn])) fun t ht => WP.block_nil ?_
    have et : t.mem = u.mem.writeW (addr p (4 * n)) (wd s₀.mem x (src + 4 * n)) := by
      rw [ht.mem, hv.mem, hv.gpr]
      have hw : wd u.mem x (src + 4 * n) = wd s₀.mem x (src + 4 * n) :=
        wd_frame hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          refine (hs.sub_left ?_).sub_right ?_
          · rw [scR_eq]; exact sub_sub hc.fit (Nat.zero_le _) (by omega_using [hd, hn]) (by omega_using [hd, hn])
          · rw [sub, sub, addr_zero]
            exact Region.sub_prefix (by omega_using [hn])
      exact congrArg (u.mem.writeW (addr p (4 * n))) hw
    refine ⟨hu.keep.trans ((updKeep hv).trans
      ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩), ?_, fun j hj => ?_⟩
    · rw [et]
      have hf : Frame [sub p 0 (4 * (n + 1))] s₀.mem u.mem := hu.frame.sub fun r hr =>
        ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩
      exact hf.writeW (List.mem_singleton_self _) _
        (sub_contains (by omega_using [hfit, hn]) (Nat.zero_le _) (by omega_using []) (by decide))
    · rw [et]
      by_cases e : j = n
      · subst e; exact wd_write_self _ _ _ _
      · rw [wd_write_ne _ _ (by omega_using [hfit, hn, hj]) (by omega_using [hfit, hn])
          (by omega_using [hj, e])]
        exact hu.words j (by omega_using [hj, e])

end VG.Proof.Ed25519.X86
