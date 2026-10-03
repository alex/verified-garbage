import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec

/-! Merged from `Proof.Ed25519.X86.CommonOutput`. -/
section
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
    (hs : (scR 8192 x).Disjoint (sub p 0 32)) :
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
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure OutputPre (s₀ : State) (scidx : Nat) : Prop where
  wr : (⟨(arg s₀ 0).setWidth 64, 32⟩ : Region) ∈ s₀.wr
  fit : (arg s₀ 0).toNat + 32 ≤ 2 ^ 32
  sep : (⟨(arg s₀ 0).setWidth 64, 32⟩ : Region).Disjoint (scR 8192 (arg s₀ scidx))
  ret : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s₀ 0).setWidth 64, 32⟩

theorem finishWords_ok {s₀ s : State} {scidx argc src : Nat}
    (hp : ScratchPre s₀ scidx argc) (ho : OutputPre s₀ scidx)
    (h : Saved s₀ (arg s₀ scidx) s) (hsrc : src + 32 ≤ 8192) :
    WP isa (.block (finishWords src)) s fun t => abiPreserved s₀ t ∧
      Spec.Ed25519.bytesAt t.mem ((arg s₀ 0).setWidth 64) 32 =
        Spec.Ed25519.encodeLE 32 (fe s.mem (arg s₀ scidx) src) := by
  simp only [finishWords, List.append_assoc]
  refine WP.block_append (WP.mono (loadArg_ok (i := 0) hp h (by have := hp.index; omega_using [this]))
    fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hwr : ∀ j < 8, InRegions u.wr (addr (arg s₀ 0) (4 * j)) 4 := by
    intro j hj
    refine ⟨_, hu.wr ▸ ho.wr, ?_⟩
    have hc := sub_contains (x := arg s₀ 0) (a := 0) (k := 32) (d := 4 * j) (n := 4)
      (by have := ho.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hj]) (by decide)
    rwa [sub, addr_zero] at hc
  have hsep : (scR 8192 (arg s₀ scidx)).Disjoint (sub (arg s₀ 0) 0 32) := by
    rw [sub, addr_zero]; exact ho.sep.symm
  refine WP.block_append (WP.mono (outputWords_ok cu eu hsrc ho.fit hwr hsep 8 (by decide)) fun v hv => ?_)
  have cv := hv.keep.ctx cu
  have saved : Spill.Saved v.mem (addr (arg s₀ scidx)) s₀.gpr savedSlots := hu.saved.of_readW fun p hp' => by
    have := savedSlots_bound p hp'
    refine wd_frame hv.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine hsep.sub_left ?_
    rw [scR_eq]
    exact sub_sub hp.fit (Nat.zero_le _) (by omega_using [this]) (by omega_using [this])
  refine WP.mono (abiRestore_ok cv saved) fun t ⟨gt, st, _, mt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases h : r = .esp
    · subst h; exact st.trans (hv.keep.esp.trans hu.esp)
    · exact gt r hr h
  · rw [mt]
    have hvret : v.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = u.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
      hv.frame.readW (Region.contains_self _ _) (by
        simp only [List.mem_singleton]; rintro r rfl
        rw [sub, addr_zero]; exact ho.ret) (by decide)
    rw [hvret]
    exact hu.frame.readW (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_sc) (by decide)
  · rw [mt, encodeLE_eq]
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    have eaddr := addr_eq (x := arg s₀ 0) (k := 4 * j) (by have := ho.fit; omega_using [this, hj])
    rw [← eaddr]
    change (wd v.mem (arg s₀ 0) (4 * j)).toNat = _
    rw [hv.words j hj, mu, Nat.pow_mul]
    exact (num_digit j (f := fun k => wv s.mem (arg s₀ scidx) (src + 4 * k))
      (fun _ _ => wv_lt _ _ _) hj).symm
end VG.Proof.Ed25519.X86
