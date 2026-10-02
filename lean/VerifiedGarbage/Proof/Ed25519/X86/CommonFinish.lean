import VerifiedGarbage.Proof.Ed25519.X86.CommonOutput

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
  refine WP.mono (abiRestore_ok cv) fun t ⟨mt, st, bt, it, pt, dt⟩ => ?_
  have saved : ∀ j < 4, wd v.mem (arg s₀ scidx) (4 * j) = s₀.gpr (savedReg j) := by
    intro j hj
    rw [wd_frame hv.frame fun r hr => ?_]
    exact hu.saved j hj
    rw [List.mem_singleton.mp hr]
    refine hsep.sub_left ?_
    rw [scR_eq]
    exact sub_sub hp.fit (Nat.zero_le _) (by omega_using [hj]) (by omega_using [hj])
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [bt]; exact saved 0 (by decide)
    · rw [it]; exact saved 1 (by decide)
    · rw [dt]; exact saved 2 (by decide)
    · rw [pt]; exact saved 3 (by decide)
    · exact st.trans (hv.keep.esp.trans hu.esp)
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
