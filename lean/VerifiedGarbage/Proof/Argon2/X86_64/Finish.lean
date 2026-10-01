import VerifiedGarbage.Proof.Argon2.X86_64.Initialize

/-! # XOR the permuted block with R and write the output -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

/-- A prefix of the output block has been written. -/
def Written (m : Mem) (out : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n → m.readW (off out (8 * i.val)) 64 = r[i]

theorem written_step {m : Mem} {out : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Written m out r n) :
    Written (m.writeW (off out (8 * n)) r[n]) out r (n + 1) := by
  intro i hi
  by_cases he : i.val = n
  · subst n
    exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep out (by omega) (by omega) (by omega)) (by decide)]
    exact h i (by omega)

theorem scratch_unchanged {m m' : Mem} {out p : Addr} (hf : Frame [⟨out, 1024⟩] m m')
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) {d : Nat} (hd' : d + 8 ≤ 4096) :
    m'.readW (off p d) 64 = m.readW (off p d) 64 :=
  hf.readW (r := ⟨p, 4096⟩) (Offset.contains_base p hd' (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- Finish an arbitrary prefix while preserving the complete scratch allocation. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 128) (s : State) {p out : Addr}
    (hs : Scratch s p) (ho : s.gpr .rdi = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range n).flatMap Impl.Argon2.X86_64.finishWord)) s fun t =>
      Written t.mem out (xorBlock (working s.mem p) (blockAt s.mem p)) n ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega
    have ho' : t.gpr .rdi = out := (hk.1 .rdi (by decide)).trans ho
    have hout : InRegions t.wr (off (t.gpr .rdi) (8 * n)) 8 := by
      rw [ho', hk.2.2]
      exact ⟨_, hw, Offset.contains_base out (by omega) (by omega)⟩
    refine (finishWord_ok t (hs.of_copy hk) ⟨n, hn'⟩ hout).mono ?_
    rintro u ⟨hm, hreg, hr, hw'⟩
    have hv : word t.mem p n ^^^ t.mem.readW (off p (8 * n)) 64 =
        (xorBlock (working s.mem p) (blockAt s.mem p))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [xorBlock_get, working_get, blockAt_get]
      simp only [word, scratch_unchanged hf hd (d := 1024 + 8 * n) (by omega),
        scratch_unchanged hf hd (d := 8 * n) (by omega)]
    refine ⟨?_, ?_, hk.trans ⟨hreg, hr, hw'⟩⟩
    · rw [hm, ho', hv]
      exact written_step hn' ht
    · rw [hm, ho']
      exact hf.writeW (r := ⟨out, 1024⟩) (by simp) _
        (Offset.contains_base out (by omega) (by omega))

theorem written_block {m : Mem} {out : Addr} {r : Block} (h : Written m out r 128) :
    blockAt m out = r := by
  apply Vector.ext
  intro i hi
  have he := h ⟨i, hi⟩ hi
  rw [← blockAt_get m out ⟨i, hi⟩] at he
  exact he

end VG.Proof.Argon2.X86_64
