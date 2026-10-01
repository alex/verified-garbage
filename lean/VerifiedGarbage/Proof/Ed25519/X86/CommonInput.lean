import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure InputPre (s₀ : State) (scidx i n : Nat) : Prop where
  rd : (sub (arg s₀ i) 0 (4 * n)) ∈ s₀.rd ++ s₀.wr
  fit : (arg s₀ i).toNat + 4 * n ≤ 2 ^ 32
  sep : (sub (arg s₀ i) 0 (4 * n)).Disjoint (scR (arg s₀ scidx))

theorem inputWord_contains {s₀ : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    {k : Nat} (hk : k < n) : (sub (arg s₀ i) 0 (4 * n)).Contains (addr (arg s₀ i) (4 * k)) 4 :=
  sub_contains (by have := hp.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)

theorem inputWord_same {s₀ s : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) {k : Nat} (hk : k < n) :
    wd s.mem (arg s₀ i) (4 * k) = wd s₀.mem (arg s₀ i) (4 * k) :=
  hs.frame.readW (inputWord_contains hp hk)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.sep) (by decide)

theorem loadInput_ok {s₀ s : State} {scidx argc i n dst : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc)
    (hd0 : 16 ≤ dst) (hd : dst + 4 * n ≤ 8192) (hd' : dst < 8192) :
    WP isa (.block (([.mov .esi (.mem (at_ .esp (4 + 4 * i)))] : List Instr) ++ copyWords dst n)) s fun t =>
      Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < n, wd t.mem (arg s₀ scidx) (dst + 4 * k) = wd s₀.mem (arg s₀ i) (4 * k)) ∧
      Frame [sub (arg s₀ scidx) dst (4 * n)] s.mem t.mem := by
  refine WP.block_append (WP.mono (loadArg_ok hp hs hia) fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hread : ∀ k < n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i) (4 * k)) 4 := by
    intro k hk; refine ⟨_, ?_, inputWord_contains hi hk⟩
    rw [hu.rd, hu.wr]; exact hi.rd
  have hsep : ∀ k < n, (sub (arg s₀ i) (4 * k) 4).Disjoint (sub (arg s₀ scidx) dst (4 * n)) := by
    intro k hk
    refine (hi.sep.sub_left ?_).sub_right ?_
    · rw [sub, sub, addr_eq (by have := hi.fit; omega_using [this, hk]), addr_zero]
      exact Offset.sub_base _ (by omega_using [hk])
    · rw [scR_eq]; exact sub_sub hp.fit (Nat.zero_le _) hd hd'
  refine WP.mono (copyWords_ok cu eu hd hread hsep n (Nat.le_refl _)) fun t ht => ?_
  refine ⟨hu.of_offset hp.fit ht.keep.scalar ht.frame hd0 hd hd', fun k hk => ?_, ?_⟩
  · rw [ht.words k hk]; exact inputWord_same hi hu hk
  · have hf := ht.frame; rw [mu] at hf; exact hf
end VG.Proof.Ed25519.X86
