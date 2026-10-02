import VerifiedGarbage.Impl.Ed25519.X86.InputBits
import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Ed25519.X86.BitsExpand

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem inputByte_contains {s₀ : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    {k : Nat} (hk : k < 4 * n) : (sub (arg s₀ i) 0 (4 * n)).Contains (addr (arg s₀ i) k) 1 :=
  sub_contains (by have := hp.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)

theorem inputBytes_same {s₀ s : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) :
    Spec.Ed25519.bytesAt s.mem ((arg s₀ i).setWidth 64) (4 * n) =
      Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n) := by
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [← addr_eq (by have := hp.fit; omega_using [this, hk'])]
  apply hs.frame
  intro r hr; rw [List.mem_singleton.mp hr]
  exact hp.sep _ (inputByte_contains hp hk')

theorem inputBits_ok {s₀ s : State} {scidx argc i n : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : n ≤ 16) :
    WP isa (.block (inputBits i (4 * n))) s fun t => Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < 32 * n, t.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n)) / 2 ^ k % 2)) := by
  refine WP.block_append (WP.mono (loadArg_ok hp hs hia) fun u ⟨hu, eu, _⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hr : ∀ k < 4 * n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i) k) 1 := by
    intro k hk; refine ⟨_, ?_, inputByte_contains hi hk⟩
    rw [hu.rd, hu.wr]; exact hi.rd
  have hsep : ∀ k < 4 * n, (sub (arg s₀ i) k 1).Disjoint (sub (arg s₀ scidx) 7168 (8 * (4 * n))) := by
    intro k hk
    refine (hi.sep.sub_left ?_).sub_right ?_
    · rw [sub, sub, addr_eq (by have := hi.fit; omega_using [this, hk]), addr_zero]
      exact Offset.sub_base _ (by omega_using [hk])
    · rw [scR_eq]; exact sub_sub hp.fit (by decide) (by omega_using [hn]) (by decide)
  refine WP.mono (expandScalarBits_ok cu eu (by omega_using [hn]) hi.fit hr hsep)
    fun t ⟨kt, ft, bt⟩ => ?_
  refine ⟨hu.of_offset hp.fit (Keep.scalar kt) ft (by decide) (by omega_using [hn]) (by decide), fun k hk => ?_⟩
  rw [bt k (by omega_using [hk]), inputBytes_same hi hu]

end VG.Proof.Ed25519.X86
