import VerifiedGarbage.Impl.Ed25519.X86.InputSlice
import VerifiedGarbage.Proof.Ed25519.X86.InputBits

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

structure SlicePre (s₀ : State) (scidx : Nat) (p : BitVec 32) (bytes : Nat) : Prop where
  rd : ∀ k len, 0 < len → k + len ≤ bytes → InRegions (s₀.rd ++ s₀.wr) (addr p k) len
  fit : p.toNat + bytes ≤ 2 ^ 32
  sep : (sub p 0 bytes).Disjoint (scR (arg s₀ scidx))

theorem slice_contains {s₀ : State} {scidx n k len : Nat} {p : BitVec 32}
    (h : SlicePre s₀ scidx p n) (hk : k + len ≤ n) (hlen : 0 < len) :
    (sub p 0 n).Contains (addr p k) len :=
  sub_contains (by have := h.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) hlen

theorem slice_read {s₀ : State} {scidx n k len : Nat} {p : BitVec 32}
    (h : SlicePre s₀ scidx p n) (hk : k + len ≤ n) (hlen : 0 < len) :
    InRegions (s₀.rd ++ s₀.wr) (addr p k) len := h.rd k len hlen hk

theorem slice_sub {s₀ : State} {scidx n k len : Nat} {p : BitVec 32}
    (h : SlicePre s₀ scidx p n) (hk : k + len ≤ n) (hlen : 0 < len) :
    (sub p k len).Sub (sub p 0 n) := by
  rw [sub, sub, addr_eq (by have := h.fit; omega_using [this, hk, hlen]), addr_zero]
  exact Offset.sub_base _ hk

theorem sliceBytes_same {s₀ s : State} {scidx n : Nat} {p : BitVec 32} (hi : SlicePre s₀ scidx p n)
    (hs : Saved s₀ (arg s₀ scidx) s) :
    Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n = Spec.Ed25519.bytesAt s₀.mem (p.setWidth 64) n := by
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [← addr_eq (by have := hi.fit; omega_using [this, hk'])]
  apply hs.frame
  intro r hr; rw [List.mem_singleton.mp hr]
  exact hi.sep _ (slice_contains hi (by omega_using [hk']) (by have := hi.fit; omega_using [this, hk']))

theorem loadSlicePointer_ok {s₀ s : State} {scidx argc i skip : Nat}
    (hp : ScratchPre s₀ scidx argc) (hs : Saved s₀ (arg s₀ scidx) s) (hi : i < argc) :
    WP isa (.block (loadSlicePointer i skip)) s fun t =>
      Saved s₀ (arg s₀ scidx) t ∧ t.gpr .esi = arg s₀ i + BitVec.ofNat 32 skip ∧ t.mem = s.mem := by
  have h := loadArg_ok hp hs hi
  refine WP.block_append (M := isa) (l₁ := ([.mov .esi (.mem (at_ .esp (4 + 4 * i)))] : List Instr))
    (WP.mono h fun u ⟨hu, eu, mu⟩ => ?_)
  refine Wp.wp_addi fun t ht => WP.block_nil ?_
  refine ⟨⟨(ht.other _ (by decide)).trans hu.edi, (ht.other _ (by decide)).trans hu.esp,
    ht.rd.trans hu.rd, ht.wr.trans hu.wr, by rw [ht.mem]; exact hu.frame,
    fun j hj => by rw [ht.mem]; exact hu.saved j hj⟩, ?_, ht.mem.trans mu⟩
  rw [ht.gpr, eu]

theorem inputSliceWords_ok {s₀ s : State} {scidx argc i skip n dst : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : SlicePre s₀ scidx (arg s₀ i + BitVec.ofNat 32 skip) (4 * n))
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc)
    (hd0 : 16 ≤ dst) (hd : dst + 4 * n ≤ 8192) (hd' : dst < 8192) :
    WP isa (.block (inputSliceWords i skip dst n)) s fun t => Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < n, wd t.mem (arg s₀ scidx) (dst + 4 * k) =
        wd s₀.mem (arg s₀ i + BitVec.ofNat 32 skip) (4 * k)) ∧
      Frame [sub (arg s₀ scidx) dst (4 * n)] s.mem t.mem := by
  refine WP.block_append (WP.mono (loadSlicePointer_ok hp hs hia) fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hr : ∀ k < n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i + BitVec.ofNat 32 skip) (4 * k)) 4 := by
    intro k hk; rw [hu.rd, hu.wr]
    exact slice_read hi (by omega_using [hk]) (by decide)
  have hsep : ∀ k < n, (sub (arg s₀ i + BitVec.ofNat 32 skip) (4 * k) 4).Disjoint (sub (arg s₀ scidx) dst (4 * n)) := by
    intro k hk
    refine (hi.sep.sub_left (slice_sub hi (by omega_using [hk]) (by decide))).sub_right ?_
    rw [scR_eq]; exact sub_sub hp.fit (Nat.zero_le _) hd hd'
  refine WP.mono (copyWords_ok cu eu hd hr hsep n (Nat.le_refl _)) fun t ht => ?_
  refine ⟨hu.of_offset hp.fit ht.keep.scalar ht.frame hd0 hd hd', ?_, by rw [← mu]; exact ht.frame⟩
  intro k hk
  rw [ht.words k hk]
  exact hu.frame.readW (slice_contains hi (by omega_using [hk]) (by decide))
    (by simp only [List.mem_singleton]; rintro r rfl; exact hi.sep) (by decide)

theorem inputSliceBits_ok {s₀ s : State} {scidx argc i skip bytes : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : SlicePre s₀ scidx (arg s₀ i + BitVec.ofNat 32 skip) bytes)
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : bytes ≤ 64) :
    WP isa (.block (inputSliceBits i skip bytes)) s fun t => Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < 8 * bytes, t.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem
          ((arg s₀ i + BitVec.ofNat 32 skip).setWidth 64) bytes) / 2 ^ k % 2)) ∧
      Frame [sub (arg s₀ scidx) 7168 (8 * bytes)] s.mem t.mem := by
  refine WP.block_append (WP.mono (loadSlicePointer_ok hp hs hia) fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr
  have hr : ∀ k < bytes, InRegions (u.rd ++ u.wr) (addr (arg s₀ i + BitVec.ofNat 32 skip) k) 1 := by
    intro k hk; rw [hu.rd, hu.wr]
    exact slice_read hi (by omega_using [hk]) (by decide)
  have hsep : ∀ k < bytes, (sub (arg s₀ i + BitVec.ofNat 32 skip) k 1).Disjoint (sub (arg s₀ scidx) 7168 (8 * bytes)) := by
    intro k hk
    refine (hi.sep.sub_left (slice_sub hi (by omega_using [hk]) (by decide))).sub_right ?_
    rw [scR_eq]; exact sub_sub hp.fit (by decide) (by omega_using [hn]) (by decide)
  refine WP.mono (expandScalarBits_ok cu eu hn hi.fit hr hsep) fun t ⟨kt, ft, bt⟩ => ?_
  refine ⟨hu.of_offset hp.fit kt.scalar ft (by decide) (by omega_using [hn]) (by decide), ?_, by rw [← mu]; exact ft⟩
  intro k hk
  rw [bt k hk, sliceBytes_same hi hu]

end VG.Proof.Ed25519.X86
