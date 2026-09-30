import VerifiedGarbage.Impl.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Proof.X25519.X86_64.Bits

/-! Untrusted: expanding each input byte uses the existing verified bit stores. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr off ofs Outside)

theorem scalarBitWide_ok {s : State} {base : Addr} (hs : Scratch s base)
    (i j : Nat) (hi : i < 64) (hj : j < 8) (hc : s.gpr .rbx = BitVec.ofNat 64 i)
    (b : BitVec 8) (hb : s.gpr .rax = b.setWidth 64) :
    WP isa (.block (expandScalarBit j)) s fun t =>
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = s.mem.writeW (off base (768 + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hg, hr, hw, hm⟩ := Proof.X25519.X86_64.bitJ_ok hn hi hc hb hj
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hg, rfl, rfl, hm⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  change Exec isa (.block (expandScalarBit j)) _ _ _ at e
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

structure BitKeep (base : Addr) (i n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rdx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base (768 + 8 * i) n s.mem t.mem

theorem BitKeep.scratch {base : Addr} {i n : Nat} {s t : State}
    (h : BitKeep base i n s t) (hs : Scratch s base) : Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem scalarBitPrefix_ok {s : State} {base : Addr} (hs : Scratch s base)
    (i n : Nat) (hi : i < 64) (hn : n ≤ 8) (hc : s.gpr .rbx = BitVec.ofNat 64 i)
    (b : BitVec 8) (hb : s.gpr .rax = b.setWidth 64) :
    WP isa (.block ((List.range n).flatMap expandScalarBit)) s fun t => BitKeep base i n s t ∧
      ∀ j < n, t.mem (off base (768 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩, fun _ h => by omega⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega) hc hb) fun t ⟨hk, hv⟩ => ?_
    refine WP.mono (scalarBitWide_ok (hk.scratch hs) i n hi (by omega)
      ((hk.gpr _ (by decide)).trans hc) b ((hk.gpr _ (by decide)).trans hb))
      fun u ⟨ug, ur, uw, um⟩ => ?_
    refine ⟨⟨fun r hr => (ug r hr).trans (hk.gpr r hr), ur.trans hk.rd, uw.trans hk.wr, ?_⟩, ?_⟩
    · intro p hp
      rw [um, Proof.X25519.X86_64.writeW8_outside _ _ _ (by omega) (by omega), hk.mem p (by omega)]
    · intro j hj
      rw [um, Proof.X25519.X86_64.writeW8_apply]
      by_cases h : j = n
      · subst j; rw [ite_eq_left rfl]
      · rw [ite_eq_right (fun he => h (by
          have hh := (Proof.X25519.X86_64.off_eq_iff base (by omega) (by omega)).mp he
          omega))]
        exact hv j (by omega)

end VG.Proof.Ed25519.X86_64
