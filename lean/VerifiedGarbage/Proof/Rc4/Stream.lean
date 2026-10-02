import VerifiedGarbage.Proof.Rc4.Memory

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

theorem bytes_cons (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1#64) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, BitVec.add_zero]
  congr 1
  apply List.map_congr_left
  intro k hk
  change m (p + BitVec.ofNat 64 (k + 1)) = m (p + 1#64 + BitVec.ofNat 64 k)
  rw [Offset.add_ofNat_succ]
  rfl

/-- The writes of a stream operation stay within its table and data. -/
def StreamFrame (p d : Addr) (n : Nat) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 256 → ¬ (x - d).toNat < n → m' x = m x

theorem stream_frame_step (m : Mem) (p d : Addr) (i j value : Byte) :
    StreamFrame p d 1 m (((m.write (p + BitVec.ofNat 64 j.toNat) 1
      (m (p + BitVec.ofNat 64 i.toNat))).write (p + BitVec.ofNat 64 i.toNat) 1
        (m (p + BitVec.ofNat 64 j.toNat))).write d 1 value) := by
  intro x hp hd
  have hne : x ≠ d := by
    intro he; subst x; exact hd (by simp [BitVec.sub_self])
  rw [write_byte, ite_eq_right hne]
  exact swap_frame m p i j x hp

theorem sep_symm {p q : Addr} {n k : Nat} (h : Mem.Sep p n q k) : Mem.Sep q k p n :=
  fun x hx hy => h x hy hx

theorem sep_tail {p d : Addr} {n : Nat} (_hn : n + 1 < 2 ^ 64)
    (h : Mem.Sep p 256 d (n + 1)) : Mem.Sep p 256 (d + 1#64) n := by
  intro x hp ht
  apply h x hp
  have hh : (⟨d, n + 1⟩ : Region).Contains (d + 1#64) n := by
    change (d + 1#64 - d).toNat + n ≤ n + 1
    rw [Offset.add_sub_cancel_left]
    change 1 + n ≤ n + 1
    omega
  have hb := hh.byte ht
  change (x - d).toNat + 1 ≤ n + 1 at hb
  omega

theorem bytes_write_sep (m : Mem) (d q : Addr) (n : Nat) (value : Byte)
    (hn : n < 2 ^ 64) (h : Mem.Sep d n q 1) :
    bytesAt (m.write q 1 value) d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  exact Mem.write_apply (h _ (by rw [Mem.sub_ofNat_toNat d (by omega)]; exact hk'))

theorem bytes_table_frame (m m' : Mem) (p d : Addr) (n : Nat) (hn : n < 2 ^ 64)
    (h : TableFrame p m m') (hs : Mem.Sep d n p 256) : bytesAt m' d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  exact h _ (hs _ (by rw [Mem.sub_ofNat_toNat d (by omega)]; exact hk'))

theorem stream_frame_trans_tail {m a b : Mem} {p d : Addr} {n : Nat}
    (h : StreamFrame p d 1 m a) (k : StreamFrame p (d + 1#64) n a b) :
    StreamFrame p d (n + 1) m b := by
  intro x hp hd
  have htail : ¬ (x - (d + 1#64)).toNat < n := by
    intro hx
    have hc : (⟨d, n + 1⟩ : Region).Contains (d + 1#64) n := by
      change (d + 1#64 - d).toNat + n ≤ n + 1
      rw [Offset.add_sub_cancel_left]
      change 1 + n ≤ n + 1
      omega
    have hh := hc.byte hx
    change (x - d).toNat + 1 ≤ n + 1 at hh
    omega
  exact (k x hp htail).trans (h x hp (by omega))

theorem stream_head (m m' : Mem) (p d : Addr) (n : Nat) (hn : n + 1 < 2 ^ 64)
    (h : StreamFrame p (d + 1#64) n m m') (hs : Mem.Sep p 256 d (n + 1)) : m' d = m d := by
  have hp : ¬ (d - p).toNat < 256 := by
    intro hh
    exact hs d hh (by simp only [BitVec.sub_self]; change 0 < n + 1; omega)
  apply h d hp
  have hsep : Mem.Sep d 1 (d + 1#64) n := Offset.sep_base d (by decide) (by omega)
  exact hsep d (by simp only [BitVec.sub_self]; decide)

theorem sep_offset_right {d p : Addr} {n k off count : Nat}
    (h : Mem.Sep d n p k) (ho : off < 2 ^ 64) (hc : off + count ≤ k) :
    Mem.Sep d n (p + BitVec.ofNat 64 off) count := by
  intro x hd hx
  apply h x hd
  have hh : (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 off) count :=
    Offset.contains_base p hc ho
  have hb := hh.byte hx
  change (x - p).toNat + 1 ≤ k at hb
  omega

end VG.Proof.Rc4
