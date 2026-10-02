import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Merkle–Damgård hash functions on AArch64: length fields and digests

What the length fields (`len64`) and digests (`out32`) of
`Impl/MdStream/AArch64.lean` write, for the hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.AArch64

open VG VG.AArch64 VG.Impl.MdStream.AArch64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame)

/-! ## Byte order -/

/-- The bytes of a byte-reversed word, one by one. -/
theorem rev32_byte_0 (x : BitVec 32) : (rev32 x).extractLsb' 0 8 = x.extractLsb' 24 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_1 (x : BitVec 32) : (rev32 x).extractLsb' 8 8 = x.extractLsb' 16 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_2 (x : BitVec 32) : (rev32 x).extractLsb' 16 8 = x.extractLsb' 8 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_3 (x : BitVec 32) : (rev32 x).extractLsb' 24 8 = x.extractLsb' 0 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem rev64_byte_0 (x : BitVec 64) : (rev64 x).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 56) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_1 (x : BitVec 64) : (rev64 x).extractLsb' 8 8 = x.extractLsb' 48 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 48) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_2 (x : BitVec 64) : (rev64 x).extractLsb' 16 8 = x.extractLsb' 40 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 40) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_3 (x : BitVec 64) : (rev64 x).extractLsb' 24 8 = x.extractLsb' 32 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 32) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_4 (x : BitVec 64) : (rev64 x).extractLsb' 32 8 = x.extractLsb' 24 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_5 (x : BitVec 64) : (rev64 x).extractLsb' 40 8 = x.extractLsb' 16 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_6 (x : BitVec 64) : (rev64 x).extractLsb' 48 8 = x.extractLsb' 8 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_7 (x : BitVec 64) : (rev64 x).extractLsb' 56 8 = x.extractLsb' 0 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then rev32 x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · rfl
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, rev32_byte_0, rev32_byte_1, rev32_byte_2,
      rev32_byte_3]


theorem bytes64_store (be : Bool) (x : BitVec 64) :
    (List.range 8).map (fun j => (if be then rev64 x else x).extractLsb' (8 * j) 8) = bytes64 be x := by
  cases be
  · rfl
  · simp only [bytes64, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.reverse_cons, List.reverse_nil, Nat.reduceMul,
      rev64_byte_0, rev64_byte_1, rev64_byte_2, rev64_byte_3, rev64_byte_4, rev64_byte_5, rev64_byte_6,
      rev64_byte_7]


theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then rev32 x else x) = writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bytes32_store]; rfl

theorem writeW64 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 64) :
    m.writeW a (if be then rev64 x else x) = writeBytes m a (bytes64 be x) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bytes64_store]; rfl

/-! ## Regions -/

theorem InRegions.offset {rs : List Region} {a : Addr} {n off m : Nat} (h : InRegions rs a n)
    (hm : off + m ≤ n) (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 off) m := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 off - R.base).toNat ≤ (a - R.base).toNat + off := by
    rw [Offset.add_sub_comm,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-! ## The length field -/

theorem times8 (x : BitVec 64) : x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

/-- `len64 d be` stores `8 · x22` at `x19 + d`. -/
theorem len64_ok {d : Nat} {be : Bool} {s : State} (hd : d < 4096)
    (hout : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (len64 d be)) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .x22).toNat))) := by
  unfold len64
  rw [List.append_assoc]
  refine wp_add fun s₁ u₁ => wp_add fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have g₃ : ∀ r, r ≠ .x9 → s₃.gpr r = s.gpr r := fun r h => by
    rw [u₃.other r h, u₂.other r h, u₁.other r h]
  have v₃ : s₃.gpr .x9 = BitVec.ofNat 64 (8 * (s.gpr .x22).toNat) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, times8]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  -- The value, reversed if big-endian, is in `x9` of a state `t` like `s₃`.
  have st : ∀ (t : State), (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → t.sp = s.sp →
      t.gpr .x9 = (if be then rev64 (BitVec.ofNat 64 (8 * (s.gpr .x22).toNat))
        else BitVec.ofNat 64 (8 * (s.gpr .x22).toNat)) →
      WP isa (.block (if d % 8 = 0 then [.str .x .x9 .x19 d] else [.addImm .x .x12 .x19 d, .str .x .x9 .x12 0]))
        t fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
          s'.sp = s.sp ∧ s'.mem = writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 d)
            (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .x22).toNat))) := by
    intro t g m rd wr sp v
    have h19 : t.gpr .x19 = s.gpr .x19 := g _ (by decide)
    by_cases hd8 : d % 8 = 0
    · simp only [hd8, ite_true]
      refine wp_str (a := s.gpr .x19 + BitVec.ofNat 64 d) ⟨hd8, by omega⟩ (by rw [h19])
        (by rw [wr]; exact hout) fun s' g' => WP.block_nil ⟨fun r h h' => by rw [g'.gpr, g r h],
          g'.rd.trans rd, g'.wr.trans wr, g'.sp.trans sp, ?_⟩
      rw [g'.mem, m, v, writeW64]
    · simp only [hd8, ite_false]
      refine wp_addImm hd fun t₁ u => wp_str (a := s.gpr .x19 + BitVec.ofNat 64 d) (by decide)
        (by rw [u.gpr, h19]; simp) (by rw [u.wr, wr]; exact hout) fun s' g' => WP.block_nil
          ⟨fun r h h' => by rw [g'.gpr, u.other r h', g r h], by rw [g'.rd, u.rd, rd],
            by rw [g'.wr, u.wr, wr], by rw [g'.sp, u.sp, sp], ?_⟩
      rw [g'.mem, u.mem, m, u.other _ (by decide), v, writeW64]
  cases be
  · simp only [Bool.false_eq_true, ite_false, List.nil_append]
    exact st s₃ g₃ m₃ rd₃ wr₃ sp₃ v₃
  · simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_rev fun s₄ u₄ => st s₄ (fun r h => by rw [u₄.other r h, g₃ r h]) (by rw [u₄.mem, m₃])
      (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃]) (by rw [u₄.sp, sp₃]) (by rw [u₄.gpr, v₃]; rfl)

/-! ## The digest -/

theorem setWidth32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `out32 n be` writes the `n` 32-bit words at `x19` to `x21`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x19) (4 * n)) (hout : InRegions s₀.wr (s₀.gpr .x21) (4 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .x19, 4 * n⟩ ⟨s₀.gpr .x21, 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = writeBytes s₀.mem (s₀.gpr .x21)
        ((List.range n).flatMap fun k => bytes32 be (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * k)) 32)) := by
  let f : Nat → List Byte := fun k => bytes32 be (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * k)) 32)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 4 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => bytes32_length _ _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.sp = s₀.sp → s.mem = writeBytes s₀.mem (s₀.gpr .x21) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        [.ldr .w .x9 .x19 (4 * k)] ++ (if be then [.rev32 .x9 .x9] else []) ++ [.str .w .x9 .x21 (4 * k)]))
        s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = writeBytes s₀.mem (s₀.gpr .x21) ((List.range n).flatMap f) by
    have := h n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl rfl
      (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
    rwa [Nat.sub_self, List.drop_zero] at this
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr sp m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, sp, m⟩
  | succ j ih =>
    intro hj s g rd wr sp m
    have hk : n - (j + 1) < n := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range,
      List.append_assoc, List.append_assoc]
    rw [show n - (j + 1) + 1 = n - j by omega]
    have hoff : 4 * (n - (j + 1)) + 4 ≤ 4 * n := by omega
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 =
        s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 := by
      rw [m]
      refine (writeBytes_frame _ _ _ (R := ⟨s₀.gpr .x21, 4 * n⟩) ?_).readW
        (r := ⟨s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1))), 4⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset hoff (by omega))
    have hmem : ∀ (t : State), t.mem = s.mem →
        t.mem.writeW (s₀.gpr .x21 + BitVec.ofNat 64 (4 * (n - (j + 1))))
          (if be then rev32 (s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32)
            else s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32) =
        writeBytes s₀.mem (s₀.gpr .x21) ((List.range (n - j)).flatMap f) := by
      intro t ht
      rw [ht, writeW32, hread, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
        List.flatMap_append, List.flatMap_singleton,
        ← writeBytes_append _ _ _ _ (by rw [hflat, bytes32_length]; omega), hflat]
    refine wp_ldr32 (a := s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) (by omega)
      (by rw [g _ (by decide)]) (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
    have ea : ∀ t : State, t.gpr .x21 = s.gpr .x21 →
        t.gpr .x21 + BitVec.ofNat 64 (4 * (n - (j + 1))) = s₀.gpr .x21 + BitVec.ofNat 64 (4 * (n - (j + 1))) :=
      fun t ht => by rw [ht, g _ (by decide)]
    cases be
    · simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
      refine wp_str32 (by omega) (ea s₁ (u₁.other _ (by decide)))
        (by rw [u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₂ g₂ => ?_
      refine ih (by omega) s₂ (fun r h => by rw [g₂.gpr, u₁.other r h, g r h]) (by rw [g₂.rd, u₁.rd, rd])
        (by rw [g₂.wr, u₁.wr, wr]) (by rw [g₂.sp, u₁.sp, sp]) ?_
      rw [g₂.mem, u₁.gpr, setWidth32]
      exact hmem s₁ u₁.mem
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine wp_rev32 fun s₂ u₂ => wp_str32 (by omega) (ea s₂ (by rw [u₂.other _ (by decide),
        u₁.other _ (by decide)])) (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega))
        fun s₃ g₃ => ?_
      refine ih (by omega) s₃ (fun r h => by rw [g₃.gpr, u₂.other r h, u₁.other r h, g r h])
        (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
      rw [g₃.mem, u₂.mem, u₂.gpr, u₁.gpr, setWidth32, setWidth32]
      exact hmem s₁ u₁.mem

end VG.Proof.MdStream.AArch64
