import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Merkle–Damgård hash functions on x86-64: length fields and digests

Untrusted: everything here is checked by Lean. What the length fields
(`len64`) and digests (`out32`, `out64`) of `Impl/MdStream/X86_64.lean` write,
for the hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame)

/-! ## Byte order -/

/-- The bytes of a byte-reversed word, one by one. -/
theorem bswap32_byte_0 (x : BitVec 32) : (bswap32 x).extractLsb' 0 8 = x.extractLsb' 24 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap32_byte_1 (x : BitVec 32) : (bswap32 x).extractLsb' 8 8 = x.extractLsb' 16 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap32_byte_2 (x : BitVec 32) : (bswap32 x).extractLsb' 16 8 = x.extractLsb' 8 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap32_byte_3 (x : BitVec 32) : (bswap32 x).extractLsb' 24 8 = x.extractLsb' 0 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bswap64_byte_0 (x : BitVec 64) : (bswap64 x).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 56) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_1 (x : BitVec 64) : (bswap64 x).extractLsb' 8 8 = x.extractLsb' 48 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 48) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_2 (x : BitVec 64) : (bswap64 x).extractLsb' 16 8 = x.extractLsb' 40 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 40) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_3 (x : BitVec 64) : (bswap64 x).extractLsb' 24 8 = x.extractLsb' 32 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 32) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_4 (x : BitVec 64) : (bswap64 x).extractLsb' 32 8 = x.extractLsb' 24 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_5 (x : BitVec 64) : (bswap64 x).extractLsb' 40 8 = x.extractLsb' 16 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_6 (x : BitVec 64) : (bswap64 x).extractLsb' 48 8 = x.extractLsb' 8 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_7 (x : BitVec 64) : (bswap64 x).extractLsb' 56 8 = x.extractLsb' 0 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then bswap32 x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · rfl
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, bswap32_byte_0, bswap32_byte_1, bswap32_byte_2,
      bswap32_byte_3]


theorem bytes64_store (be : Bool) (x : BitVec 64) :
    (List.range 8).map (fun j => (if be then bswap64 x else x).extractLsb' (8 * j) 8) = bytes64 be x := by
  cases be
  · rfl
  · simp only [bytes64, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.reverse_cons, List.reverse_nil, Nat.reduceMul,
      bswap64_byte_0, bswap64_byte_1, bswap64_byte_2, bswap64_byte_3, bswap64_byte_4, bswap64_byte_5, bswap64_byte_6,
      bswap64_byte_7]


theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then bswap32 x else x) = writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bytes32_store]; rfl

theorem writeW64 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 64) :
    m.writeW a (if be then bswap64 x else x) = writeBytes m a (bytes64 be x) := by
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

/-- `len64 d be` stores `8 · r12` at `rbx + d`. -/
theorem len64_ok {d : Nat} {be : Bool} {s : State} {rest : List Instr} {Q : State → Prop}
    (hout : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) 8)
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .r12).toNat))) → WP isa (.block rest) s' Q) :
    WP isa (.block (len64 d be ++ rest)) s Q := by
  have hdi : BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d := ofInt_natCast d
  refine wp_mov fun s₁ u₁ _ _ => wp_add fun s₂ u₂ => wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => ?_
  have g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s.gpr r := fun r h => by
    rw [u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  have v₄ : s₄.gpr .rax = BitVec.ofNat 64 (8 * (s.gpr .r12).toNat) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, times8]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have ea : ∀ t : State, t.gpr .rbx = s.gpr .rbx →
      t.ea (at_ .rbx d) = s.gpr .rbx + BitVec.ofNat 64 d := fun t ht => by rw [ea_at, ht, hdi]
  cases be
  · simp only [Bool.false_eq_true, ite_false]
    refine wp_store (ea s₄ (g₄ _ (by decide))) (by rw [wr₄]; exact hout) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
    refine k s₅ (fun r h => by rw [g₅, g₄ r h]) (rd₅.trans rd₄) (wr₅.trans wr₄) ?_
    rw [m₅, m₄, v₄, ← writeW64 _ _ false]; rfl
  · simp only [ite_true]
    refine wp_bswap fun s₅ u₅ => wp_store (ea s₅ (by rw [u₅.other _ (by decide), g₄ _ (by decide)]))
      (by rw [u₅.wr, wr₄]; exact hout) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
    refine k s₆ (fun r h => by rw [g₆, u₅.other r h, g₄ r h]) (by rw [rd₆, u₅.rd, rd₄]) (by rw [wr₆, u₅.wr, wr₄]) ?_
    rw [m₆, u₅.mem, m₄, u₅.gpr, v₄, ← writeW64 _ _ true]; rfl

/-! ## The digest -/

/-- Words `[k, n)` of the hash value at `rbx` are written as `f` says, the first
`k` already written. -/
theorem out_words {w : Nat} (n : Nat) (hn : w * n ≤ 64) (f : BitVec (8 * w) → List Byte)
    (hf : ∀ x, (f x).length = w) (ins : Nat → List Instr) {s₀ : State}
    (hstep : ∀ k < n, ∀ (s : State) (rest : List Instr) (Q : State → Prop),
      s.gpr .rbx = s₀.gpr .rbx → s.gpr .rbp = s₀.gpr .rbp → s.rd = s₀.rd → s.wr = s₀.wr →
      (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = writeBytes s.mem (s₀.gpr .rbp + BitVec.ofNat 64 (w * k))
          (f (s.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k)) (8 * w))) → WP isa (.block rest) s' Q) →
      WP isa (.block (ins k ++ rest)) s Q)
    (hd : Region.Disjoint ⟨s₀.gpr .rbx, w * n⟩ ⟨s₀.gpr .rbp, w * n⟩) :
    ∀ j ≤ n, ∀ s, (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.mem = writeBytes s₀.mem (s₀.gpr .rbp)
        ((List.range (n - j)).flatMap fun k => f (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k)) (8 * w))) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap ins)) s fun s' =>
        (∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
        s'.mem = writeBytes s₀.mem (s₀.gpr .rbp)
          ((List.range n).flatMap fun k => f (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k)) (8 * w))) := by
  have hflat : ∀ k, ((List.range k).flatMap fun k => f (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k))
      (8 * w))).length = w * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => hf _), List.map_const', List.sum_replicate_nat,
      List.length_range, Nat.mul_comm]
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, m⟩
  | succ j ih =>
    intro hj s g rd wr m
    have hk : n - (j + 1) < n := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
    refine hstep _ hk s _ _ (by rw [g _ (by decide)]) (by rw [g _ (by decide)]) rd wr
      fun s' g' rd' wr' m' => ?_
    rw [show n - (j + 1) + 1 = n - j by omega]
    refine ih (by omega) s' (fun r h => by rw [g' r h, g r h]) (rd'.trans rd) (wr'.trans wr) ?_
    -- The word read is not yet overwritten.
    have h1 : w * (n - (j + 1)) + w ≤ w * n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    have e8 : 8 * w / 8 = w := Nat.mul_div_cancel_left w (by decide)
    have hread : s.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * (n - (j + 1)))) (8 * w) =
        s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * (n - (j + 1)))) (8 * w) := by
      rw [m]
      refine (writeBytes_frame _ _ _ (R := ⟨s₀.gpr .rbp, w * n⟩) ?_).readW
        (r := ⟨s₀.gpr .rbx + BitVec.ofNat 64 (w * (n - (j + 1))), w⟩)
        (by rw [e8]; exact Region.contains_self _ _) ?_ (by rw [e8]; omega)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        exact Nat.mul_le_mul_left _ (by omega)
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset h1 (by omega))
    rw [m', hread, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, ← writeBytes_append _ _ _ _ (by rw [hflat, hf]; omega), hflat]

theorem setWidth32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `out32 n be` writes the `n` 32-bit words at `rbx` to `rbp`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rbx) (4 * n)) (hout : InRegions s₀.wr (s₀.gpr .rbp) (4 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .rbx, 4 * n⟩ ⟨s₀.gpr .rbp, 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = writeBytes s₀.mem (s₀.gpr .rbp)
        ((List.range n).flatMap fun k => bytes32 be (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (4 * k)) 32)) := by
  have h := out_words (w := 4) n hn (bytes32 be) (bytes32_length be)
    (fun k => [.mov32 .rax (.mem (at_ .rbx (4 * k)))] ++ (if be then [.bswap32 .rax] else []) ++
      [.store32 (at_ .rbp (4 * k)) .rax]) (s₀ := s₀) ?_ hd n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx hbp hrd hwr kk
  have hoff : 4 * k + 4 ≤ 4 * n := by omega
  refine wp_mov32m (a := s₀.gpr .rbx + BitVec.ofNat 64 (4 * k)) (by rw [ea_at, hbx, ofInt_natCast])
    (by rw [hrd, hwr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
  have ea₁ : ∀ t : State, t.gpr .rbp = s₀.gpr .rbp →
      t.ea (at_ .rbp (4 * k)) = s₀.gpr .rbp + BitVec.ofNat 64 (4 * k) := fun t ht => by
    rw [ea_at, ht, ofInt_natCast]
  cases be
  · refine wp_store32 (ea₁ s₁ (by rw [u₁.other _ (by decide), hbp]))
      (by rw [u₁.wr, hwr]; exact InRegions.offset hout hoff (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
    refine kk s₂ (fun r h => by rw [g₂, u₁.other r h]) (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr]) ?_
    rw [m₂, u₁.mem, u₁.gpr, setWidth32, ← writeW32 _ _ false]; rfl
  · refine wp_bswap32 fun s₂ u₂ => wp_store32 (ea₁ s₂ (by rw [u₂.other _ (by decide),
      u₁.other _ (by decide), hbp])) (by rw [u₂.wr, u₁.wr, hwr]; exact InRegions.offset hout hoff (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => ?_
    refine kk s₃ (fun r h => by rw [g₃, u₂.other r h, u₁.other r h]) (by rw [rd₃, u₂.rd, u₁.rd])
      (by rw [wr₃, u₂.wr, u₁.wr]) ?_
    rw [m₃, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, setWidth32, setWidth32, ← writeW32 _ _ true]; rfl

/-- `out64 n` writes the `n` 64-bit words at `rbx` to `rbp`, big-endian. -/
theorem out64_ok {n : Nat} (hn : 8 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rbx) (8 * n)) (hout : InRegions s₀.wr (s₀.gpr .rbp) (8 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .rbx, 8 * n⟩ ⟨s₀.gpr .rbp, 8 * n⟩) :
    WP isa (.block (out64 n)) s₀ fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = writeBytes s₀.mem (s₀.gpr .rbp)
        ((List.range n).flatMap fun k => bytes64 true (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64)) := by
  have h := out_words (w := 8) n hn (bytes64 true) (bytes64_length true)
    (fun k => [.mov .rax (.mem (at_ .rbx (8 * k))), .bswap .rax, .store (at_ .rbp (8 * k)) .rax])
    (s₀ := s₀) ?_ hd n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx hbp hrd hwr kk
  have hoff : 8 * k + 8 ≤ 8 * n := by omega
  refine wp_movm (a := s₀.gpr .rbx + BitVec.ofNat 64 (8 * k)) (by rw [ea_at, hbx, ofInt_natCast])
    (by rw [hrd, hwr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
  refine wp_bswap fun s₂ u₂ => wp_store (a := s₀.gpr .rbp + BitVec.ofNat 64 (8 * k))
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbp, ofInt_natCast])
    (by rw [u₂.wr, u₁.wr, hwr]; exact InRegions.offset hout hoff (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine kk s₃ (fun r h => by rw [g₃, u₂.other r h, u₁.other r h]) (by rw [rd₃, u₂.rd, u₁.rd])
    (by rw [wr₃, u₂.wr, u₁.wr]) ?_
  rw [m₃, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, ← writeW64 _ _ true]; rfl

end VG.Proof.MdStream.X86_64
