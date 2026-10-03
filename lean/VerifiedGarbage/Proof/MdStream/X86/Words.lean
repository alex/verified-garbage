import VerifiedGarbage.Proof.MdStream.X86.Common

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): length fields and digests

What the length fields (`len64`) and digests (`out32`) of
`Impl/MdStream/X86.lean` write, for the hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.X86

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame shl3 bits8)

/-! ## Byte order -/

theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then bswap x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · simp [bytes32, List.range_succ]
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · refine byte_ext fun i hi => ?_
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | exact absurd hi (by omega)
        | (simp only [bswap, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp)

theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then bswap x else x) = writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bytes32_store]; rfl

/-- The bytes of a 64-bit word, from those of its halves. -/
theorem bytes64_halves (be : Bool) (hi lo : BitVec 32) :
    bytes64 be (hi ++ lo) = if be then bytes32 true hi ++ bytes32 true lo else bytes32 false lo ++ bytes32 false hi := by
  cases be <;>
  · simp only [bytes64, bytes32, Bool.false_eq_true, ite_true, ite_false, List.range_succ, List.range_zero,
      List.nil_append, List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      split <;> first | omega | (congr 1; omega) | rfl

/-! ## The length field -/

theorem times8 (x : BitVec 32) : x + x + (x + x) + (x + x + (x + x)) = x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The bit count of a byte count, from its halves. -/
theorem bitCount (hi lo : BitVec 32) :
    (hi <<< 3 ||| lo >>> 29) ++ lo <<< 3 = BitVec.ofNat 64 (8 * (hi ++ lo).toNat) := by
  rw [shl3, bits8]

/-- `len64Of d be` stores `8 · count`, from `count` in `eax` (low word) and `ecx` (high word), at
`ebx + d`. -/
theorem len64Of_ok {d : Nat} {be : Bool} {s : State} {hi lo : BitVec 32}
    (hfit : (s.gpr .ebx).toNat + d + 8 ≤ 2 ^ 32) (hax : s.gpr .eax = lo) (hcx : s.gpr .ecx = hi)
    (ho₁ : InRegions s.wr (addr (s.gpr .ebx) d) 4) (ho₂ : InRegions s.wr (addr (s.gpr .ebx) (d + 4)) 4) :
    WP isa (.block (len64Of d be)) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (hi ++ lo).toNat))) := by
  unfold len64Of
  refine wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_shr (by decide) fun s₇ u₇ => wp_or fun s₈ u₈ => wp_add fun s₉ u₉ => wp_add fun s₁₀ u₁₀ =>
    wp_add fun s₁₁ u₁₁ => ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁₁.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₁₁.other r h1, u₁₀.other r h1, u₉.other r h1, u₈.other r h2, u₇.other r h3,
      u₆.other r h3, u₅.other r h2, u₄.other r h2, u₃.other r h2]
  have m₁₁ : s₁₁.mem = s.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have rd₁₁ : s₁₁.rd = s.rd := by
    rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]
  have wr₁₁ : s₁₁.wr = s.wr := by
    rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]
  have c5 : s₅.gpr .ecx = hi <<< 3 := by rw [u₅.gpr, u₄.gpr, u₃.gpr, hcx, times8]
  have a5 : s₅.gpr .eax = lo := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hax]
  have d7 : s₇.gpr .edx = lo >>> 29 := by rw [u₇.gpr, u₆.gpr, a5]
  have c8 : s₈.gpr .ecx = (hi <<< 3) ||| (lo >>> 29) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), c5, d7]
  have a11 : s₁₁.gpr .eax = lo <<< 3 := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a5,
      times8]
  have c11 : s₁₁.gpr .ecx = (hi <<< 3) ||| (lo >>> 29) := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), c8]
  have ebx₁₁ : s₁₁.gpr .ebx = s.gpr .ebx := g _ (by decide) (by decide) (by decide)
  have e₁ : addr (s.gpr .ebx) d = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d := addr_eq (by omega)
  have hx := bitCount hi lo
  cases be
  · simp only [Bool.false_eq_true, ite_false]
    refine wp_store (a := addr (s.gpr .ebx) d) (by rw [ea_at, ebx₁₁]) (by rw [wr₁₁]; exact ho₁) fun s₁₂ u₁₂ => ?_
    refine wp_store (a := addr (s.gpr .ebx) (d + 4)) (by rw [ea_at, u₁₂.gpr, ebx₁₁])
      (by rw [u₁₂.wr, wr₁₁]; exact ho₂) fun s₁₃ u₁₃ => WP.block_nil ?_
    refine ⟨fun r h1 h2 h3 => by rw [u₁₃.gpr, u₁₂.gpr, g r h1 h2 h3], by rw [u₁₃.rd, u₁₂.rd, rd₁₁],
      by rw [u₁₃.wr, u₁₂.wr, wr₁₁], ?_⟩
    rw [u₁₃.mem, u₁₂.mem, u₁₂.gpr, a11, c11, m₁₁, ← hx, bytes64_halves]
    simp only [Bool.false_eq_true, ite_false]
    have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => writeW32 m a false x
    simp only [Bool.false_eq_true, ite_false] at w
    rw [w, w, e₁, show addr (s.gpr .ebx) (d + 4) = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d +
      BitVec.ofNat 64 (bytes32 false (lo <<< 3)).length by rw [addr_eq (by omega), add_ofNat]; rfl,
      writeBytes_append _ _ _ _ (by simp [bytes32])]
  · simp only [ite_true]
    refine wp_bswap fun s₁₂ u₁₂ => ?_
    refine wp_store (a := addr (s.gpr .ebx) d) (by rw [ea_at, u₁₂.other _ (by decide), ebx₁₁])
      (by rw [u₁₂.wr, wr₁₁]; exact ho₁) fun s₁₃ u₁₃ => wp_bswap fun s₁₄ u₁₄ => ?_
    refine wp_store (a := addr (s.gpr .ebx) (d + 4))
      (by rw [ea_at, u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), ebx₁₁])
      (by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]; exact ho₂) fun s₁₅ u₁₅ => WP.block_nil ?_
    refine ⟨fun r h1 h2 h3 => by rw [u₁₅.gpr, u₁₄.other r h1, u₁₃.gpr, u₁₂.other r h2, g r h1 h2 h3],
      by rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁], by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁], ?_⟩
    have a14 : s₁₄.gpr .eax = bswap (lo <<< 3) := by
      rw [u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), a11]
    have c12 : s₁₂.gpr .ecx = bswap ((hi <<< 3) ||| (lo >>> 29)) := by rw [u₁₂.gpr, c11]
    rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, a14, c12, m₁₁, ← hx, bytes64_halves]
    simp only [ite_true]
    have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => writeW32 m a true x
    simp only [ite_true] at w
    rw [w, w, e₁, show addr (s.gpr .ebx) (d + 4) = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d +
      BitVec.ofNat 64 (bytes32 true ((hi <<< 3) ||| (lo >>> 29))).length by
      rw [addr_eq (by omega), add_ofNat]; rfl,
      writeBytes_append _ _ _ _ (by simp [bytes32])]

/-- `loadCount so` loads `count` into `eax` (low word) and `ecx` (high word). -/
theorem loadCount_ok {so : Nat} {s : State} {rest : List Instr} {Q : State → Prop}
    (hlo : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 16)) 4)
    (hhi : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 20)) 4)
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.gpr .eax = s.mem.readW (addr (s.gpr .ebp) (so + 16)) 32 →
      s'.gpr .ecx = s.mem.readW (addr (s.gpr .ebp) (so + 20)) 32 → WP isa (.block rest) s' Q) :
    WP isa (.block (loadCount so ++ rest)) s Q := by
  refine wp_movm (a := addr (s.gpr .ebp) (so + 16)) (ea_at _ _ _) hlo fun s₁ u₁ => ?_
  refine wp_movm (a := addr (s.gpr .ebp) (so + 20)) (by rw [ea_at, u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact hhi) fun s₂ u₂ => k s₂ (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1])
      (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.other _ (by decide), u₁.gpr]) (by rw [u₂.gpr, u₁.mem])

/-- `len64 so d be` stores `8 · count`, from `count` in `[ebp + so + 16]` (low
word) and `[ebp + so + 20]` (high word), at `ebx + d`. -/
theorem len64_ok {so d : Nat} {be : Bool} {s : State} (hfit : (s.gpr .ebx).toNat + d + 8 ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 16)) 4)
    (hhi : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 20)) 4)
    (ho₁ : InRegions s.wr (addr (s.gpr .ebx) d) 4) (ho₂ : InRegions s.wr (addr (s.gpr .ebx) (d + 4)) 4) :
    WP isa (.block (len64 so d be)) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.mem.readW (addr (s.gpr .ebp) (so + 20)) 32 ++
          s.mem.readW (addr (s.gpr .ebp) (so + 16)) 32).toNat))) :=
  loadCount_ok hlo hhi fun s' g m rd wr ha hc => by
    have hb : s'.gpr .ebx = s.gpr .ebx := g _ (by decide) (by decide)
    refine (len64Of_ok (by rw [hb]; exact hfit) ha hc (by rw [wr, hb]; exact ho₁) (by rw [wr, hb]; exact ho₂)).mono
      fun s'' ⟨g', rd', wr', m'⟩ => ⟨fun r h1 h2 h3 => by rw [g' r h1 h2 h3, g r h1 h2], rd'.trans rd,
        wr'.trans wr, by rw [m', m, hb]⟩

/-! ## The digest -/

/-- The `w`-byte words `[k, n)` of the hash value at `ebx` are written to `eax` as `g` says, the
first `k` already written. -/
theorem out_words (n w : Nat) (hwn : w * n ≤ 64) (g : Nat → List Byte) (hg : ∀ k, (g k).length = w)
    (ins : Nat → List Instr) {s₀ : State}
    (hstep : ∀ k < n, ∀ (s : State) (rest : List Instr) (Q : State → Prop),
      s.gpr .ebx = s₀.gpr .ebx → s.gpr .eax = s₀.gpr .eax → s.rd = s₀.rd → s.wr = s₀.wr →
      Frame [⟨(s₀.gpr .eax).setWidth 64, w * n⟩] s₀.mem s.mem →
      (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = writeBytes s.mem ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (w * k)) (g k) →
        WP isa (.block rest) s' Q) →
      WP isa (.block (ins k ++ rest)) s Q) :
    ∀ j ≤ n, ∀ s, (∀ r, r ≠ .ecx → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.mem = writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64) ((List.range (n - j)).flatMap g) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap ins)) s fun s' =>
        (∀ r, r ≠ .ecx → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
        s'.mem = writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64) ((List.range n).flatMap g) := by
  have hflat : ∀ k, ((List.range k).flatMap g).length = w * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => hg _), List.map_const', List.sum_replicate_nat,
      List.length_range, Nat.mul_comm]
  intro j
  induction j with
  | zero =>
    intro _ s hg' rd wr m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨hg', rd, wr, m⟩
  | succ j ih =>
    intro hj s hg' rd wr m
    have hk : n - (j + 1) < n := by omega
    have hle : w * (n - (j + 1)) + w ≤ w * n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left w (by omega)
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
    have hf : Frame [⟨(s₀.gpr .eax).setWidth 64, w * n⟩] s₀.mem s.mem := by
      rw [m]
      refine writeBytes_frame _ _ _ ?_
      rw [hflat]
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      omega
    refine hstep _ hk s _ _ (by rw [hg' _ (by decide)]) (by rw [hg' _ (by decide)]) rd wr hf
      fun s' hg'' rd' wr' m' => ?_
    rw [show n - (j + 1) + 1 = n - j by omega]
    refine ih (by omega) s' (fun r h => by rw [hg'' r h, hg' r h]) (rd'.trans rd) (wr'.trans wr) ?_
    rw [m', m, show n - j = n - (j + 1) + 1 by omega, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, ← writeBytes_append _ _ _ _ (by rw [hflat, hg]; omega), hflat]

/-- A word of the hash value at `ebx`, while only the digest at `eax` is written. -/
theorem out_read {s₀ : State} {m : Mem} {n o : Nat}
    (hf : Frame [⟨(s₀.gpr .eax).setWidth 64, n⟩] s₀.mem m)
    (hd : Region.Disjoint ⟨(s₀.gpr .ebx).setWidth 64, n⟩ ⟨(s₀.gpr .eax).setWidth 64, n⟩)
    (h : o + 4 ≤ n) (hn : n ≤ 64) :
    m.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 o) 32 =
      s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 o) 32 :=
  hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hd.sub_left (sub_offset h (by omega))) (by decide)

/-- `[x + o, x + o + 4)` lies in a region of `n` bytes at `x`. -/
theorem out_in {rs : List Region} {a : Addr} {n o : Nat} (h : InRegions rs a n) (ho : o + 4 ≤ n) (hn : n ≤ 64) :
    InRegions rs (a + BitVec.ofNat 64 o) 4 := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 o - R.base).toNat ≤ (a - R.base).toNat + o := by
    rw [show a + BitVec.ofNat 64 o - R.base = (a - R.base) + BitVec.ofNat 64 o by
      rw [VG.Offset.add_sub_comm],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_le _ _
  omega

/-- `out32 n be` writes the `n` 32-bit words at `ebx` to `eax`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (hbx : (s₀.gpr .ebx).toNat + 4 * n ≤ 2 ^ 32) (hax : (s₀.gpr .eax).toNat + 4 * n ≤ 2 ^ 32)
    (hin : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .ebx).setWidth 64) (4 * n))
    (hout : InRegions s₀.wr ((s₀.gpr .eax).setWidth 64) (4 * n))
    (hd : Region.Disjoint ⟨(s₀.gpr .ebx).setWidth 64, 4 * n⟩ ⟨(s₀.gpr .eax).setWidth 64, 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64)
        ((List.range n).flatMap fun k =>
          bytes32 be (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32)) := by
  have h := out_words n 4 hn (fun k => bytes32 be (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 +
      BitVec.ofNat 64 (4 * k)) 32)) (fun _ => bytes32_length be _)
    (fun k => [.mov .ecx (.mem (at_ .ebx (4 * k)))] ++ (if be then [.bswap .ecx] else []) ++
      [.store (at_ .eax (4 * k)) .ecx]) (s₀ := s₀) ?_ n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx' hax' hrd hwr hf kk
  have hoff : 4 * k + 4 ≤ 4 * n := by omega
  have hread := out_read hf hd hoff hn
  refine wp_movm (a := (s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k))
    (by rw [ea_at, hbx', addr_eq (by omega)])
    (by rw [hrd, hwr]; exact out_in hin hoff hn) fun s₁ u₁ => ?_
  have ea₁ : ∀ t : State, t.gpr .eax = s₀.gpr .eax →
      t.ea (at_ .eax (4 * k)) = (s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (4 * k) := fun t ht => by
    rw [ea_at, ht, addr_eq (by omega)]
  cases be
  · refine wp_store (ea₁ s₁ (by rw [u₁.other _ (by decide), hax']))
      (by rw [u₁.wr, hwr]; exact out_in hout hoff hn) fun s₂ u₂ => ?_
    refine kk s₂ (fun r h => by rw [u₂.gpr, u₁.other r h]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_
    rw [u₂.mem, u₁.mem, u₁.gpr, hread, ← writeW32 _ _ false]; rfl
  · refine wp_bswap fun s₂ u₂ => wp_store (ea₁ s₂ (by rw [u₂.other _ (by decide),
      u₁.other _ (by decide), hax'])) (by rw [u₂.wr, u₁.wr, hwr]; exact out_in hout hoff hn)
      fun s₃ u₃ => ?_
    refine kk s₃ (fun r h => by rw [u₃.gpr, u₂.other r h, u₁.other r h]) (by rw [u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr]) ?_
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hread, ← writeW32 _ _ true]; rfl

/-- `out64 n` writes the `n` 64-bit words at `ebx`, each stored little-endian (its low half
first), to `eax` big-endian: the high half, then the low half. -/
theorem out64_ok {n : Nat} (hn : 8 * n ≤ 64) {s₀ : State}
    (hbx : (s₀.gpr .ebx).toNat + 8 * n ≤ 2 ^ 32) (hax : (s₀.gpr .eax).toNat + 8 * n ≤ 2 ^ 32)
    (hin : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .ebx).setWidth 64) (8 * n))
    (hout : InRegions s₀.wr ((s₀.gpr .eax).setWidth 64) (8 * n))
    (hd : Region.Disjoint ⟨(s₀.gpr .ebx).setWidth 64, 8 * n⟩ ⟨(s₀.gpr .eax).setWidth 64, 8 * n⟩) :
    WP isa (.block (out64 n)) s₀ fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64)
        ((List.range n).flatMap fun k =>
          bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) ++
          bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32)) := by
  have h := out_words n 8 hn (fun k =>
      bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) ++
      bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32))
    (fun _ => by simp [bytes32_length])
    (fun k => [.mov .ecx (.mem (at_ .ebx (8 * k + 4))), .bswap .ecx, .store (at_ .eax (8 * k)) .ecx,
      .mov .ecx (.mem (at_ .ebx (8 * k))), .bswap .ecx, .store (at_ .eax (8 * k + 4)) .ecx])
    (s₀ := s₀) ?_ n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx' hax' hrd hwr hf kk
  have h₀ : 8 * k + 4 ≤ 8 * n := by omega
  have h₄ : 8 * k + 4 + 4 ≤ 8 * n := by omega
  have ea : ∀ (t : State) (r : Reg) (o : Nat), t.gpr r = s₀.gpr r → (s₀.gpr r).toNat + o < 2 ^ 32 →
      t.ea (at_ r o) = (s₀.gpr r).setWidth 64 + BitVec.ofNat 64 o := fun t r o ht ho => by
    rw [ea_at, ht, addr_eq ho]
  simp only [List.cons_append, List.nil_append]
  refine wp_movm (ea s .ebx _ hbx' (by omega)) (by rw [hrd, hwr]; exact out_in hin h₄ hn) fun s₁ u₁ =>
    wp_bswap fun s₂ u₂ => ?_
  refine wp_store (ea s₂ .eax _ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hax']) (by omega))
    (by rw [u₂.wr, u₁.wr, hwr]; exact out_in hout h₀ hn) fun s₃ u₃ => ?_
  have hf₃ : Frame [⟨(s₀.gpr .eax).setWidth 64, 8 * n⟩] s₀.mem s₃.mem := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_offset h₀ (by omega))
  refine wp_movm (ea s₃ .ebx _ (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hbx'])
    (by omega)) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrd, hwr]; exact out_in hin h₀ hn)
    fun s₄ u₄ => wp_bswap fun s₅ u₅ => ?_
  refine wp_store (ea s₅ .eax _ (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hax']) (by omega))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]; exact out_in hout h₄ hn) fun s₆ u₆ => ?_
  refine kk s₆ (fun r h => by rw [u₆.gpr, u₅.other r h, u₄.other r h, u₃.gpr, u₂.other r h, u₁.other r h])
    (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) ?_
  have v₂ : s₂.gpr .ecx = bswap (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) := by
    rw [u₂.gpr, u₁.gpr, out_read hf hd h₄ hn]
  have v₅ : s₅.gpr .ecx = bswap (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32) := by
    rw [u₅.gpr, u₄.gpr, out_read hf₃ hd (by omega) hn]
  have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => writeW32 m a true x
  simp only [ite_true] at w
  rw [u₆.mem, u₅.mem, u₄.mem, v₅, u₃.mem, v₂, u₂.mem, u₁.mem, w, w,
    ← writeBytes_append _ _ _ _ (by simp [bytes32_length]), bytes32_length, add_ofNat]

end VG.Proof.MdStream.X86
