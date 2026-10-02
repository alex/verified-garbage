import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode

/-!
# ML-KEM on x86-64: `vg_mlkem_decode_decompress`

The loop is proven once for every width (`DD.loop_ok`), and the function by
its three cases.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace DD

section
variable (s₀ : State)
abbrev bP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rcx
/-- The input, for the width `d`. -/
abbrev B (d : Nat) : List Byte := bytesAt s₀.mem (bP s₀) (32 * d)
end

/-- A value of a segment of the bytes of group `i` (of `c` values in `b`
bytes): bits `s + p …` of the number of its `l` bytes from `o` are value `e`
of the group, decompressed. -/
theorem seg {d c b : Nat} (hd1 : 1 ≤ d) (hd11 : d ≤ 11) (hdc : d * c = 8 * b) (B : List Byte)
    {i o l s p e : Nat} (hbi : b * i + o + l ≤ B.length) (hk : c * i + e < 256) (hp : s + p + d ≤ 8 * l)
    (he : d * e = 8 * o + s + p) :
    (3329 * (digits 8 ((List.range l).map fun t => (B.getD (b * i + (o + t)) 0).toNat) / 2 ^ s / 2 ^ p % 2 ^ d) +
      2 ^ (d - 1)) / 2 ^ d = ((decodeDecompress d B)[c * i + e]!).val := by
  have hk' : c * i + e < Spec.MlKem.n := by rw [n_eq]; exact hk
  have hy : digits 8 (B.map (·.toNat)) / 2 ^ (d * (c * i + e)) % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
  rw [decodeDecompress_get d B hk', byteDecode_getElem d B hk', ifp (show d < 12 by omega), Nat.mod_mod,
    (decompress_val_of_le (by omega) hd11 hy).1, q_eq]
  have e1 : (List.range l).map (fun t => (B.getD (b * i + (o + t)) 0).toNat) =
      ((B.map (·.toNat)).drop (b * i + o)).take l := by
    rw [← List.map_drop, ← List.map_take, bytes_map_take_drop B hbi]
    refine List.map_congr_left fun t _ => ?_
    rw [Nat.add_assoc]
  have ex : 8 * (b * i + o) + s + p = d * (c * i + e) := by
    rw [Nat.mul_add, Nat.mul_add d, ← Nat.mul_assoc, ← Nat.mul_assoc, hdc]; omega
  rw [e1, chunk_eq (map_bytes_lt B) (b * i + o) l s p d hp, ex]

/-- The group's facts that its code needs. -/
structure GrpIn (c b : Nat) (B : List Byte) (i : Nat) (s : State) : Prop where
  rd : ∀ k < b, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1
  bytes : ∀ k < b, s.mem (s.gpr .rdi + BitVec.ofNat 64 k) = B.getD (b * i + k) 0
  wr : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4
  r9 : (s.gpr .r9).toNat = 3329
  dj : Region.Disjoint ⟨s.gpr .rdi, b⟩ ⟨s.gpr .rsi, 4 * c⟩

/-- What a group's code does: its `c` coefficients, within its `4c` bytes. -/
abbrev GrpOut (d c : Nat) (B : List Byte) (i : Nat) (s s' : State) : Prop :=
  (∀ j < c, (s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32).toNat =
      ((decodeDecompress d B)[c * i + j]!).val) ∧
    Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧ Keep [.rax, .rdx, .r10] s s'

/-- A group whose code loads its `b` bytes and decompresses its `c` values
(`d · c = 8 · b`). -/
theorem grp_ok {d c b : Nat} (hd1 : 1 ≤ d) (hd11 : d ≤ 11) (hdc : d * c = 8 * b) (hb : b ≤ 7) (hc : c ≤ 8)
    (B : List Byte) {i : Nat} (hbi : b * i + b ≤ B.length) (hci : c * i + c ≤ 256) {s : State}
    (h : GrpIn c b B i s) :
    WP isa (.block (ddLd 0 b ++ ddVals d 0 c)) s (GrpOut d c B i s) := by
  rw [WP.block_append_iff]
  refine WP.mono (ddLd_ok (o := 0) hb s (fun k hk => by rw [Nat.zero_add]; exact h.rd k hk))
    fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ddVals_ok (o := 0) (c := c) (d := d) hd1 hd11 hc s₁ (fun j hj => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr j hj)) fun s₂ ⟨w₂, f₂, k₂⟩ => ?_
  have si₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.gpr (by decide)
  refine ⟨fun j hj => ?_, ?_, (k₁.trans k₂).mono (by decide)⟩
  · have := w₂ j hj
    rw [si₁, Nat.zero_add] at this
    rw [this, ddW_toNat hd1 hd11 _ (by rw [k₁.gpr (by decide)]; exact h.r9), shr_toNat, r₁]
    have e : (List.range b).map (fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (0 + k))).toNat) =
        (List.range b).map fun t => (B.getD (b * i + (0 + t)) 0).toNat :=
      List.map_congr_left fun t ht => by simp only [Nat.zero_add, h.bytes t (List.mem_range.mp ht)]
    have hj' : d * j + d ≤ 8 * b := by
      rw [← hdc, show d * j + d = d * (j + 1) by rw [Nat.mul_succ]]; exact Nat.mul_le_mul_left _ hj
    rw [e, ← seg (o := 0) (l := b) (s := 0) (p := d * j) hd1 hd11 hdc B (by omega) (by omega) (by omega)
      (by omega), Nat.pow_zero, Nat.div_one]
  · rw [si₁, Nat.mul_zero, add_ofNat_zero, m₁] at f₂; exact f₂

/-- After `i` groups. -/
structure Inv (s₀ : State) (d c b : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 (b * i)
  rsi : s.gpr .rsi = fP s₀ + BitVec.ofNat 64 (4 * c * i)
  r9 : (s.gpr .r9).toNat = 3329
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (fP s₀)] s₀.mem s.mem
  done : ∀ k < c * i, (coeffAt s.mem (fP s₀) k).toNat = ((decodeDecompress d (B s₀ d))[k]!).val

theorem tail_ok (c b : Nat) (hc : 4 * c < 2 ^ 31) (hb : b < 2 ^ 31) (s : State) :
    WP isa (.block (ddTail c b)) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 b ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddTail
  xrun [sx_ofNat hc, sx_ofNat hb]

theorem lenEq {ws : List Nat} {s₀ : State} (hp : (decodeDecompressWK ws).pre s₀) {d : Nat}
    (hdd : dArg s₀ .rdx = d) : (s₀.gpr .rsi).toNat = 32 * d := by rw [hp.2.2.2.2.2.2, hdd]

section
variable {ws : List Nat} {s₀ : State} (hp : (decodeDecompressWK ws).pre s₀) {d c b : Nat} (hd11 : d ≤ 11)
  (hc0 : 0 < c) (hc : c ≤ 8) (hb : b ≤ 11) (hbN : b * (256 / c) = 32 * d) (hcN : c * (256 / c) = 256)
  (hdd : dArg s₀ .rdx = d)
include hp hd11 hc0 hc hb hbN hcN hdd

omit hc0 hc hb hbN hcN in
theorem byte {m : Mem} (hf : Frame [pR (fP s₀)] s₀.mem m) {k : Nat} (hk : k < 32 * d) :
    m (bP s₀ + BitVec.ofNat 64 k) = (B s₀ d).getD k 0 := by
  rw [bytesAt_getD _ _ hk]
  have h1 := hp.2.2.1; rw [lenEq hp hdd] at h1
  exact bytes_frame hf (by simpa using h1) (by omega) k hk

theorem step {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, GrpIn c b (B s₀ d) i s → WP isa (.block grp) s (GrpOut d c (B s₀ d) i s))
    {i : Nat} (hi : i < 256 / c) {s : State} (hI : Inv s₀ d c b i s) :
    WP isa (.block (grp ++ ddTail c b)) s fun s' => Inv s₀ d c b (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hci : c * i + c ≤ 256 := by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega
  have hbi : b * i + b ≤ 32 * d := by
    have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega
  have hrd : s.rd ++ s.wr = [⟨bP s₀, 32 * d⟩, pR (fP s₀)] := by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, lenEq hp hdd]; rfl
  have hwr : s.wr = [pR (fP s₀)] := by rw [hI.wr, hp.2.1]
  have hdj : Region.Disjoint ⟨bP s₀, 32 * d⟩ (pR (fP s₀)) := by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; exact this
  have hsub : Region.Sub ⟨s.gpr .rsi, 4 * c⟩ (pR (fP s₀)) := by
    rw [hI.rsi]; exact sub_offset' (by rw [Nat.mul_assoc, ← Nat.mul_add]; omega) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (hgrp i hi s ⟨fun k hk => ?_, fun k hk => ?_, fun j hj => ?_, hI.r9, ?_⟩) fun s₁ ⟨w₁, f₁, k₁⟩ => ?_
  · rw [hrd, hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨⟨bP s₀, 32 * d⟩, by simp, contains_offset' (by omega) (by omega)⟩
  · rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add, byte hp hd11 hdd hI.frame (by omega)]
  · rw [hwr, hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_singleton_self _, contains_offset' (by rw [Nat.mul_assoc]; omega) (by decide)⟩
  · rw [hI.rdi]
    exact (hdj.sub_left (sub_offset' (by omega) (by omega))).sub_right hsub
  refine WP.mono (tail_ok c b (by omega) (by omega) s₁) fun s₂ ⟨⟨di₂, si₂, cx₂, z₂, m₂⟩, k₂⟩ => ⟨?_, ?_, ?_⟩
  rotate_left
  · rw [cx₂, k₁.gpr (by decide)]
  · rw [z₂, k₁.gpr (by decide)]
  have hf₂ : Frame [pR (fP s₀)] s.mem s₂.mem := by
    rw [m₂]; exact f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hI.frame.trans hf₂, fun k hk => ?_⟩
  · rw [di₂, k₁.gpr (by decide), hI.rdi]; exact ptr_step _ i b
  · rw [si₂, k₁.gpr (by decide), hI.rsi]; exact ptr_step _ i (4 * c)
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.r9]
  · rw [k₂.2.1, k₁.2.1, hI.rd]
  · rw [k₂.2.2, k₁.2.2, hI.wr]
  by_cases hk' : k < c * i
  · -- Written before.
    rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
    refine congrArg BitVec.toNat (Mem.readW_congr fun t ht => ?_)
    rw [m₂]
    refine (f₁.bytes (R := ⟨coeffAddr (fP s₀) k, 4⟩) ?_ (show 4 ≤ 2 ^ 64 by decide)
      (show t < 4 by omega))
    simp only [List.mem_singleton, forall_eq]
    rw [hI.rsi]
    exact off_disj (by rw [Nat.mul_assoc]; omega) (by rw [Nat.mul_assoc]; omega)
  · -- This group.
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < c ∧ k = c * i + j := ⟨k - c * i, by rw [Nat.mul_succ] at hk; omega, by omega⟩
    rw [coeffAt_eq, ← show s.gpr .rsi + BitVec.ofNat 64 (4 * j) = coeffAddr (fP s₀) (c * i + j) by
      rw [hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc], m₂]
    exact w₁ j hj

/-- The loop over the groups, each `grp`, from a state with `b` in `rdi` and
`f` in `rsi`. -/
theorem loop_ok {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, GrpIn c b (B s₀ d) i s → WP isa (.block grp) s (GrpOut d c (B s₀ d) i s))
    {s : State} (hdi : s.gpr .rdi = bP s₀) (hsi : s.gpr .rsi = fP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ddLoopW (256 / c) (grp ++ ddTail c b)) s fun s' =>
      PolyIs s'.mem (fP s₀) (decodeDecompress d (B s₀ d)) ∧ Frame [pR (fP s₀)] s₀.mem s'.mem := by
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun s' => s'.gpr .r9 = 3329 ∧ s'.mem = s.mem)
    (by xrun) (by decide)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  have hN : 0 < 256 / c ∧ 256 / c ≤ 256 := ⟨Nat.div_pos (by omega) hc0, Nat.div_le_self _ _⟩
  refine WP.mono (wp_counted (N := 256 / c) (v := BitVec.ofNat 32 (256 / c))
    (by rw [BitVec.toNat_ofNat]; omega) (by omega) (Inv s₀ d c b)
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega)⟩)
    fun i hi s hI => step hp hd11 hc0 hc hb hbN hcN hdd hgrp hi hI) fun s' hI =>
      ⟨polyIs_of_toNat fun k hk => hI.done k (by rw [hcN]; exact hk), hI.frame⟩
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hsi]; simp
  · rw [k₂.gpr (by decide), h9]; rfl
  · rw [k₂.2.1, k₁.2.1, hrd]
  · rw [k₂.2.2, k₁.2.2, hwr]
  · rw [m₂, m₁, hm]; exact Frame.refl _ _

end

end DD

theorem ddPrologue_ok (s₀ : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 1)]) s₀ fun s =>
      (s.gpr .rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.gpr .rdx)) ∧ s.gpr .rsi = s₀.gpr .rcx ∧
        s.zf = some (BitVec.setWidth 32 (s₀.gpr .rdx) - 1 == 0) ∧ s.mem = s₀.mem) ∧ Keep [.rdx, .rsi] s₀ s := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem dd_wp {s₀ : State} (hp : decodeDecompressK.pre s₀) :
    WP isa Impl.MlKem.X86_64.decodeDecompress s₀ fun s' =>
      PolyIs s'.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)) ∧
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [DD.lenEq hp rfl]
  unfold Impl.MlKem.X86_64.decodeDecompress
  refine WP.seq (WP.mono (ddPrologue_ok s₀) fun s₁ ⟨⟨dx₁, si₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have go : ∀ {d c b : Nat}, d ∈ compressWidths → d * c = 8 * b → b ≤ 5 → 0 < c → c ≤ 8 →
      b * (256 / c) = 32 * d → c * (256 / c) = 256 → dArg s₀ .rdx = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsi = s₀.gpr .rcx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (ddLoop d c b) s fun s' =>
        PolyIs s'.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi)
          (32 * dArg s₀ .rdx))) ∧ Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
    intro d c b hd hdc hb hc0 hc hbN hcN hdd s h1 h2 h3 h4 h5
    have hd11 : 1 ≤ d ∧ d ≤ 11 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    rw [hdd]
    exact DD.loop_ok hp hd11.2 hc0 hc (by omega) hbN hcN hdd
      (fun i hi s hs => DD.grp_ok hd11.1 hd11.2 hdc (by omega) hc _
        (by
          have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this
          rw [bytesAt_length]; omega)
        (by have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega) hs)
      h1 h2 h3 h4 h5
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact go (d := 1) (c := 8) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp only [dArg, h]; rfl) s₁ di₁ si₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (cmp32_ok .rdx 4 s₁) fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    rw [dx₁, BitVec.setWidth_32_64_32] at z₂
    refine WP.ite (M := isa) _ (show isa.eval .e s₂ = _ from z₂) (fun h' => ?_) (fun h' => ?_)
    · rw [sub_beq_zero32, decide_eq_true_eq] at h'
      exact go (d := 4) (c := 2) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by simp only [dArg, h']; rfl) s₂ (by rw [k₂.gpr (by decide), di₁])
        (by rw [k₂.gpr (by decide), si₁]) (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])
    · rw [sub_beq_zero32, decide_eq_false_iff_not] at h'
      have h10 : dArg s₀ .rdx = 10 := by
        rcases mem_compressWidths hd with e | e | e
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h'
        · exact e
      exact go (d := 10) (c := 4) (b := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) h10 s₂ (by rw [k₂.gpr (by decide), di₁])
        (by rw [k₂.gpr (by decide), si₁]) (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])

theorem decodeDecompress_correct (s : State) (hs : decodeDecompressK.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.decodeDecompress s t s' ∧ abiPreserved s s' ∧
      decodeDecompressK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.decodeDecompress)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .r10] (dd_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem decodeDecompress_ct :
    ConstantTime isa decodeDecompressK.pre decodeDecompressK.pub Impl.MlKem.X86_64.decodeDecompress :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def decodeDecompressSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 1 | .rcx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decodeDecompress_verified :
    Verified X86_64.target Impl.MlKem.X86_64.decodeDecompress (Spec.MlKem.decodeDecompressContract X86_64.abi) :=
  Verified.of_correct decodeDecompress_correct decodeDecompress_ct (by
    mlkem_implies [Spec.MlKem.decodeDecompressContract, Spec.MlKem.decodeDecompressSig, decodeDecompressK,
      X86_64.abi, X86_64.argRegs] [decodeDecompressSat] using decodeDecompressSat)

end VG.Proof.MlKem.X86_64
