import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decode_decompress`

A segment of a group's bytes holds values of the decoding (`dd_seg`); a
group's segments write its 8 coefficients (`dgrp5_ok`, `dgrp11_ok`); the loop
is proven once for both widths, from what its group does (`DD4.loop_ok`), and
the function by its two cases.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A value of a segment of the bytes of group `i`: bits `s + p …` of the
number of its `c` bytes from `o` are value `e` of the group, decompressed. -/
theorem dd_seg {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (B : List Byte) (hB : B.length = 32 * d)
    {i o c s p e : Nat} (hi : i < 32) (hoc : o + c ≤ d) (hp : s + p + d ≤ 8 * c) (he : d * e = 8 * o + s + p)
    (he8 : e < 8) :
    (3329 * (digits 8 ((List.range c).map fun t => (B.getD (d * i + (o + t)) 0).toNat) / 2 ^ s / 2 ^ p % 2 ^ d) +
      2 ^ (d - 1)) / 2 ^ d = ((decodeDecompress d B)[8 * i + e]!).val := by
  have hd12 : d < 12 := by rcases widths1024 hd with rfl | rfl <;> decide
  have hk : 8 * i + e < n := by rw [n_eq]; omega
  have hy : digits 8 (B.map (·.toNat)) / 2 ^ (d * (8 * i + e)) % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
  rw [decodeDecompress_get d B hk, byteDecode_getElem d B hk, ifp hd12, Nat.mod_mod, (decompress1024_val hd hy).1,
    q_eq]
  have hdi : d * i + o + c ≤ B.length := by
    rw [hB]
    have := Nat.mul_le_mul_left d (show i + 1 ≤ 32 by omega); rw [Nat.mul_succ] at this; rw [Nat.mul_comm 32 d]; omega
  have e1 : (List.range c).map (fun t => (B.getD (d * i + (o + t)) 0).toNat) =
      ((B.map (·.toNat)).drop (d * i + o)).take c := by
    rw [← List.map_drop, ← List.map_take, bytes_map_take_drop B hdi]
    refine List.map_congr_left fun t _ => ?_
    rw [Nat.add_assoc]
  have ex : 8 * (d * i + o) + s + p = d * (8 * i + e) := by
    rw [Nat.mul_add, Nat.mul_add d, Nat.mul_left_comm]; omega
  rw [e1, chunk_eq (map_bytes_lt B) (d * i + o) c s p d hp, ex]

/-- The group's facts that its code needs. -/
structure DGrpIn (d : Nat) (B : List Byte) (i : Nat) (s : State) : Prop where
  rd : ∀ k < d, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1
  b : ∀ k < d, s.mem (s.gpr .rdi + BitVec.ofNat 64 k) = B.getD (d * i + k) 0
  wr : ∀ j < 8, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4
  r9 : (s.gpr .r9).toNat = 3329
  dj : Region.Disjoint ⟨s.gpr .rdi, d⟩ ⟨s.gpr .rsi, 32⟩

/-- What a group's code does: its 8 coefficients, within its 32 bytes. -/
abbrev DGrpOut (d : Nat) (B : List Byte) (i : Nat) (s s' : State) : Prop :=
  (∀ j < 8, (s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32).toNat = ((decodeDecompress d B)[8 * i + j]!).val) ∧
    Frame [⟨s.gpr .rsi, 32⟩] s.mem s'.mem ∧ Keep [.rax, .rdx, .r10] s s'

theorem dgrp5_ok (B : List Byte) (hB : B.length = 32 * 5) {i : Nat} (hi : i < 32) {s : State} (h : DGrpIn 5 B i s) :
    WP isa (.block (ddLd 0 5 ++ ddVals 5 0 8)) s (DGrpOut 5 B i s) := by
  rw [WP.block_append_iff]
  refine WP.mono (ddLd_ok (o := 0) (b := 5) (by decide) s (fun k hk => by rw [Nat.zero_add]; exact h.rd k hk))
    fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ddVals_ok (o := 0) (c := 8) (d := 5) (by decide) (by decide) (by decide) s₁ (fun j hj => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr j hj)) fun s₂ ⟨w₂, f₂, k₂⟩ => ?_
  have si₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.gpr (by decide)
  refine ⟨fun j hj => ?_, ?_, (k₁.trans k₂).mono (by decide)⟩
  · have := w₂ j hj
    rw [si₁, Nat.zero_add] at this
    rw [this, ddW_toNat' (by decide) (by decide) _ (by rw [k₁.gpr (by decide)]; exact h.r9), shr_toNat, r₁]
    have e : (List.range 5).map (fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (0 + k))).toNat) =
        (List.range 5).map fun t => (B.getD (5 * i + (0 + t)) 0).toNat :=
      List.map_congr_left fun t ht => by simp only [Nat.zero_add, h.b t (List.mem_range.mp ht)]
    rw [e, ← dd_seg (o := 0) (c := 5) (s := 0) (p := 5 * j) (by decide) B hB hi (by decide) (by omega) (by omega) hj,
      Nat.pow_zero, Nat.div_one]
  · rw [si₁, Nat.mul_zero, add_ofNat_zero, m₁] at f₂; exact f₂

theorem dgrp11_ok (B : List Byte) (hB : B.length = 32 * 11) {i : Nat} (hi : i < 32) {s : State}
    (h : DGrpIn 11 B i s) :
    WP isa (.block (ddLd 0 6 ++ ddVals 11 0 4 ++ ddLd 5 6 ++ ([.shift .shr .r10 4] : List Instr) ++ ddVals 11 4 4)) s
      (DGrpOut 11 B i s) := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- Bytes 0–5, and values 0–3.
  refine WP.mono (ddLd_ok (o := 0) (b := 6) (by decide) s (fun k hk => by rw [Nat.zero_add]; exact h.rd k (by omega)))
    fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ddVals_ok (o := 0) (c := 4) (d := 11) (by decide) (by decide) (by decide) s₁ (fun j hj => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr j (by omega))) fun s₂ ⟨w₂, f₂, k₂⟩ => ?_
  have si₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.gpr (by decide)
  rw [si₁, Nat.mul_zero, add_ofNat_zero, m₁] at f₂
  -- Bytes 5–10, shifted, and values 4–7.
  have di₂ : s₂.gpr .rdi = s.gpr .rdi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have si₂ : s₂.gpr .rsi = s.gpr .rsi := by rw [k₂.gpr (by decide), si₁]
  have b₂ : ∀ k < 11, s₂.mem (s.gpr .rdi + BitVec.ofNat 64 k) = s.mem (s.gpr .rdi + BitVec.ofNat 64 k) :=
    fun k hk => f₂.bytes (R := ⟨s.gpr .rdi, 11⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h.dj.sub_right (Region.sub_prefix (by decide))) (show 11 ≤ 2 ^ 64 by decide) hk
  refine WP.mono (ddLd_ok (o := 5) (b := 6) (by decide) s₂ (fun k hk => by
      rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2, di₂]; exact h.rd _ (by omega))) fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  refine WP.mono (shr10_ok 4 (by decide) (by decide) s₃) fun s₄ ⟨⟨r₄, m₄⟩, k₄⟩ => ?_
  have si₄ : s₄.gpr .rsi = s.gpr .rsi := by rw [k₄.gpr (by decide), k₃.gpr (by decide), si₂]
  refine WP.mono (ddVals_ok (o := 4) (c := 4) (d := 11) (by decide) (by decide) (by decide) s₄ (fun j hj => by
      rw [k₄.2.2, k₃.2.2, k₂.2.2, k₁.2.2, si₄]; exact h.wr _ (by omega))) fun s₅ ⟨w₅, f₅, k₅⟩ => ?_
  rw [si₄, m₄, m₃] at f₅
  have r9₄ : (s₄.gpr .r9).toNat = 3329 := by
    rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact h.r9
  have r9₁ : (s₁.gpr .r9).toNat = 3329 := by rw [k₁.gpr (by decide)]; exact h.r9
  refine ⟨fun j hj => ?_, ?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · by_cases hj4 : j < 4
    · -- Written by the first segment, kept by the second.
      have hk : s₅.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 =
          s₂.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 :=
        f₅.readW (r := ⟨s.gpr .rsi + BitVec.ofNat 64 (4 * j), 4⟩) (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact off_disj (by omega) (by decide)) (by decide)
      have := w₂ j hj4
      rw [si₁, Nat.zero_add] at this
      rw [hk, this, ddW_toNat' (by decide) (by decide) _ r9₁, shr_toNat, r₁]
      have e : (List.range 6).map (fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (0 + k))).toNat) =
          (List.range 6).map fun t => (B.getD (11 * i + (0 + t)) 0).toNat :=
        List.map_congr_left fun t ht => by
          simp only [Nat.zero_add, h.b t (by have := List.mem_range.mp ht; omega)]
      rw [e, ← dd_seg (o := 0) (c := 6) (s := 0) (p := 11 * j) (by decide) B hB hi (by decide) (by omega) (by omega) hj,
        Nat.pow_zero, Nat.div_one]
    · have := w₅ (j - 4) (by omega)
      rw [si₄, show 4 + (j - 4) = j by omega] at this
      rw [this, ddW_toNat' (by decide) (by decide) _ r9₄, shr_toNat, r₄, shr_toNat, r₃, di₂]
      have e : (List.range 6).map (fun k => (s₂.mem (s.gpr .rdi + BitVec.ofNat 64 (5 + k))).toNat) =
          (List.range 6).map fun t => (B.getD (11 * i + (5 + t)) 0).toNat :=
        List.map_congr_left fun t ht => by
          have := List.mem_range.mp ht
          rw [b₂ _ (by omega), h.b _ (by omega)]
      rw [e, ← dd_seg (o := 5) (c := 6) (s := 4) (p := 11 * (j - 4)) (by decide) B hB hi (by decide) (by omega)
        (by omega) hj]
  · refine (f₂.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, sub_offset' (by decide) (by decide)⟩

namespace DD4

section
variable (s₀ : State)
abbrev bP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rcx
/-- The input, for the width `d`. -/
abbrev B (d : Nat) : List Byte := bytesAt s₀.mem (bP s₀) (32 * d)
end

/-- After `i` groups. -/
structure Inv (s₀ : State) (d : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 (d * i)
  rsi : s.gpr .rsi = fP s₀ + BitVec.ofNat 64 (32 * i)
  r9 : (s.gpr .r9).toNat = 3329
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (fP s₀)] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem (fP s₀) k).toNat = ((decodeDecompress d (B s₀ d))[k]!).val

theorem tail_ok (b : Nat) (hb : b < 2 ^ 31) (s : State) :
    WP isa (.block (ddTail b)) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 b ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 32 ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddTail
  xrun [sx_ofNat hb]
  rfl

theorem lenEq {s₀ : State} (hp : decodeDecompress1024K.pre s₀) {d : Nat} (hdd : dArg s₀ .rdx = d) :
    (s₀.gpr .rsi).toNat = 32 * d := by rw [hp.2.2.2.2.2.2, hdd]

section
variable {s₀ : State} (hp : decodeDecompress1024K.pre s₀) {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths)
  (hdd : dArg s₀ .rdx = d)
include hp hd hdd

theorem byte {m : Mem} (hf : Frame [pR (fP s₀)] s₀.mem m) {k : Nat} (hk : k < 32 * d) :
    m (bP s₀ + BitVec.ofNat 64 k) = (B s₀ d).getD k 0 := by
  rw [bytesAt_getD _ _ hk]
  have h1 := hp.2.2.1; rw [lenEq hp hdd] at h1
  have h2 := (CE4.hd11 hd).2
  exact bytes_frame hf (by simpa using h1) (by omega) k hk

theorem step {grp : List Instr}
    (hgrp : ∀ i < 32, ∀ s, DGrpIn d (B s₀ d) i s → WP isa (.block grp) s (DGrpOut d (B s₀ d) i s))
    {i : Nat} (hi : i < 32) {s : State} (hI : Inv s₀ d i s) :
    WP isa (.block (grp ++ ddTail d)) s fun s' => Inv s₀ d (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hd1, hd11⟩ := CE4.hd11 hd
  have hbi : d * i + d ≤ 32 * d := by
    have := Nat.mul_le_mul_left d (show i + 1 ≤ 32 by omega); rw [Nat.mul_succ] at this; rw [Nat.mul_comm 32 d]; omega
  have hrd : s.rd ++ s.wr = [⟨bP s₀, 32 * d⟩, pR (fP s₀)] := by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, lenEq hp hdd]; rfl
  have hwr : s.wr = [pR (fP s₀)] := by rw [hI.wr, hp.2.1]
  have hdj : Region.Disjoint ⟨bP s₀, 32 * d⟩ (pR (fP s₀)) := by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; exact this
  have hsub : Region.Sub ⟨s.gpr .rsi, 32⟩ (pR (fP s₀)) := by
    rw [hI.rsi]; exact sub_offset' (by omega) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (hgrp i hi s ⟨fun k hk => ?_, fun k hk => ?_, fun j hj => ?_, hI.r9, ?_⟩) fun s₁ ⟨w₁, f₁, k₁⟩ => ?_
  · rw [hrd, hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨⟨bP s₀, 32 * d⟩, by simp, contains_offset' (by omega) (by omega)⟩
  · rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add, byte hp hd hdd hI.frame (by omega)]
  · rw [hwr, hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_singleton_self _, contains_offset' (by omega) (by decide)⟩
  · rw [hI.rdi]
    exact (hdj.sub_left (sub_offset' (by omega) (by omega))).sub_right hsub
  refine WP.mono (tail_ok d (by omega) s₁) fun s₂ ⟨⟨di₂, si₂, cx₂, z₂, m₂⟩, k₂⟩ => ⟨?_, ?_, ?_⟩
  rotate_left
  · rw [cx₂, k₁.gpr (by decide)]
  · rw [z₂, k₁.gpr (by decide)]
  have hf₂ : Frame [pR (fP s₀)] s.mem s₂.mem := by
    rw [m₂]; exact f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hI.frame.trans hf₂, fun k hk => ?_⟩
  · rw [di₂, k₁.gpr (by decide), hI.rdi]; exact ptr_step _ i d
  · rw [si₂, k₁.gpr (by decide), hI.rsi]; exact ptr_step _ i 32
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.r9]
  · rw [k₂.2.1, k₁.2.1, hI.rd]
  · rw [k₂.2.2, k₁.2.2, hI.wr]
  by_cases hk' : k < 8 * i
  · -- Written before.
    rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
    refine congrArg BitVec.toNat (Mem.readW_congr fun t ht => ?_)
    rw [m₂]
    refine (f₁.bytes (R := ⟨coeffAddr (fP s₀) k, 4⟩) ?_ (show 4 ≤ 2 ^ 64 by decide)
      (show t < 4 by omega))
    simp only [List.mem_singleton, forall_eq]
    rw [hI.rsi]
    exact off_disj (by omega) (by omega)
  · -- This group.
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < 8 ∧ k = 8 * i + j := ⟨k - 8 * i, by rw [Nat.mul_succ] at hk; omega, by omega⟩
    rw [coeffAt_eq, show coeffAddr (fP s₀) (8 * i + j) = s.gpr .rsi + BitVec.ofNat 64 (4 * j) by
      rw [hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * i + 4 * j = 4 * (8 * i + j) by omega], m₂]
    exact w₁ j hj

/-- The loop for the width `d`, from a state with `b` in `rdi` and `f` in `rsi`. -/
theorem loop_ok {grp : List Instr}
    (hgrp : ∀ i < 32, ∀ s, DGrpIn d (B s₀ d) i s → WP isa (.block grp) s (DGrpOut d (B s₀ d) i s))
    {s : State} (hdi : s.gpr .rdi = bP s₀) (hsi : s.gpr .rsi = fP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ddLoop (grp ++ ddTail d)) s fun s' => PolyIs s'.mem (fP s₀) (decodeDecompress d (B s₀ d)) ∧
      Frame [pR (fP s₀)] s₀.mem s'.mem := by
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun s' => s'.gpr .r9 = 3329 ∧ s'.mem = s.mem)
    (by xrun) (by decide)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_counted (N := 32) (v := 32) rfl (by decide) (Inv s₀ d)
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega)⟩)
    fun i hi s hI => step hp hd hdd hgrp hi hI) fun s' hI =>
      ⟨polyIs_of_toNat fun k hk => hI.done k (by rw [n_eq] at hk; omega), hI.frame⟩
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hsi]; simp
  · rw [k₂.gpr (by decide), h9]; rfl
  · rw [k₂.2.1, k₁.2.1, hrd]
  · rw [k₂.2.2, k₁.2.2, hwr]
  · rw [m₂, m₁, hm]; exact Frame.refl _ _

end

end DD4

theorem ddPrologue_ok (s₀ : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov .rsi (.reg .rcx), .alu32 .cmp .rdx (.imm 5)]) s₀ fun s =>
      (s.gpr .rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.gpr .rdx)) ∧ s.gpr .rsi = s₀.gpr .rcx ∧
        s.zf = some (BitVec.setWidth 32 (s₀.gpr .rdx) - 5 == 0) ∧ s.mem = s₀.mem) ∧ Keep [.rdx, .rsi] s₀ s := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem dd_wp {s₀ : State} (hp : decodeDecompress1024K.pre s₀) :
    WP isa decodeDecompress1024 s₀ fun s' =>
      PolyIs s'.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)) ∧
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [DD4.lenEq hp rfl]
  unfold decodeDecompress1024
  refine WP.seq (WP.mono (ddPrologue_ok s₀) fun s₁ ⟨⟨_, si₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h5 : dArg s₀ .rdx = 5 := by simp only [dArg, h]; rfl
    rw [h5]
    exact DD4.loop_ok hp (by rw [← h5]; exact hd) h5 (fun i hi s hs => dgrp5_ok _ (bytesAt_length _ _ _) hi hs)
      di₁ si₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    have h11 : dArg s₀ .rdx = 11 := by
      rcases widths1024 hd with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
      · exact e
    rw [h11]
    exact DD4.loop_ok hp (by rw [← h11]; exact hd) h11 (fun i hi s hs => dgrp11_ok _ (bytesAt_length _ _ _) hi hs)
      di₁ si₁ k₁.2.1 k₁.2.2 m₁

theorem decodeDecompress1024_correct (s : State) (hs : decodeDecompress1024K.pre s) :
    ∃ t s', Exec isa decodeDecompress1024 s t s' ∧ abiPreserved s s' ∧ decodeDecompress1024K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := decodeDecompress1024)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .r10] (dd_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem decodeDecompress1024_ct :
    ConstantTime isa decodeDecompress1024K.pre decodeDecompress1024K.pub decodeDecompress1024 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def decodeDecompress1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 160 | .rdx => 5 | .rcx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 160⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decodeDecompress1024_verified :
    Verified X86_64.target decodeDecompress1024 (Spec.MlKem1024.decodeDecompressContract X86_64.abi) :=
  Verified.of_correct decodeDecompress1024_correct decodeDecompress1024_ct (by
    mlkem_implies [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig,
      decodeDecompress1024K, X86_64.abi, X86_64.argRegs] [decodeDecompress1024Sat] using decodeDecompress1024Sat)

end VG.Proof.MlKem1024.X86_64
