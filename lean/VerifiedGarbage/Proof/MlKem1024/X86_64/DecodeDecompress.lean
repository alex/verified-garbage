import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decode_decompress`

A group of 5 bytes is decoded as ML-KEM-768's are (`DD.grp_ok`), one of 11
bytes in two segments (`dgrp11_ok`, from `DD.seg`); the loop is ML-KEM-768's
(`DD.loop_ok`, `Proof/MlKem/X86_64/DecodeDecompress.lean`), and the function
is proven by its two cases.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Impl.MlKem.X86_64 (ceAcc ceSt ceTail ceLoopW ddLd ddVals ddTail ddLoopW)
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A group of 11 bytes: values 0–4 (55 bits) are the low 6 bytes 0–5; values
4–7 (44 bits) shifted right by 4 are bytes 5–10. -/
theorem dgrp11_ok (B : List Byte) (hB : B.length = 32 * 11) {i : Nat} (hi : i < 32) {s : State}
    (h : DD.GrpIn 8 11 B i s) :
    WP isa (.block (ddLd 0 6 ++ ddVals 11 0 4 ++ ddLd 5 6 ++ ([.shift .shr .r10 4] : List Instr) ++ ddVals 11 4 4)) s
      (DD.GrpOut 11 8 B i s) := by
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
      rw [hk, this, ddW_toNat (by decide) (by decide) _ r9₁, shr_toNat, r₁]
      have e : (List.range 6).map (fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (0 + k))).toNat) =
          (List.range 6).map fun t => (B.getD (11 * i + (0 + t)) 0).toNat :=
        List.map_congr_left fun t ht => by
          simp only [Nat.zero_add, h.bytes t (by have := List.mem_range.mp ht; omega)]
      rw [e, ← DD.seg (o := 0) (l := 6) (s := 0) (p := 11 * j) (c := 8) (b := 11) (by decide) (by decide) (by decide) B
        (by omega) (by omega) (by omega) (by omega),
        Nat.pow_zero, Nat.div_one]
    · have := w₅ (j - 4) (by omega)
      rw [si₄, show 4 + (j - 4) = j by omega] at this
      rw [this, ddW_toNat (by decide) (by decide) _ r9₄, shr_toNat, r₄, shr_toNat, r₃, di₂]
      have e : (List.range 6).map (fun k => (s₂.mem (s.gpr .rdi + BitVec.ofNat 64 (5 + k))).toNat) =
          (List.range 6).map fun t => (B.getD (11 * i + (5 + t)) 0).toNat :=
        List.map_congr_left fun t ht => by
          have := List.mem_range.mp ht
          rw [b₂ _ (by omega), h.bytes _ (by omega)]
      rw [e, ← DD.seg (o := 5) (l := 6) (s := 4) (p := 11 * (j - 4)) (c := 8) (b := 11) (by decide) (by decide)
        (by decide) B (by omega) (by omega) (by omega) (by omega)]
  · refine (f₂.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, sub_offset' (by decide) (by decide)⟩

/-- The loop for the width `d`, from a state with `b` in `rdi` and `f` in `rsi`. -/
theorem ddLoop_ok {s₀ : State} (hp : decodeDecompress1024K.pre s₀) {d : Nat}
    (hd : d ∈ Spec.MlKem1024.compressWidths) (hdd : dArg s₀ .rdx = d) {grp : List Instr}
    (hgrp : ∀ i < 32, ∀ s, DD.GrpIn 8 d (DD.B s₀ d) i s → WP isa (.block grp) s (DD.GrpOut d 8 (DD.B s₀ d) i s))
    {s : State} (hdi : s.gpr .rdi = DD.bP s₀) (hsi : s.gpr .rsi = DD.fP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ddLoopW 32 (grp ++ ddTail 8 d)) s fun s' =>
      PolyIs s'.mem (DD.fP s₀) (decodeDecompress d (DD.B s₀ d)) ∧ Frame [pR (DD.fP s₀)] s₀.mem s'.mem := by
  have hd11 : d ≤ 11 := by rcases widths1024 hd with rfl | rfl <;> decide
  exact DD.loop_ok (c := 8) (b := d) hp hd11 (by decide) (by decide) hd11 (by omega) (by decide) hdd hgrp
    hdi hsi hrd hwr hm

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
  rw [DD.lenEq hp rfl]
  unfold decodeDecompress1024
  refine WP.seq (WP.mono (ddPrologue_ok s₀) fun s₁ ⟨⟨_, si₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h5 : dArg s₀ .rdx = 5 := by simp only [dArg, h]; rfl
    rw [h5]
    exact ddLoop_ok hp (by rw [← h5]; exact hd) h5 (fun i hi s hs => DD.grp_ok (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by rw [bytesAt_length]; omega) (by omega) hs)
      di₁ si₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    have h11 : dArg s₀ .rdx = 11 := by
      rcases widths1024 hd with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
      · exact e
    rw [h11]
    exact ddLoop_ok hp (by rw [← h11]; exact hd) h11 (fun i hi s hs => dgrp11_ok _ (bytesAt_length _ _ _) hi hs)
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

theorem dd4_nosp : NoSp decodeDecompress1024 := nosp_of (by decide +kernel)
theorem dd4_depth : decodeDecompress1024.depth = 0 := by decide +kernel

/-- `vg_mlkem1024_decode_decompress`, for the calls of the top-level functions. -/
theorem ddImpl1024 : DDImpl "vg_mlkem1024_decode_decompress" decodeDecompress1024 Spec.MlKem1024.compressWidths :=
  ⟨fun _ hd => by rcases widths1024 hd with rfl | rfl <;> decide, decodeDecompress1024_correct, decodeDecompress1024_ct, dd4_nosp,
    dd4_depth⟩

end VG.Proof.MlKem1024.X86_64
