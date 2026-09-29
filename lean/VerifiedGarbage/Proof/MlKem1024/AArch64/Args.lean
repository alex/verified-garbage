import VerifiedGarbage.Proof.MlKem.AArch64.TopArgs
import VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.AArch64.DecodeDecompress

/-!
# ML-KEM-1024 on AArch64: buffers of the top-level functions, and calls

Untrusted: everything here is checked by Lean. As `TopArgs.lean` of
ML-KEM-768 (whose `R`, `R.sub` and `R.cov` serve here), for arguments of
up to 64 KiB, as ML-KEM-1024's 48 KiB `scratch` (`Args`, `Args.rdisj`,
`Args.rstk`); and the calls of ML-KEM-1024's compression functions, from
their proofs (as `PrimCall.lean` of ML-KEM-768).
-/

namespace VG.Proof.MlKem1024.AArch64

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The arguments' regions `⟨A b, L b⟩` (for `b < nb`) are pairwise
disjoint, at most 64 KiB, and apart from the 16 bytes below `sp`. -/
structure Args (A : Nat → Addr) (L : Nat → Nat) (nb : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → Region.Disjoint ⟨A b, L b⟩ ⟨A c, L c⟩
  len : ∀ b < nb, L b ≤ 65536
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, L b⟩

theorem Args.rdisj {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : Args A L nb sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ L b₁)
    (f₂ : o₂ + l₂ ≤ L b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R A b₁ o₁ l₁).Disjoint (R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    have hl := h.len b₁ hb₁
    have hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem Args.rstk {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : Args A L nb sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ L b) : Region.Disjoint ⟨sp - 16, 16⟩ (R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

/-- `vg_mlkem1024_compress_encode(f, d, out, 32 d)`. -/
theorem compressEncode1024_call {s : State} {f o : Addr} {d : Nat} (h0 : s.gpr .x0 = f)
    (h1 : ((s.gpr .x1).setWidth 32).toNat = d) (h2 : s.gpr .x2 = o) (h3 : (s.gpr .x3).toNat = 32 * d)
    (hdw : d ∈ Spec.MlKem1024.compressWidths) (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩)
    (hr : Reduced s.mem f) (hc : Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨o, 32 * d⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) →
      Q s') :
    WP isa (.call "vg_mlkem1024_compress_encode" Impl.MlKem1024.AArch64.compressEncode) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : ((s.callEntry.gpr .x1).setWidth 32).toNat = d := by rw [entry s]; exact h1
  have c2 : s.callEntry.gpr .x2 = o := (entry s).trans h2
  have c3 : (s.callEntry.gpr .x3).toNat = 32 * d := by rw [entry s]; exact h3
  refine WP.call (k := MlKem1024.compressEncodeAArch64) MlKem1024.AArch64.CE.correct (rd := [⟨f, 1024⟩]) (wr := [⟨o, 32 * d⟩]) ?_
    hc hw ?_
  · simp only [MlKem1024.compressEncodeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [MlKem1024.compressEncodeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-- `vg_mlkem1024_decode_decompress(b, 32 d, d, f)`. -/
theorem decodeDecompress1024_call {s : State} {b f : Addr} {d : Nat} (h0 : s.gpr .x0 = b)
    (h1 : (s.gpr .x1).toNat = 32 * d) (h2 : ((s.gpr .x2).setWidth 32).toNat = d) (h3 : s.gpr .x3 = f)
    (hdw : d ∈ Spec.MlKem1024.compressWidths) (hd : Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩)
    (hc : Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' →
      PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') :
    WP isa (.call "vg_mlkem1024_decode_decompress" Impl.MlKem1024.AArch64.decodeDecompress) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = 32 * d := by rw [entry s]; exact h1
  have c2 : ((s.callEntry.gpr .x2).setWidth 32).toNat = d := by rw [entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = f := (entry s).trans h3
  refine WP.call (k := MlKem1024.decodeDecompressAArch64) MlKem1024.AArch64.DD.correct (rd := [⟨b, 32 * d⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [MlKem1024.decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [MlKem1024.decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

end VG.Proof.MlKem1024.AArch64
