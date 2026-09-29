import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.AArch64.Mul
import VerifiedGarbage.Proof.MlKem.AArch64.NttInv
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# ML-KEM-768 on AArch64: calling the primitives

Untrusted: everything here is checked by Lean. Each call of a verified
polynomial primitive, from its proof (with `WP.call`; `sample_ntt` with
`WP.callF`, as its Keccak calls have frames): what it needs of the state it
is called from, and what holds when it returns (`Kept`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem entry (s : State) {r : Reg} (h : r ∉ linkRegs := by decide) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

/-- `vg_mlkem_cbd2(b, f)`. -/
theorem cbd2_call {s : State} {b f : Addr} (h0 : s.gpr .x0 = b) (h1 : s.gpr .x1 = f)
    (hd : Region.Disjoint ⟨b, 128⟩ ⟨f, 1024⟩) (hc : Covers [⟨b, 128⟩, ⟨f, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨f, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) → Q s') :
    WP isa (.call "vg_mlkem_cbd2" cbd2) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = f := (entry s).trans h1
  refine WP.call (k := cbd2AArch64) Cbd2.correct (rd := [⟨b, 128⟩]) (wr := [⟨f, 1024⟩]) ?_ hc hw ?_
  · simp only [cbd2AArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hd⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [cbd2AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1]
      at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-- `vg_mlkem_ntt(f, scratch)` or `vg_mlkem_ntt_inv(f, scratch)`. -/
theorem inPlace_call {t : Poly → Poly} {c : Prog isa} {name : String}
    (hv : ∀ s, (inPlaceAArch64 t).pre s →
      ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (inPlaceAArch64 t).post s s')
    (hn : c.noFrames = true) {s : State} {f w : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = w)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩) (hr : Reduced s.mem f)
    (hw : Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (t (polyAt s.mem f)) → Q s') :
    WP isa (.call name c) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = w := (entry s).trans h1
  refine WP.call (k := inPlaceAArch64 t) hv (rd := []) (wr := [⟨f, 1024⟩, ⟨w, 1024⟩]) ?_
    (covers_rw' hw) hw ?_ hn
  · simp only [inPlaceAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1]
    exact ⟨trivial, trivial, hd, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [inPlaceAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0]
      at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

theorem ntt_call {s : State} {f w : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = w)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩) (hr : Reduced s.mem f)
    (hw : Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (ntt (polyAt s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem_ntt" Impl.MlKem.AArch64.ntt) s Q :=
  inPlace_call Ntt.correct (by decide +kernel) h0 h1 hd hr hw hQ

theorem nttInv_call {s : State} {f w : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = w)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩) (hr : Reduced s.mem f)
    (hw : Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (nttInv (polyAt s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem_ntt_inv" Impl.MlKem.AArch64.nttInv) s Q :=
  inPlace_call Ntt.correctInv (by decide +kernel) h0 h1 hd hr hw hQ

/-- `vg_mlkem_add(f, g)` or `vg_mlkem_sub(f, g)`. -/
theorem acc_call {op : Poly → Poly → Poly} {c : Prog isa} {name : String}
    (hv : ∀ s, (accAArch64 op).pre s →
      ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accAArch64 op).post s s')
    (hn : c.noFrames = true) {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (op (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call name c) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = g := (entry s).trans h1
  refine WP.call (k := accAArch64 op) hv (rd := [⟨g, 1024⟩]) (wr := [⟨f, 1024⟩]) ?_ hc hw ?_ hn
  · simp only [accAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1]
    exact ⟨trivial, trivial, hd, hrf, hrg⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [accAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1]
      at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

theorem add_call {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (add (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_add" Impl.MlKem.AArch64.add) s Q :=
  acc_call add_correct (by decide +kernel) h0 h1 hd hrf hrg hc hw hQ

theorem sub_call {s : State} {f g : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = g)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (sub (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.AArch64.sub) s Q :=
  acc_call sub_correct (by decide +kernel) h0 h1 hd hrf hrg hc hw hQ

/-- `vg_mlkem_multiply_ntts(h, f, g, scratch)`. -/
theorem mul_call {s : State} {h f g w : Addr} (h0 : s.gpr .x0 = h) (h1 : s.gpr .x1 = f)
    (h2 : s.gpr .x2 = g) (h3 : s.gpr .x3 = w)
    (d₁ : Region.Disjoint ⟨h, 1024⟩ ⟨f, 1024⟩) (d₂ : Region.Disjoint ⟨h, 1024⟩ ⟨g, 1024⟩)
    (d₃ : Region.Disjoint ⟨h, 1024⟩ ⟨w, 1024⟩) (d₄ : Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩)
    (d₅ : Region.Disjoint ⟨g, 1024⟩ ⟨w, 1024⟩) (hrf : Reduced s.mem f) (hrg : Reduced s.mem g)
    (hc : Covers [⟨f, 1024⟩, ⟨g, 1024⟩, ⟨h, 1024⟩, ⟨w, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨h, 1024⟩, ⟨w, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨h, 1024⟩, ⟨w, 1024⟩] s s' →
      PolyIs s'.mem h (multiplyNTTs (polyAt s.mem f) (polyAt s.mem g)) → Q s') :
    WP isa (.call "vg_mlkem_multiply_ntts" Impl.MlKem.AArch64.multiplyNTTs) s Q := by
  have c0 : s.callEntry.gpr .x0 = h := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = f := (entry s).trans h1
  have c2 : s.callEntry.gpr .x2 = g := (entry s).trans h2
  have c3 : s.callEntry.gpr .x3 = w := (entry s).trans h3
  refine WP.call (k := mulAArch64) Mul.correct (rd := [⟨f, 1024⟩, ⟨g, 1024⟩])
    (wr := [⟨h, 1024⟩, ⟨w, 1024⟩]) ?_ hc hw ?_
  · simp only [mulAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
    exact ⟨trivial, trivial, d₁, d₂, d₃, d₄, d₅, hrf, hrg⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [mulAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1,
      c2] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-- `vg_mlkem_encode12(f, out)`. -/
theorem encode12_call {s : State} {f o : Addr} (h0 : s.gpr .x0 = f) (h1 : s.gpr .x1 = o)
    (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 384⟩) (hr : Reduced s.mem f)
    (hc : Covers [⟨f, 1024⟩, ⟨o, 384⟩] (s.rd ++ s.wr)) (hw : Covers [⟨o, 384⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 384⟩] s s' → bytesAt s'.mem o 384 = encode12 (polyAt s.mem f) → Q s') :
    WP isa (.call "vg_mlkem_encode12" Impl.MlKem.AArch64.encode12) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = o := (entry s).trans h1
  refine WP.call (k := encode12AArch64) Encode12.correct (rd := [⟨f, 1024⟩]) (wr := [⟨o, 384⟩]) ?_
    hc hw ?_
  · simp only [encode12AArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1]
    exact ⟨trivial, trivial, hd, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [encode12AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0,
      c1] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-- `vg_mlkem_decode12(b, f)`. -/
theorem decode12_call {s : State} {b f : Addr} (h0 : s.gpr .x0 = b) (h1 : s.gpr .x1 = f)
    (hd : Region.Disjoint ⟨b, 384⟩ ⟨f, 1024⟩) (hc : Covers [⟨b, 384⟩, ⟨f, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨f, 1024⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (decode12 (bytesAt s.mem b 384)) → Q s') :
    WP isa (.call "vg_mlkem_decode12" Impl.MlKem.AArch64.decode12) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = f := (entry s).trans h1
  refine WP.call (k := decode12AArch64) Decode12.correct (rd := [⟨b, 384⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [decode12AArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hd⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [decode12AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0,
      c1] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-- `vg_mlkem_compress_encode(f, d, out, 32 d)`. -/
theorem compressEncode_call {s : State} {f o : Addr} {d : Nat} (h0 : s.gpr .x0 = f)
    (h1 : ((s.gpr .x1).setWidth 32).toNat = d) (h2 : s.gpr .x2 = o) (h3 : (s.gpr .x3).toNat = 32 * d)
    (hdw : d ∈ compressWidths) (hd : Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩) (hr : Reduced s.mem f)
    (hc : Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr)) (hw : Covers [⟨o, 32 * d⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) →
      Q s') :
    WP isa (.call "vg_mlkem_compress_encode" Impl.MlKem.AArch64.compressEncode) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  have c1 : ((s.callEntry.gpr .x1).setWidth 32).toNat = d := by rw [entry s]; exact h1
  have c2 : s.callEntry.gpr .x2 = o := (entry s).trans h2
  have c3 : (s.callEntry.gpr .x3).toNat = 32 * d := by rw [entry s]; exact h3
  refine WP.call (k := compressEncodeAArch64) CE.correct (rd := [⟨f, 1024⟩]) (wr := [⟨o, 32 * d⟩]) ?_
    hc hw ?_
  · simp only [compressEncodeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial, hr⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [compressEncodeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-- `vg_mlkem_decode_decompress(b, 32 d, d, f)`. -/
theorem decodeDecompress_call {s : State} {b f : Addr} {d : Nat} (h0 : s.gpr .x0 = b)
    (h1 : (s.gpr .x1).toNat = 32 * d) (h2 : ((s.gpr .x2).setWidth 32).toNat = d) (h3 : s.gpr .x3 = f)
    (hdw : d ∈ compressWidths) (hd : Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩)
    (hc : Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨f, 1024⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 1024⟩] s s' →
      PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') :
    WP isa (.call "vg_mlkem_decode_decompress" Impl.MlKem.AArch64.decodeDecompress) s Q := by
  have c0 : s.callEntry.gpr .x0 = b := (entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = 32 * d := by rw [entry s]; exact h1
  have c2 : ((s.callEntry.gpr .x2).setWidth 32).toNat = d := by rw [entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = f := (entry s).trans h3
  refine WP.call (k := decodeDecompressAArch64) DD.correct (rd := [⟨b, 32 * d⟩]) (wr := [⟨f, 1024⟩]) ?_
    hc hw ?_
  · simp only [decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3]
    exact ⟨trivial, trivial, hd, hdw, trivial⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [decodeDecompressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

theorem sampleNTT_fdepth : Impl.MlKem.AArch64.sampleNTT.fdepth = 1 := by decide +kernel

/-- `vg_mlkem_sample_ntt(seed, a, scratch)`. -/
theorem sample_call {s : State} {sd a w : Addr} (h0 : s.gpr .x0 = sd) (h1 : s.gpr .x1 = a)
    (h2 : s.gpr .x2 = w) (d₁ : Region.Disjoint ⟨sd, 34⟩ ⟨a, 1024⟩)
    (d₂ : Region.Disjoint ⟨sd, 34⟩ ⟨w, 2048⟩) (d₃ : Region.Disjoint ⟨a, 1024⟩ ⟨w, 2048⟩)
    (hsp : 16 ≤ s.sp.toNat) (k₁ : (stk s).Disjoint ⟨sd, 34⟩) (k₂ : (stk s).Disjoint ⟨a, 1024⟩)
    (k₃ : (stk s).Disjoint ⟨w, 2048⟩)
    (hc : Covers [⟨sd, 34⟩, ⟨a, 1024⟩, ⟨w, 2048⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨a, 1024⟩, ⟨w, 2048⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨a, 1024⟩, ⟨w, 2048⟩, below s.sp 16] s s' → Reduced s'.mem a →
      ((s'.gpr .x0 = 1 ∧ sampleNTT 280 (bytesAt s.mem sd 34) = some (polyAt s'.mem a)) ∨
        (s'.gpr .x0 = 0 ∧ sampleNTT 280 (bytesAt s.mem sd 34) = none)) → Q s') :
    WP isa (.call "vg_mlkem_sample_ntt" Impl.MlKem.AArch64.sampleNTT) s Q := by
  have c0 : s.callEntry.gpr .x0 = sd := (entry s).trans h0
  have c1 : s.callEntry.gpr .x1 = a := (entry s).trans h1
  have c2 : s.callEntry.gpr .x2 = w := (entry s).trans h2
  refine WP.callF (k := Sample.sampleStrong) Sample.sample_strong (rd := [⟨sd, 34⟩])
    (wr := [⟨a, 1024⟩, ⟨w, 2048⟩]) ?_ hc hw ?_ (by rw [sampleNTT_fdepth]; decide)
  · simp only [Sample.sampleStrong, sampleAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2]
    exact ⟨trivial, trivial, d₁, d₂, d₃, hsp, k₁, k₂, k₃⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    rw [sampleNTT_fdepth, Nat.mul_one] at hf
    simp only [Sample.sampleStrong, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c0, c1] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, frame3 hf⟩ hpost.1 hpost.2

/-- What a call of `sample_ntt` needs. -/
structure SampleArgs (s : State) (sd a w : Addr) : Prop where
  h0 : s.gpr .x0 = sd
  h1 : s.gpr .x1 = a
  h2 : s.gpr .x2 = w
  d₁ : Region.Disjoint ⟨sd, 34⟩ ⟨a, 1024⟩
  d₂ : Region.Disjoint ⟨sd, 34⟩ ⟨w, 2048⟩
  d₃ : Region.Disjoint ⟨a, 1024⟩ ⟨w, 2048⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (stk s).Disjoint ⟨sd, 34⟩
  k₂ : (stk s).Disjoint ⟨a, 1024⟩
  k₃ : (stk s).Disjoint ⟨w, 2048⟩
  hc : Covers [⟨sd, 34⟩, ⟨a, 1024⟩, ⟨w, 2048⟩] (s.rd ++ s.wr)
  hw : Covers [⟨a, 1024⟩, ⟨w, 2048⟩] s.wr

theorem SampleArgs.pre {s : State} {sd a w : Addr} (h : SampleArgs s sd a w) :
    Sample.sampleStrong.pre (s.callEntry.withRegions [⟨sd, 34⟩] [⟨a, 1024⟩, ⟨w, 2048⟩]) := by
  have c0 : s.callEntry.gpr .x0 = sd := (entry s).trans h.h0
  have c1 : s.callEntry.gpr .x1 = a := (entry s).trans h.h1
  have c2 : s.callEntry.gpr .x2 = w := (entry s).trans h.h2
  simp only [Sample.sampleStrong, sampleAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃⟩

/-- A call of `sample_ntt` returns with the stack pointer it was called with. -/
theorem SampleArgs.sp {s : State} {sd a w : Addr} (h : SampleArgs s sd a w) :
    WP isa (.call "vg_mlkem_sample_ntt" Impl.MlKem.AArch64.sampleNTT) s fun s' => s'.sp = s.sp :=
  sample_call h.h0 h.h1 h.h2 h.d₁ h.d₂ h.d₃ h.hsp h.k₁ h.k₂ h.k₃ h.hc h.hw fun _ k _ _ => k.sp

/-- Two calls of `sample_ntt` on the same seed, at the same addresses, leak the same. -/
theorem sample_ct {P : State → State → Prop} {sd a w : Addr}
    (hP : ∀ s₁ s₂, P s₁ s₂ → SampleArgs s₁ sd a w ∧ SampleArgs s₂ sd a w ∧
      bytesAt s₁.mem sd 34 = bytesAt s₂.mem sd 34 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call "vg_mlkem_sample_ntt" Impl.MlKem.AArch64.sampleNTT) fun _ _ => True :=
  AArch64.RelCT.call Sample.sample_strong Sample.ct_strong [⟨sd, 34⟩] [⟨a, 1024⟩, ⟨w, 2048⟩] fun s₁ s₂ h => by
    obtain ⟨A₁, A₂, hb, hsp⟩ := hP s₁ s₂ h
    refine ⟨A₁.pre, A₂.pre, ?_, A₁.hc, A₁.hw, A₂.hc, A₂.hw⟩
    have c0 : ∀ {u : State}, SampleArgs u sd a w → u.callEntry.gpr .x0 = sd := fun hu => (entry _).trans hu.h0
    have c1 : ∀ {u : State}, SampleArgs u sd a w → u.callEntry.gpr .x1 = a := fun hu => (entry _).trans hu.h1
    have c2 : ∀ {u : State}, SampleArgs u sd a w → u.callEntry.gpr .x2 = w := fun hu => (entry _).trans hu.h2
    simp only [Sample.sampleStrong, sampleAArch64, State.withRegions_gpr, State.withRegions_sp,
      State.withRegions_mem, State.callEntry_sp, State.callEntry_mem, c0 A₁, c1 A₁, c2 A₁, c0 A₂, c1 A₂,
      c2 A₂, hsp, hb]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.MlKem.AArch64
