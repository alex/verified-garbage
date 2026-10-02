import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
import VerifiedGarbage.Proof.MlKem1024.Arm.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.Arm.Decompress
import VerifiedGarbage.Impl.MlKem1024.Arm.Top

/-!
# ML-KEM-1024 on 32-bit ARM: calling the compression to 5 and 11 bits

As `Proof/MlKem/Arm/Calls.lean` and `CallsCT.lean` for the other primitives: a
contract written with the precondition of the proof of
`vg_mlkem1024_compress_encode` (and of `vg_mlkem1024_decode_decompress`) and
what it shows, the call of it with its arguments at offsets in the buffers of
a layout (`compressL4`, `decompressL4`), and that it is constant time from any
state whose argument registers are public (`compress4T`, `decompress4T`).
-/

namespace VG.Proof.MlKem1024.Arm

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm

/-! ## `vg_mlkem1024_compress_encode`, `vg_mlkem1024_decode_decompress` -/

def kCmp4 : Contract isa := mkK CompressEncode.Pre
  (fun s₀ s => bytesAt s.mem (CompressEncode.O s₀) (CompressEncode.len s₀) = CompressEncode.CE s₀)
  (regsEq [.r0, .r1, .r2, .r3])

theorem kCmp4_ok : ∀ s, kCmp4.pre s → ∃ t s', Exec isa compressEncode1024 s t s' ∧
    abiPreserved s s' ∧ kCmp4.post s s' := mkK_ok fun _ hp => CompressEncode.correct hp

def kDcm4 : Contract isa := mkK Decompress.Pre (fun s₀ s => PolyIs s.mem (Decompress.F s₀) (Decompress.D s₀))
  (regsEq [.r0, .r1, .r2, .r3])

theorem kDcm4_ok : ∀ s, kDcm4.pre s → ∃ t s', Exec isa decodeDecompress1024 s t s' ∧
    abiPreserved s s' ∧ kDcm4.post s s' := mkK_ok fun _ hp => Decompress.correct hp

theorem width_lt4 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : d < 2 ^ 32 ∧ 32 * d < 2 ^ 32 := by
  rcases VG.Proof.MlKem.mem_compressWidths1024 hd with rfl | rfl <;> decide

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `(i, o)` into the `32 d` bytes at `(j, o')`. -/
theorem compressL4 {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (g2 : s.gpr .r2 = L.ptr j + BitVec.ofNat 32 o') (g3 : s.gpr .r3 = BitVec.ofNat 32 (32 * d))
    (hd : d ∈ Spec.MlKem1024.compressWidths) (hs : sepB L.sizes (i, o, 1024) (j, o', 32 * d) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {f : Poly} (hf : PolyIs s.mem (L.A i o) f)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 32 * d)]) s s' → bytesAt s'.mem (L.A j o') (32 * d) = compressEncode d f →
      Q s') :
    WP isa callCompress4 s Q := by
  have ⟨d1, d2⟩ := width_lt4 hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths1024 hd with rfl | rfl <;> decide
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) (by decide)
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) hd0
  have eF : CompressEncode.F (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = L.A i o := by
    simp only [CompressEncode.F, CompressEncode.pf, view_r0, g0, ea]
  have eO : CompressEncode.O (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = L.A j o' := by
    simp only [CompressEncode.O, CompressEncode.po, view_r2, g2, eb]
  have eD : CompressEncode.dd (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = d := by
    simp only [CompressEncode.dd, view_r1, g1, toNat_ofNat32 d1]
  have eL : CompressEncode.len (view s [polyRegion (L.A i o)] [⟨L.A j o', 32 * d⟩]) = 32 * d := by
    simp only [CompressEncode.len, view_r3, g3, toNat_ofNat32 d2]
  have cw : Covers [⟨L.A j o', 32 * d⟩] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kCmp4) kCmp4_ok (by decide +kernel) (rd := [polyRegion (L.A i o)])
    (wr := [⟨L.A j o', 32 * d⟩])
    ⟨by simp only [eF, State.withRegions_rd], by simp only [CompressEncode.outR, eO, eL, State.withRegions_wr],
      by simp only [CompressEncode.outR, eF, eO, eL]; exact Lay.disj hL hs,
      by simp only [CompressEncode.pf, view_r0, g0]; exact fa, by rw [eL]; simp only [CompressEncode.po, view_r2, g2]; exact fb,
      by rw [eD]; exact hd, by rw [eL, eD], by rw [eF]; exact hf.1⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kCmp4, mkK, CompressEncode.CE, CompressEncode.fp, eF, eO, eL, eD, State.withRegions_mem,
    State.callEntry_mem, hf.2] at hq
  exact hq

/-- `Decompress_d(ByteDecode_d(·))` of the `32 d` bytes at `(i, o)` into the polynomial at `(j, o')`. -/
theorem decompressL4 {L : Lay} {s : State} (hL : L.Ok) {i o j o' d : Nat}
    (g0 : s.gpr .r0 = L.ptr i + BitVec.ofNat 32 o) (g1 : s.gpr .r1 = BitVec.ofNat 32 (32 * d))
    (g2 : s.gpr .r2 = BitVec.ofNat 32 d) (g3 : s.gpr .r3 = L.ptr j + BitVec.ofNat 32 o')
    (hd : d ∈ Spec.MlKem1024.compressWidths) (hs : sepB L.sizes (i, o, 32 * d) (j, o', 1024) = true)
    (wi : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(j, o', 1024)]) s s' →
      PolyIs s'.mem (L.A j o') (decodeDecompress d (bytesAt s.mem (L.A i o) (32 * d))) → Q s') :
    WP isa callDecompress4 s Q := by
  have ⟨d1, d2⟩ := width_lt4 hd
  have hd0 : 0 < 32 * d := by rcases VG.Proof.MlKem.mem_compressWidths1024 hd with rfl | rfl <;> decide
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) hd0
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) (by decide)
  have eB : Decompress.B (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = L.A i o := by
    simp only [Decompress.B, Decompress.pb, view_r0, g0, ea]
  have eF : Decompress.F (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = L.A j o' := by
    simp only [Decompress.F, Decompress.pf, view_r3, g3, eb]
  have eD : Decompress.dd (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = d := by
    simp only [Decompress.dd, view_r2, g2, toNat_ofNat32 d1]
  have eL : Decompress.len (view s [⟨L.A i o, 32 * d⟩] [polyRegion (L.A j o')]) = 32 * d := by
    simp only [Decompress.len, view_r1, g1, toNat_ofNat32 d2]
  have cw : Covers [polyRegion (L.A j o')] s.wr := Lay.covers wj (sepB_bounds (sepB_symm hs)).2
  refine call_kept (k := kDcm4) kDcm4_ok (by decide +kernel) (rd := [⟨L.A i o, 32 * d⟩])
    (wr := [polyRegion (L.A j o')])
    ⟨by simp only [Decompress.inR, eB, eL, State.withRegions_rd], by simp only [eF, State.withRegions_wr],
      by simp only [Decompress.inR, eB, eF, eL]; exact Lay.disj hL hs,
      by rw [eL]; simp only [Decompress.pb, view_r0, g0]; exact fa, by simp only [Decompress.pf, view_r3, g3]; exact fb,
      by rw [eD]; exact hd, by rw [eL, eD]⟩
    (covers_append (Lay.covers wi (sepB_bounds hs).2) (covers_wr cw)) cw fun s' hk hq => hQ s' hk ?_
  simp only [kDcm4, mkK, Decompress.D, Decompress.bs, eB, eF, eL, eD, State.withRegions_mem,
    State.callEntry_mem] at hq
  exact hq

theorem compress4T :
    ConstantTime isa (fun _ => True) (regsEq [.r0, .r1, .r2, .r3]) compressEncode1024 :=
  Add.ctRegs (k := kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

theorem decompress4T :
    ConstantTime isa (fun _ => True) (regsEq [.r0, .r1, .r2, .r3]) decodeDecompress1024 :=
  Add.ctRegs (k := kT [.r0, .r1, .r2, .r3]) [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

theorem at352_eq (p : BitVec 32) {i : Nat} (_h : 352 * i < 2 ^ 32) :
    p + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 6 + BitVec.ofNat 32 i <<< 5 = p + BitVec.ofNat 32 (352 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

end VG.Proof.MlKem1024.Arm
