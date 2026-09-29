import VerifiedGarbage.Proof.MlKem1024.X86_64.Groups
import VerifiedGarbage.Proof.MlKem1024.X86_64.Contracts
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_compress_encode`

Untrusted: everything here is checked by Lean. A segment of a group is
bytes of the encoding (`ce_seg`); a group's segments write its `d` bytes
(`grp5_ok`, `grp11_ok`); the loop is proven once for both widths, from what
its group does (`CE4.loop_ok`), and the function by its two cases.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem widths1024 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : d = 5 ∨ d = 11 :=
  mem_compressWidths1024 hd

/-- Bytes of a segment of group `i`: the number of its `c` values from `o`,
shifted right by `s + p` bits, is byte `j` of the group. -/
theorem ce_seg {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (F : Poly) {i o c s p j : Nat} (hi : i < 32)
    (hoc : o + c ≤ 8) (hp : s + p + 8 ≤ d * c) (hj : 8 * j = d * o + s + p) (hjd : j < d) :
    BitVec.ofNat 8 (digits d ((List.range c).map fun t => compress d F[8 * i + (o + t)]!) / 2 ^ s / 2 ^ p) =
      (compressEncode d F)[d * i + j]! := by
  have hd0 : 0 < d := by rcases widths1024 hd with rfl | rfl <;> decide
  have hL := map_toList_lt F (compress_lt d)
  have hk : d * i + j < 32 * d := by
    have := Nat.mul_le_mul_left d (show i + 1 ≤ 32 by omega); rw [Nat.mul_succ] at this
    rw [Nat.mul_comm 32 d]; omega
  rw [compressEncode, byteEncode_getElem hd0 hL hk]
  apply ofNat8_eq
  have e : (List.range c).map (fun t => compress d F[8 * i + (o + t)]!) =
      ((F.map (compress d)).toList.drop (8 * i + o)).take c := by
    rw [take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
    refine List.map_congr_left fun t ht => ?_
    rw [map_toList_getD _ _ (by have := List.mem_range.mp ht; omega), Nat.add_assoc]
  have ex : d * (8 * i + o) + s + p = 8 * (d * i + j) := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_add 8]; omega
  rw [e, show (256 : Nat) = 2 ^ 8 from rfl, chunk_eq hL (8 * i + o) c s p 8 hp, ex]

theorem shr10_ok (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 63) (s : State) :
    WP isa (.block [.shift .shr .r10 n]) s fun s' =>
      (s'.gpr .r10 = s.gpr .r10 >>> n ∧ s'.mem = s.mem) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hn, hn']

theorem ceV_lt (d : Nat) (a : BitVec 32) (M : BitVec 64) : (ceV d a M).toNat < 2 ^ 64 := (ceV d a M).isLt

/-- The group's facts that its code needs. -/
structure GrpIn (d : Nat) (F : Poly) (i : Nat) (s : State) : Prop where
  rd : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4
  v : ∀ j < 8, (ceV d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9)).toNat =
    compress d F[8 * i + j]!
  wr : ∀ k < d, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 k) 1
  dj : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .r8, d⟩

theorem grp5_ok (F : Poly) {i : Nat} (hi : i < 32) {s : State} (h : GrpIn 5 F i s) :
    WP isa (.block (ceAcc 5 0 8 ++ ceSt 0 5)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) 5 (fun k => (compressEncode 5 F)[5 * i + k]!) ∧ Keep [.rax, .rdx, .r10] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (ceAcc_ok (o := 0) (c := 8) (by decide) (by decide) (by decide) s
    (fun j hj => by rw [Nat.zero_add]; exact h.rd j hj) (fun j => compress 5 F[8 * i + (0 + j)]!)
    (fun j hj => by rw [Nat.zero_add]; exact h.v j hj) (fun _ _ => compress_lt 5 _)) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 0) (nb := 5) (by decide) s₁ (fun k hk => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr k hk)) fun s₂ ⟨w₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono (by decide)⟩
  rw [k₁.gpr (by decide), add_ofNat_zero, m₁, r₁] at w₂
  refine w₂.congr fun k hk => ?_
  rw [← ce_seg (o := 0) (c := 8) (s := 0) (p := 8 * k) (by decide) F hi (by decide) (by omega) (by omega) hk,
    Nat.pow_zero, Nat.div_one]

theorem grp11_ok (F : Poly) {i : Nat} (hi : i < 32) {s : State} (h : GrpIn 11 F i s) :
    WP isa (.block (ceAcc 11 0 5 ++ ceSt 0 6 ++ ceAcc 11 4 4 ++ ([.shift .shr .r10 4] : List Instr) ++ ceSt 6 5)) s
      fun s' => Written s.mem s'.mem (s.gpr .r8) 11 (fun k => (compressEncode 11 F)[11 * i + k]!) ∧
        Keep [.rax, .rdx, .r10] s s' := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  -- Values 0–4, and bytes 0–5.
  refine WP.mono (ceAcc_ok (o := 0) (c := 5) (by decide) (by decide) (by decide) s
    (fun j hj => by rw [Nat.zero_add]; exact h.rd j (by omega)) (fun j => compress 11 F[8 * i + (0 + j)]!)
    (fun j hj => by rw [Nat.zero_add]; exact h.v j (by omega)) (fun _ _ => compress_lt 11 _)) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 0) (nb := 6) (by decide) s₁ (fun k hk => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr k (by omega))) fun s₂ ⟨w₂, k₂⟩ => ?_
  rw [k₁.gpr (by decide), add_ofNat_zero, m₁, r₁] at w₂
  -- Values 4–7, shifted, and bytes 6–10.
  have di₂ : s₂.gpr .rdi = s.gpr .rdi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have r9₂ : s₂.gpr .r9 = s.gpr .r9 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have r8₂ : s₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]
  have ww₂ : s₂.wr = s.wr := by rw [k₂.2.2, k₁.2.2]
  have hf₂ : Frame [⟨s.gpr .r8, 6⟩] s.mem s₂.mem := w₂.frame (Region.contains_self _ _)
  have hv₂ : ∀ j < 8, s₂.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 =
      s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 := fun j hj =>
    hf₂.readW (r := ⟨s.gpr .rdi, 32⟩) (contains_offset' (by omega) (by decide)) (fun r' hr' => by
      rw [List.mem_singleton] at hr'; subst hr'; exact h.dj.sub_right (Region.sub_prefix (by decide))) (by decide)
  refine WP.mono (ceAcc_ok (o := 4) (c := 4) (by decide) (by decide) (by decide) s₂
    (fun j hj => by rw [rw₂, di₂]; exact h.rd _ (by omega)) (fun j => compress 11 F[8 * i + (4 + j)]!)
    (fun j hj => by rw [di₂, r9₂, hv₂ _ (by omega)]; exact h.v _ (by omega)) (fun _ _ => compress_lt 11 _))
    fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  refine WP.mono (shr10_ok 4 (by decide) (by decide) s₃) fun s₄ ⟨⟨r₄, m₄⟩, k₄⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 6) (nb := 5) (by decide) s₄ (fun k hk => by
      rw [k₄.2.2, k₃.2.2, ww₂, k₄.gpr (by decide), k₃.gpr (by decide), r8₂]; exact h.wr _ (by omega)))
    fun s₅ ⟨w₅, k₅⟩ => ⟨?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  rw [k₄.gpr (by decide), k₃.gpr (by decide), r8₂, m₄, m₃, r₄, shr_toNat, r₃] at w₅
  refine (Written.append w₂ w₅ (by decide)).congr fun k hk => ?_
  by_cases hk6 : k < 6
  · rw [ifp hk6, ← ce_seg (o := 0) (c := 5) (s := 0) (p := 8 * k) (by decide) F hi (by decide) (by omega) (by omega) (by omega),
      Nat.pow_zero, Nat.div_one]
  · rw [ifn hk6, ← ce_seg (o := 4) (c := 4) (s := 4) (p := 8 * (k - 6)) (j := k) (by decide) F hi (by decide) (by omega)
      (by omega) hk]

namespace CE4

section
variable (s₀ : State)
abbrev fP : Addr := s₀.gpr .rdi
abbrev oP : Addr := s₀.gpr .rdx
abbrev F : Poly := polyAt s₀.mem (fP s₀)
end

/-- After `i` groups. -/
structure Inv (s₀ : State) (d : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = fP s₀ + BitVec.ofNat 64 (32 * i)
  r8 : s.gpr .r8 = oP s₀ + BitVec.ofNat 64 (d * i)
  r9 : (s.gpr .r9).toNat = compressMul1024 d
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨oP s₀, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < d * i, s.mem (oP s₀ + BitVec.ofNat 64 k) = (compressEncode d (F s₀))[k]!

theorem tail_ok (b : Nat) (hb : b < 2 ^ 31) (s : State) :
    WP isa (.block (ceTail b)) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 32 ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 b ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ceTail
  xrun [sx_ofNat hb]
  rfl

theorem hd11 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : 1 ≤ d ∧ d ≤ 11 := by
  rcases widths1024 hd with rfl | rfl <;> decide

theorem lenEq {s₀ : State} (hp : compressEncode1024K.pre s₀) {d : Nat} (hdd : dArg s₀ .rsi = d) :
    (s₀.gpr .rcx).toNat = 32 * d := by rw [hp.2.2.2.2.2.2.1, hdd]

section
variable {s₀ : State} (hp : compressEncode1024K.pre s₀) {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths)
  (hdd : dArg s₀ .rsi = d)
include hp hd hdd

theorem coeff {m : Mem} (hf : Frame [⟨oP s₀, 32 * d⟩] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (fP s₀) k = coeffAt s₀.mem (fP s₀) k := by
  have := (hd11 hd).2
  exact coeffAt_congr (bytes_frame hf (by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; simpa using this) (by decide)) hk

theorem step {grp : List Instr}
    (hgrp : ∀ i < 32, ∀ s, GrpIn d (F s₀) i s → WP isa (.block grp) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) d (fun k => (compressEncode d (F s₀))[d * i + k]!) ∧ Keep [.rax, .rdx, .r10] s s')
    {i : Nat} (hi : i < 32) {s : State} (hI : Inv s₀ d i s) :
    WP isa (.block (grp ++ ceTail d)) s fun s' => Inv s₀ d (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hd1, hd11⟩ := hd11 hd
  have hbi : d * i + d ≤ 32 * d := by
    have := Nat.mul_le_mul_left d (show i + 1 ≤ 32 by omega); rw [Nat.mul_succ] at this; rw [Nat.mul_comm 32 d]; omega
  have hrd : s.rd ++ s.wr = [pR (fP s₀), ⟨oP s₀, 32 * d⟩] := by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, lenEq hp hdd]; rfl
  have hwr : s.wr = [⟨oP s₀, 32 * d⟩] := by rw [hI.wr, hp.2.1, lenEq hp hdd]
  have ha : ∀ j < 8, s.gpr .rdi + BitVec.ofNat 64 (4 * j) = coeffAddr (fP s₀) (8 * i + j) := fun j _ => by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hdj : Region.Disjoint (pR (fP s₀)) ⟨oP s₀, 32 * d⟩ := by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (hgrp i hi s ⟨fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, ?_⟩) fun s₁ ⟨w₁, k₁⟩ => ?_
  · rw [ha j hj, hrd]; exact ⟨_, by simp, coeff_contains _ (show 8 * i + j < 256 by omega)⟩
  · have hr : Reduced s₀.mem (fP s₀) := hp.2.2.2.2.2.2.2
    have hk : 8 * i + j < 256 := by omega
    rw [ha j hj, ← coeffAt_eq, coeff hp hd hdd hI.frame hk]
    have harg := compress1024_arg_lt hd (F s₀)[8 * i + j]!
    rw [polyAt_val hr hk] at harg
    rw [ceV_toNat hd11 (by rw [hI.r9]; unfold compressAdd1024 at harg; exact harg), hI.r9,
      compress1024_eq hd, polyAt_val hr hk]
    rfl
  · rw [hwr, hI.r8, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_singleton_self _, contains_offset' (by omega) (by omega)⟩
  · rw [hI.rdi, hI.r8]
    exact (hdj.sub_left (sub_offset' (by omega) (by decide))).sub_right (sub_offset' (by omega) (by omega))
  refine WP.mono (tail_ok d (by omega) s₁) fun s₂ ⟨⟨di₂, r8₂, cx₂, z₂, m₂⟩, k₂⟩ => ⟨?_, ?_, ?_⟩
  rotate_left
  · rw [cx₂, k₁.gpr (by decide)]
  · rw [z₂, k₁.gpr (by decide)]
  have hw : Written s.mem s₂.mem (oP s₀ + BitVec.ofNat 64 (d * i)) d
      fun k => (compressEncode d (F s₀))[d * i + k]! := by
    rw [m₂, ← hI.r8]; exact w₁
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hw hbi (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega)⟩
  · rw [di₂, k₁.gpr (by decide), hI.rdi]; exact ptr_step _ i 32
  · rw [r8₂, k₁.gpr (by decide), hI.r8]; exact ptr_step _ i d
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.r9]
  · rw [k₂.2.1, k₁.2.1, hI.rd]
  · rw [k₂.2.2, k₁.2.2, hI.wr]

/-- The loop for the width `d`, from a state with `f` in `rdi` and `out` in `r8`. -/
theorem loop_ok {grp : List Instr}
    (hgrp : ∀ i < 32, ∀ s, GrpIn d (F s₀) i s → WP isa (.block grp) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) d (fun k => (compressEncode d (F s₀))[d * i + k]!) ∧ Keep [.rax, .rdx, .r10] s s')
    {s : State} (hdi : s.gpr .rdi = fP s₀) (h8 : s.gpr .r8 = oP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ceLoop d (grp ++ ceTail d)) s fun s' => bytesAt s'.mem (oP s₀) (32 * d) = compressEncode d (F s₀) ∧
      Frame [⟨oP s₀, 32 * d⟩] s₀.mem s'.mem := by
  have hM : ceMul1024 d < 2 ^ 31 := by rw [ceMul1024]; split <;> decide
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun s' => s'.gpr .r9 = BitVec.ofNat 64 (ceMul1024 d) ∧ s'.mem = s.mem)
    (by xrun [sx_ofNat hM]) (by rfl)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_counted (N := 32) (v := 32) rfl (by decide) (Inv s₀ d)
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega)⟩)
    fun i hi s hI => step hp hd hdd hgrp hi hI) fun s' hI => ⟨?_, hI.frame⟩
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), h8]; simp
  · rw [k₂.gpr (by decide), h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rcases widths1024 hd with rfl | rfl <;> rfl
  · rw [k₂.2.1, k₁.2.1, hrd]
  · rw [k₂.2.2, k₁.2.2, hwr]
  · rw [m₂, m₁, hm]; exact Frame.refl _ _
  · exact bytesAt_eq! (compressEncode_length _ _) fun k hk => hI.done k (by rw [Nat.mul_comm]; exact hk)

end

end CE4

theorem cePrologue_ok (s₀ : State) :
    WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 5)]) s₀ fun s =>
      (s.gpr .rsi = BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.gpr .rsi)) ∧ s.gpr .r8 = s₀.gpr .rdx ∧
        s.zf = some (BitVec.setWidth 32 (s₀.gpr .rsi) - 5 == 0) ∧ s.mem = s₀.mem) ∧ Keep [.rsi, .r8] s₀ s := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem ce_wp {s₀ : State} (hp : compressEncode1024K.pre s₀) :
    WP isa compressEncode1024 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE4.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [CE4.lenEq hp rfl]
  unfold compressEncode1024
  refine WP.seq (WP.mono (cePrologue_ok s₀) fun s₁ ⟨⟨_, r8₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h5 : dArg s₀ .rsi = 5 := by simp only [dArg, h]; rfl
    rw [h5]
    exact CE4.loop_ok hp (by rw [← h5]; exact hd) h5 (fun i hi s hs => grp5_ok _ hi hs) di₁ r8₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    have h11 : dArg s₀ .rsi = 11 := by
      rcases widths1024 hd with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
      · exact e
    rw [h11]
    exact CE4.loop_ok hp (by rw [← h11]; exact hd) h11 (fun i hi s hs => grp11_ok _ hi hs) di₁ r8₁ k₁.2.1 k₁.2.2 m₁

theorem compressEncode1024_correct (s : State) (hs : compressEncode1024K.pre s) :
    ∃ t s', Exec isa compressEncode1024 s t s' ∧ abiPreserved s s' ∧ compressEncode1024K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := compressEncode1024)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] (ce_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem compressEncode1024_ct :
    ConstantTime isa compressEncode1024K.pre compressEncode1024K.pub compressEncode1024 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def compressEncode1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 5 | .rdx => 0x2000 | .rcx => 160 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 160⟩]

theorem compressEncode1024_verified :
    Verified X86_64.target compressEncode1024 (Spec.MlKem1024.compressEncodeContract X86_64.abi) :=
  Verified.of_correct compressEncode1024_correct compressEncode1024_ct (by
    mlkem_implies [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, compressEncode1024K,
      X86_64.abi, X86_64.argRegs] [compressEncode1024Sat] using compressEncode1024Sat)

end VG.Proof.MlKem1024.X86_64
