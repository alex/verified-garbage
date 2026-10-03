import VerifiedGarbage.Proof.MlKem.X86_64.Groups
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: compression (`vg_mlkem_compress_encode`, `vg_mlkem1024_compress_encode`)

The loop over the groups is proven once, for any widths, group of `c`
coefficients and `b` bytes, multiplier and rounding constant, from what the
code of a group does (`CE.loop_ok`), given the facts it needs (`CE.GrpIn`):
a group whose code accumulates its `c` values and stores its `b` bytes
(`CE.grp_ok`), as for every width of `vg_mlkem_compress_encode`, or one in
segments (`vg_mlkem1024_compress_encode`). `vg_mlkem_compress_encode` is
proven by its three cases.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem ceMul_eq : ceMul = compressMul := rfl

namespace CE

section
variable (s₀ : State)
abbrev fP : Addr := s₀.gpr .rdi
abbrev oP : Addr := s₀.gpr .rdx
abbrev F : Poly := polyAt s₀.mem (fP s₀)
end

/-- After `i` groups of `c` coefficients and `b` bytes, with the multiplier `M` in `r9`. -/
structure Inv (s₀ : State) (d c b M : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = fP s₀ + BitVec.ofNat 64 (4 * c * i)
  r8 : s.gpr .r8 = oP s₀ + BitVec.ofNat 64 (b * i)
  r9 : (s.gpr .r9).toNat = M
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨oP s₀, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < b * i, s.mem (oP s₀ + BitVec.ofNat 64 k) = (compressEncode d (F s₀))[k]!

theorem tail_ok (c b : Nat) (hc : 4 * c < 2 ^ 31) (hb : b < 2 ^ 31) (s : State) :
    WP isa (.block [.alu .add .rdi (.imm (BitVec.ofNat 32 (4 * c))), .alu .add .r8 (.imm (BitVec.ofNat 32 b)),
      .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 b ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sx_ofNat hc, sx_ofNat hb]

theorem lenEq {ws : List Nat} {s₀ : State} (hp : (compressEncodeWK ws).pre s₀) {d : Nat} (hdd : dArg s₀ .rsi = d) :
    (s₀.gpr .rcx).toNat = 32 * d := by rw [hp.2.2.2.2.2.2.1, hdd]

/-- What the code of group `i` needs: its coefficients readable, their
compressed values (with the multiplier in `r9` and the rounding constant
`r`), its bytes writable, apart. -/
structure GrpIn (r d c b : Nat) (F : Poly) (i : Nat) (s : State) : Prop where
  rd : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4
  v : ∀ j < c, (ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9)).toNat =
    compress d F[c * i + j]!
  wr : ∀ k < b, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 k) 1
  dj : Region.Disjoint ⟨s.gpr .rdi, 4 * c⟩ ⟨s.gpr .r8, b⟩

/-- What the code of group `i` does: its `b` bytes of the encoding. -/
abbrev GrpOut (d b : Nat) (F : Poly) (i : Nat) (s s' : State) : Prop :=
  Written s.mem s'.mem (s.gpr .r8) b (fun k => (compressEncode d F)[b * i + k]!) ∧ Keep [.rax, .rdx, .r10] s s'

section
variable {ws : List Nat} {s₀ : State} (hp : (compressEncodeWK ws).pre s₀) {r d c b M : Nat}
  (hd11 : 1 ≤ d ∧ d ≤ 11) (hc0 : 0 < c) (hc8 : c ≤ 8) (hb : b ≤ 11) (hbN : b * (256 / c) = 32 * d)
  (hcN : c * (256 / c) = 256) (hdd : dArg s₀ .rsi = d)
  (hcomp : ∀ x : Zq, x.val * M + r < 2 ^ 30 ∧ compress d x = (x.val * M + r) / 2 ^ 19 % 2 ^ d)
include hp hd11 hc0 hc8 hb hbN hcN hdd

omit hd11 hc0 hc8 hb hbN hcN in
theorem coeff {m : Mem} (hf : Frame [⟨oP s₀, 32 * d⟩] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (fP s₀) k = coeffAt s₀.mem (fP s₀) k :=
  coeffAt_congr (bytes_frame hf (by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; simpa using this) (by decide)) hk

include hcomp in
theorem step {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, GrpIn r d c b (F s₀) i s → WP isa (.block grp) s (GrpOut d b (F s₀) i s))
    {i : Nat} (hi : i < 256 / c) {s : State} (hI : Inv s₀ d c b M i s) :
    WP isa (.block (grp ++ ceTail c b)) s fun s' => Inv s₀ d c b M (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hci : c * i + c ≤ 256 := by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega
  have hbi : b * i + b ≤ 32 * d := by
    have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega
  have hrd : s.rd ++ s.wr = [pR (fP s₀), ⟨oP s₀, 32 * d⟩] := by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, lenEq hp hdd]; rfl
  have hwr : s.wr = [⟨oP s₀, 32 * d⟩] := by rw [hI.wr, hp.2.1, lenEq hp hdd]
  have ha : ∀ j < c, s.gpr .rdi + BitVec.ofNat 64 (4 * j) = coeffAddr (fP s₀) (c * i + j) := fun j _ => by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hdj : Region.Disjoint (pR (fP s₀)) ⟨oP s₀, 32 * d⟩ := by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (hgrp i hi s ⟨fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, ?_⟩) fun s₁ ⟨w₁, k₁⟩ => ?_
  · rw [ha j hj, hrd]; exact ⟨_, by simp, coeff_contains _ (show c * i + j < 256 by omega)⟩
  · have hr : Reduced s₀.mem (fP s₀) := hp.2.2.2.2.2.2.2
    have hk : c * i + j < 256 := by omega
    rw [ha j hj, ← coeffAt_eq, coeff hp hdd hI.frame hk]
    have harg := (hcomp (F s₀)[c * i + j]!).1
    rw [polyAt_val hr hk] at harg
    rw [ceV_toNat hd11.2 (by rw [hI.r9]; exact harg), hI.r9, (hcomp _).2, polyAt_val hr hk]
  · rw [hwr, hI.r8, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_singleton_self _, contains_offset' (by omega) (by omega)⟩
  · rw [hI.rdi, hI.r8]
    exact (hdj.sub_left (sub_offset' (by rw [Nat.mul_assoc]; omega) (by decide))).sub_right
      (sub_offset' (by omega) (by omega))
  refine WP.mono (tail_ok c b (by omega) (by omega) s₁) fun s₂ ⟨⟨di₂, r8₂, cx₂, z₂, m₂⟩, k₂⟩ => ⟨?_, ?_, ?_⟩
  rotate_left
  · rw [cx₂, k₁.gpr (by decide)]
  · rw [z₂, k₁.gpr (by decide)]
  have hw : Written s.mem s₂.mem (oP s₀ + BitVec.ofNat 64 (b * i)) b
      fun k => (compressEncode d (F s₀))[b * i + k]! := by
    rw [m₂, ← hI.r8]; exact w₁
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hw hbi (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega)⟩
  · rw [di₂, k₁.gpr (by decide), hI.rdi]; exact ptr_step _ i (4 * c)
  · rw [r8₂, k₁.gpr (by decide), hI.r8]; exact ptr_step _ i b
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.r9]
  · rw [k₂.2.1, k₁.2.1, hI.rd]
  · rw [k₂.2.2, k₁.2.2, hI.wr]

include hcomp in
/-- The loop over the groups, each `grp`, with the multiplier `M`, from a
state with `f` in `rdi` and `out` in `r8`. -/
theorem loop_ok {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, GrpIn r d c b (F s₀) i s → WP isa (.block grp) s (GrpOut d b (F s₀) i s))
    (hM : M < 2 ^ 31) {s : State} (hdi : s.gpr .rdi = fP s₀) (h8 : s.gpr .r8 = oP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ceLoopW M (256 / c) (grp ++ ceTail c b)) s fun s' =>
      bytesAt s'.mem (oP s₀) (32 * d) = compressEncode d (F s₀) ∧ Frame [⟨oP s₀, 32 * d⟩] s₀.mem s'.mem := by
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun s' => s'.gpr .r9 = BitVec.ofNat 64 M ∧ s'.mem = s.mem)
    (by xrun [sx_ofNat hM]) (by rfl)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  have hN : 0 < 256 / c ∧ 256 / c ≤ 256 := ⟨Nat.div_pos (by omega) hc0, Nat.div_le_self _ _⟩
  refine WP.mono (wp_counted (N := 256 / c) (v := BitVec.ofNat 32 (256 / c))
    (by rw [BitVec.toNat_ofNat]; omega) (by omega) (Inv s₀ d c b M)
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega)⟩)
    fun i hi s hI => step hp hd11 hc0 hc8 hb hbN hcN hdd hcomp hgrp hi hI) fun s' hI => ⟨?_, hI.frame⟩
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), h8]; simp
  · rw [k₂.gpr (by decide), h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [k₂.2.1, k₁.2.1, hrd]
  · rw [k₂.2.2, k₁.2.2, hwr]
  · rw [m₂, m₁, hm]; exact Frame.refl _ _
  · exact bytesAt_eq! (compressEncode_length _ _) fun k hk => hI.done k (by omega)

end

/-- A group whose code accumulates its `c` values and stores its `b` bytes
(`d · c = 8 · b`). -/
theorem grp_ok {r d c b : Nat} (hr : r < 2 ^ 31) (hd11 : 1 ≤ d ∧ d ≤ 11) (hdc : d * c = 8 * b) (hb : b ≤ 7)
    (F : Poly) {i : Nat} (hci : c * i + c ≤ 256) (hbi : b * i + b ≤ 32 * d) {s : State} (h : GrpIn r d c b F i s) :
    WP isa (.block (ceAcc r d 0 c ++ ceSt 0 b)) s (GrpOut d b F i s) := by
  rw [WP.block_append_iff]
  refine WP.mono (ceAcc_ok (o := 0) (c := c) hr hd11.1 hd11.2 (by omega) s
    (fun j hj => by rw [Nat.zero_add]; exact h.rd j hj) (fun j => compress d F[c * i + (0 + j)]!)
    (fun j hj => by rw [Nat.zero_add]; exact h.v j hj) (fun _ _ => compress_lt d _)) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 0) (nb := b) (by omega) s₁ (fun k hk => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr k hk)) fun s₂ ⟨w₂, k₂⟩ =>
    ⟨?_, (k₁.trans k₂).mono (by decide)⟩
  rw [k₁.gpr (by decide), add_ofNat_zero, m₁, r₁] at w₂
  refine w₂.congr fun k hk => ?_
  rw [Spec.MlKem.compressEncode, byteEncode_group (c := c) (by omega) hdc (map_toList_lt _ (compress_lt d)) hk
    (by omega), take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [map_toList_getD _ _ (show c * i + j < 256 by have := List.mem_range.mp hj; omega), Nat.zero_add]

end CE

/-- `x - k` is zero exactly when `x = k`. -/
theorem sub_beq_zero32 (x k : BitVec 32) : (x - k == 0) = decide (x = k) := by
  by_cases h : x = k
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h; bv_omega

theorem cePrologue_ok (s₀ : State) :
    WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 1)]) s₀ fun s =>
      (s.gpr .rsi = BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.gpr .rsi)) ∧ s.gpr .r8 = s₀.gpr .rdx ∧
        s.zf = some (BitVec.setWidth 32 (s₀.gpr .rsi) - 1 == 0) ∧ s.mem = s₀.mem) ∧ Keep [.rsi, .r8] s₀ s := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem cmp32_ok (r : Reg) (k : BitVec 32) (s : State) :
    WP isa (.block [.alu32 .cmp r (.imm k)]) s fun s' =>
      (s'.zf = some (BitVec.setWidth 32 (s.gpr r) - k == 0) ∧ s'.mem = s.mem) ∧ Keep [r] s s' := by
  refine WP.keep _ ?_ (by cases r <;> rfl)
  xrun

theorem ce_wp {s₀ : State} (hp : compressEncodeK.pre s₀) :
    WP isa Impl.MlKem.X86_64.compressEncode s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [CE.lenEq hp rfl]
  unfold Impl.MlKem.X86_64.compressEncode
  refine WP.seq (WP.mono (cePrologue_ok s₀) fun s₁ ⟨⟨si₁, r8₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have go : ∀ {d c b : Nat}, d ∈ compressWidths → d * c = 8 * b → b ≤ 5 → 0 < c → c ≤ 8 →
      b * (256 / c) = 32 * d → c * (256 / c) = 256 → dArg s₀ .rsi = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rdx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (ceLoop d c b) s fun s' =>
        bytesAt s'.mem (s₀.gpr .rdx) (32 * dArg s₀ .rsi) = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
          Frame [⟨s₀.gpr .rdx, 32 * dArg s₀ .rsi⟩] s₀.mem s'.mem := by
    intro d c b hd hdc hb hc0 hc hbN hcN hdd s h1 h2 h3 h4 h5
    have hd11 : 1 ≤ d ∧ d ≤ 11 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    rw [hdd]
    exact CE.loop_ok hp hd11 hc0 hc (by omega) hbN hcN hdd (M := ceMul d) (r := 262080)
      (fun x => ⟨compress_arg_lt hd x, compress_eq hd x⟩)
      (fun i hi s hs => CE.grp_ok (by decide) hd11 hdc (by omega) _
        (by have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega)
        (by have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega) hs)
      (by rw [ceMul]; split <;> [decide; split <;> decide]) h1 h2 h3 h4 h5
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact go (d := 1) (c := 8) (b := 1) (by rw [← (show dArg s₀ .rsi = 1 by simp only [dArg, h]; rfl)]; exact hd)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp only [dArg, h]; rfl) s₁ di₁ r8₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (cmp32_ok .rsi 4 s₁) fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    rw [si₁, BitVec.setWidth_32_64_32] at z₂
    refine WP.ite (M := isa) _ (show isa.eval .e s₂ = _ from z₂) (fun h' => ?_) (fun h' => ?_)
    · rw [sub_beq_zero32, decide_eq_true_eq] at h'
      exact go (d := 4) (c := 2) (b := 1) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp only [dArg, h']; rfl) s₂ (by rw [k₂.gpr (by decide), di₁])
        (by rw [k₂.gpr (by decide), r8₁]) (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])
    · rw [sub_beq_zero32, decide_eq_false_iff_not] at h'
      have h10 : dArg s₀ .rsi = 10 := by
        rcases mem_compressWidths hd with e | e | e
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h'
        · exact e
      exact go (d := 10) (c := 4) (b := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        h10 s₂ (by rw [k₂.gpr (by decide), di₁])
        (by rw [k₂.gpr (by decide), r8₁]) (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])

theorem compressEncode_correct (s : State) (hs : compressEncodeK.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.compressEncode s t s' ∧ abiPreserved s s' ∧
      compressEncodeK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.compressEncode)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] (ce_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem compressEncode_ct :
    ConstantTime isa compressEncodeK.pre compressEncodeK.pub Impl.MlKem.X86_64.compressEncode :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def compressEncodeSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 32 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 32⟩]

theorem compressEncode_verified :
    Verified X86_64.target Impl.MlKem.X86_64.compressEncode (Spec.MlKem.compressEncodeContract X86_64.abi) :=
  Verified.of_correct compressEncode_correct compressEncode_ct (by
    mlkem_implies [Spec.MlKem.compressEncodeContract, Spec.MlKem.compressEncodeSig, compressEncodeK,
      X86_64.abi, X86_64.argRegs] [compressEncodeSat] using compressEncodeSat)

end VG.Proof.MlKem.X86_64
