import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# `vg_rsa_public_precompute` on x86-64: the computation for a valid modulus

`main`, from the header that `entry` leaves, for a valid modulus `m` of `w`
words: `m` and `R² mod m` to `pre`, 1 returned, and the saved registers
restored (`pcMain_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- `m` into its array, and `-m⁻¹`. -/
def pcLoad : List (Prog isa) := [.block head, loadBE,
  .block ([.mov .r10 (.reg .rbx), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .rbx))] ++
    minv ++ [.store (hdr sMinv) .r15])]

/-- `m` and `R² mod m` to `pre`, and 1 returned. -/
def pcOut : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))), .mov .rbx (.mem (hdr sOut))],
  copyWords,
  .block (eightW ++ [.alu .add .rbx (.reg .rax), .mov .rsi (.mem (hdr (sArr aR2)))]),
  copyWords,
  .block ([.mov32 .rax (.imm 1)] ++ exit)]

theorem seqs_one (c : Prog isa) : seqs [c] = c := rfl

theorem pcMain_eq : Precompute.main = seqs (pcLoad ++ (r2Steps ++ pcOut)) := rfl

/-- What the load changes. -/
def pcLoadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (8 * sMinv, 8)]

theorem pcLoadRanges_fixed (w : Nat) :
    ∀ r ∈ pcLoadRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h1 : slot w 0 ≤ slot w aN := by unfold slot; omega
  simp only [pcLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv] at * <;> omega

theorem pcLoadRanges_le (w : Nat) : ∀ r ∈ pcLoadRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  simp only [pcLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv] at * <;> omega

/-- The load: `w`, the bases, `m`, and `-m⁻¹` for the odd `m`. -/
theorem pcLoad_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hnb : Src s B Z np nb) (hnl : nb.length = k) (hodd : Spec.Rsa.os2ip nb % 2 = 1) :
    WP isa (seqs pcLoad) s fun t => ∃ minv, Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      ((word t.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .r10 = off B (slot ((k + 7) / 8) aN) ∧
      Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have hsl : ∀ r ∈ pcLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr =>
    (pcLoadRanges_le _ r hr).trans hZ
  unfold pcLoad
  refine WP.seq (WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN)
    fun t₁ ⟨h12, hcx, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [pcLoadRanges])
  refine WP.seq (WP.mono (loadArr_ok hs₁ (by decide) hZ (hnb.congrK (InScr.of_frm hf₁' hsl) k₁) hnl (by omega)
    hk hsi hcx hbx) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hf₂ : Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays1 ha₂ (by simp [pcLoadRanges]))
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have hb₂ : ∀ j < 8, word t₂.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ha₂.hslot (by decide)]; exact hW₁
  have hodd₀ : (word t₂.mem B (slot ((k + 7) / 8) aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ (k + 7) / 8 by omega), Nat.mod_mod_of_dvd _ (by decide), hv₂, hodd]
  have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  have hbx₂ : t₂.gpr .rbx = off B (slot ((k + 7) / 8) aN) := (k₂.gpr (by decide)).trans hbx
  rw [seqs_one, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r10, .r12, .rbx] (Q := fun t => t.gpr .r10 = off B (slot ((k + 7) / 8) aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .rbx = word t₂.mem B (slot ((k + 7) / 8) aN) ∧
      t.mem = t₂.mem) (by
    xrun [State.ea, hdr, at0, hdi₂, hdrOff, hl sW (by decide), hbx₂, hW₂,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs₂.ld (d := slot ((k + 7) / 8) aN) (by omega)])
    rfl) fun t₃ ⟨⟨h10₃, h12₃, hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [hbx₃] at hinv
  have hs₄ := (hs₂.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by omega)]) rfl) fun t ⟨hm, k₅⟩ => ?_
  have hm' : t.mem = t₂.mem.writeW (off B (8 * sMinv)) (t₄.gpr .r15) := by rw [hm, hm₄, hm₃]
  have hwo : Outside B (8 * sMinv) 8 t₂.mem t.mem := by rw [hm']; exact writeW_outside _ B _ (by omega)
  refine ⟨t₄.gpr .r15, ⟨hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄, ⟨?_, ?_, fun j hj => ?_⟩⟩, ?_, ?_,
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h12₃),
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10₃),
    hf₂.trans (Frm.of_outside hwo (by simp [pcLoadRanges])),
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [hwo.word (by omega) (by omega)]; exact hW₂
  · rw [hm', word_writeW_self]
  · rw [hwo.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega)]; exact hb₂ j hj
  · rw [hwo.wv (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega) (by omega)]
    exact hv₂
  · rw [hwo.word (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega) (by omega)]
    exact hinv

/-! ## The result to `pre` -/

/-- An address outside the working space is past the `n` bytes of a buffer
outside it, from that buffer's start. -/
theorem le_ofs_of_sep {B op x : Addr} {Z n : Nat} (hsep : ∀ i < n, Z ≤ ofs B (op + BitVec.ofNat 64 i))
    (hx : ofs B x < Z) : n ≤ ofs op x := by
  rcases Nat.lt_or_ge (ofs op x) n with h | h
  · have := hsep (ofs op x) h
    rw [show op + BitVec.ofNat 64 (ofs op x) = x by
      rw [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]] at this
    omega
  · exact h

/-- A word of a number, as `toWords` gives it. -/
theorem word_eq_ofNat (m : Mem) (B : Addr) (ed w : Nat) {q : Nat} (hq : q < w) :
    word m B (ed + 8 * q) = BitVec.ofNat 64 (wv m B ed w / 2 ^ (64 * q)) := by
  apply BitVec.eq_of_toNat_eq
  rw [word_of_wv m B ed w hq, BitVec.toNat_ofNat]

/-- The `2 w` words at `op`: two numbers of `w` words. -/
theorem wordsAt_two {m : Mem} {op : Addr} {w : Nat} {x y : Nat}
    (hx : ∀ i < w, word m op (8 * i) = BitVec.ofNat 64 (x / 2 ^ (64 * i)))
    (hy : ∀ i < w, word m op (8 * w + 8 * i) = BitVec.ofNat 64 (y / 2 ^ (64 * i))) :
    Spec.Rsa.wordsAt m op (2 * w) = Spec.Rsa.toWords x w ++ Spec.Rsa.toWords y w := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, show 2 * w = w + w by omega, List.range_add,
    List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun i hi => hx i (List.mem_range.mp hi)
  · refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply]
    rw [show 8 * (w + i) = 8 * w + 8 * i by omega]
    exact hy i (List.mem_range.mp hi)

/-- What `main` (and `fail`) leave: the words `ws` to `pre`, the flag `c`
returned, the saved registers restored, and memory outside the working space
and `pre` unchanged. -/
structure PcPost (s t : State) (B : Addr) (Z w : Nat) (op : Addr) (ws : List (BitVec 64)) (c : Bool) :
    Prop where
  words : Spec.Rsa.wordsAt t.mem op (2 * w) = ws
  rax : t.gpr .rax = BitVec.ofNat 64 c.toNat
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, Z ≤ ofs B x → 16 * w ≤ ofs op x → t.mem x = s.mem x
  keep : Keep mmRegs s t

/-- `pcOut`: the arrays of `m` and `R² mod m` to `pre`, 1 returned, and the
saved registers restored. -/
theorem pcOut_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {op : Addr} {N R : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30)
    (hO : word s.mem B (8 * sOut) = op) (hn : wv s.mem B (slot w aN) w = N)
    (hr : wv s.mem B (slot w aR2) w = R)
    (hpw : ∀ i < 2 * w, InRegions s.wr (off op (8 * i)) 8)
    (hps : ∀ i < 16 * w, Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa (seqs pcOut) s fun t => PcPost s t B Z w op (Spec.Rsa.toWords N w ++ Spec.Rsa.toWords R w) true := by
  have hs := hg.scr
  have hnw := hs.nowrap
  have h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := w) (show 0 < 8 by decide)
  have hsN := slot_le (w := w) (show aN < 8 by decide)
  have hsR := slot_le (w := w) (show aR2 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  -- A byte of the working space is past `pre`'s `16 w` bytes.
  have hsep : ∀ x, ofs B x < Z → 16 * w ≤ ofs op x := fun x hx => le_ofs_of_sep hps hx
  have hsepw : ∀ e, e + 8 * w ≤ Z → ∀ j < w, ∀ b < 8,
      16 * w ≤ ofs op (off B (e + 8 * j) + BitVec.ofNat 64 b) := fun e he j hj b hb =>
    hsep _ (by rw [ofs_off B (by omega)]; omega)
  unfold pcOut
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w aN) ∧ t.gpr .rbx = off op 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hl sOut (by decide),
      hg.hdr.hw, hg.hdr.harr aN (by decide), hO]) rfl) fun t₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyWords_ok hsi hbx h12 hw (by omega) (by omega)
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact hs.ld (by omega))
    (fun j hj => by rw [k₁.2.2, Nat.zero_add]; exact hpw j (by omega))
    (fun j hj b hb => Or.inr (by have := hsepw (slot w aN) (by omega) j hj b hb; omega)))
    fun t₂ ⟨_, hc₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at hc₂ ho₂
  -- The working space is as it was.
  have hin₂ : ∀ x, ofs B x < Z → t₂.mem x = s.mem x := fun x hx =>
    ho₂ x (Or.inr (by have := hsep x hx; omega))
  have hword₂ : ∀ d, d + 8 ≤ Z → word t₂.mem B d = word s.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hin₂ _ (by rw [ofs_off B (d := d) (i := b) (by omega)]; omega)
  have k12 := k₁.trans k₂
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hbx₂ : t₂.gpr .rbx = op := by rw [(k₂.gpr (by decide)).trans hbx]; simp [off]
  have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 w → r + r + (r + r) + (r + r + (r + r)) =
      BitVec.ofNat 64 (8 * w) := by
    rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
  refine WP.seq (WP.mono (WP.keep [.rax, .rbx, .rsi] (Q := fun t => t.gpr .rbx = off op (8 * w) ∧
      t.gpr .rsi = off B (slot w aR2) ∧ t.mem = t₂.mem) (by
    unfold eightW
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ (sArr aR2) (by decide), hword₂ _ (show 8 * sArr aR2 + 8 ≤ Z by
      unfold sArr aR2; omega), hg.hdr.harr aR2 (by decide), h12₂, hbx₂, hax8 _ rfl]) rfl)
    fun t₃ ⟨⟨hbx₃, hsi₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans h12₂
  refine WP.seq (WP.mono (copyWords_ok hsi₃ hbx₃ h12₃ hw (by omega) (by omega)
    (fun j hj => by rw [k13.2.1, k13.2.2]; exact hs.ld (by omega))
    (fun j hj => by
      rw [k13.2.2, show 8 * w + 8 * j = 8 * (w + j) by omega]; exact hpw (w + j) (by omega))
    (fun j hj b hb => Or.inr (by have := hsepw (slot w aR2) (by omega) j hj b hb; omega)))
    fun t₄ ⟨_, hc₄, ho₄, k₄⟩ => ?_)
  rw [hm₃] at hc₄ ho₄
  have hin₄ : ∀ x, ofs B x < Z → t₄.mem x = s.mem x := fun x hx =>
    (ho₄ x (Or.inr (by have := hsep x hx; omega))).trans (hin₂ x hx)
  have hword₄ : ∀ d, d + 8 ≤ Z → word t₄.mem B d = word s.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hin₄ _ (by rw [ofs_off B (d := d) (i := b) (by omega)]; omega)
  have k14 := k13.trans k₄
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans hg.rdi
  have hl₄ : ∀ i < 32, InRegions (t₄.rd ++ t₄.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k14.2.1, k14.2.2]; exact hl i hi
  rw [seqs_one, exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₄.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₄, hdrOff, hl₄ 0 (by decide), hl₄ 1 (by decide), hl₄ 2 (by decide),
      hl₄ 3 (by decide), hl₄ 4 (by decide), hl₄ 5 (by decide), hword₄ (8 * 0) (by omega),
      hword₄ (8 * 1) (by omega), hword₄ (8 * 2) (by omega), hword₄ (8 * 3) (by omega),
      hword₄ (8 * 4) (by omega), hword₄ (8 * 5) (by omega)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₅⟩ => ⟨?_, hax, ?_, ?_, (k14.trans k₅).mono (by decide)⟩
  · rw [hm]
    refine wordsAt_two (fun i hi => ?_) (fun i hi => ?_)
    · have h := hc₂ i hi
      rw [Nat.zero_add] at h
      rw [ho₄.word (by omega) (by omega), h, ← hn]
      exact word_eq_ofNat _ _ _ _ hi
    · rw [hc₄ i hi, hword₂ _ (by omega), ← hr]
      exact word_eq_ofNat _ _ _ _ hi
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm, ho₄ x (Or.inr (by omega)), ho₂ x (Or.inr (by omega))]

/-- The precomputed values of a valid modulus. -/
theorem publicPrecompute_some {nb : List Byte} {k : Nat} (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.toWords (Spec.Rsa.os2ip nb) ((k + 7) / 8) ++
      Spec.Rsa.toWords (2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb) ((k + 7) / 8)) := by
  simp only [Spec.Rsa.publicPrecompute, hnl, hv, ite_true]; rfl

/-- `main`, for a valid modulus `m`: `m` and `R² mod m` to `pre`, and 1
returned. -/
theorem pcMain_ok {s : State} {B : Addr} {Z k : Nat} {op np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hO : word s.mem B (8 * sOut) = op) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hN : word s.mem B (8 * sN) = np) (hnb : Src s B Z np nb) (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hpw : ∀ i < 2 * ((k + 7) / 8), InRegions s.wr (off op (8 * i)) 8)
    (hps : ∀ i < 16 * ((k + 7) / 8), Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa Precompute.main s fun t => ∃ ws, Spec.Rsa.publicPrecompute nb = some ws ∧
      PcPost s t B Z ((k + 7) / 8) op ws true := by
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv hk1
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  rw [pcMain_eq]
  refine wp_seqs_append (by simp [pcLoad]) (by simp [r2Steps])
    (WP.mono (pcLoad_ok hs hdi hZ (by omega) (by omega) hK hN hnb hnl hodd)
      fun t₁ ⟨minv, hg₁, hn₁, hinv₁, h12₁, h10₁, f₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [r2Steps]) (by simp [pcOut])
    (WP.mono (r2_ok hg₁ hZ (by omega) (by omega) hn₁ hinv₁ h12₁ h10₁ hodd hlo)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have x₁₂ := (Fixed.of_frm f₁ (pcLoadRanges_fixed _)).trans (Fixed.of_frm f₂ (r2Ranges_fixed _))
  have i₁₂ : InScr B Z s.mem t₂.mem := (InScr.of_frm f₁ fun r hr => (pcLoadRanges_le _ r hr).trans hZ).trans
    (InScr.of_frm f₂ fun r hr => (r2Ranges_le _ r hr).trans hZ)
  have k₁₂ := k₁.trans k₂
  have hR : wv t₂.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) =
      2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    rw [← Nat.mod_eq_of_lt hlt₂, hr₂, ← Nat.pow_add]; congr 2; omega
  refine WP.mono (pcOut_ok hg₂ hZ (by omega) (by omega) (by rw [x₁₂ sOut (by decide)]; exact hO)
    (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hn₁) hR
    (fun i hi => by rw [k₁₂.2.2]; exact hpw i hi) hps)
    fun t hp => ⟨_, publicPrecompute_some hnl hv, hp.words, hp.rax,
      fun i hi => by rw [hp.saved i hi]; exact x₁₂ i (by omega),
      fun x hx hx' => by rw [hp.frame x hx hx', i₁₂ x hx], (k₁₂.trans hp.keep).mono (by decide)⟩

end VG.Proof.Bignum.X86_64
