import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Multiword arithmetic on x86-64: words to bytes

`storeBE` writes the `w` words of an array (`rbx`), each masked with `r15`
(0 or all ones, `mask c`), as `k` bytes most significant first at `rsi`:
I2OSP of the number if `c`, and zeros otherwise (`storeBE_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

theorem and_mask_toNat (x : BitVec 64) (c : Bool) : (x &&& mask c).toNat = if c then x.toNat else 0 := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes]; rfl

theorem shr8_toNat (x : BitVec 64) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A word of a number of `w` words. -/
theorem word_of_wv (m : Mem) (B : Addr) (ed w : Nat) {q : Nat} (hq : q < w) :
    (word m B (ed + 8 * q)).toNat = wv m B ed w / 2 ^ (64 * q) % 2 ^ 64 := by
  have h := wv_add m B ed q (w - q)
  rw [show q + (w - q) = w by omega] at h
  obtain ⟨r, hr⟩ : ∃ r, w - q = r + 1 := ⟨w - q - 1, by omega⟩
  rw [hr, show r + 1 = 1 + r by omega, wv_add, show (wv m B (ed + 8 * q) 1) = (word m B (ed + 8 * q)).toNat
    by simp [wv]] at h
  rw [h]
  have hl := wv_lt m B ed q
  have hw := (word m B (ed + 8 * q)).isLt
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl, Nat.zero_add,
    show 64 * 1 = 64 from rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]

theorem out_ne {out : Addr} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    out + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j := by
  intro he
  apply h
  have h2 : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
    have := congrArg (fun x => x - out) he
    simpa only [Offset.add_sub_cancel_left] using this
  have := congrArg BitVec.toNat h2
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

/-- After `p` bytes of `storeBE` from `s`: the bytes `k - 1 - j` for `j < p`
are the bytes `j` of `Y_m` (the number, or 0, by the mask), and `rax`
holds what is left of the current word. -/
structure SInv (s : State) (out : Addr) (k : Nat) (Ym : Nat) (p : Nat) (t : State) : Prop where
  wr : t.wr = s.wr
  rd : t.rd = s.rd
  keep : Keep [.rax, .rdx, .rbp, .r14] s t
  rdx : t.gpr .rdx = BitVec.ofNat 64 p
  r14 : t.gpr .r14 = out + BitVec.ofNat 64 (k - p)
  rax : p % 8 ≠ 0 → (t.gpr .rax).toNat = Ym / 256 ^ p % 256 ^ (8 - p % 8)
  bytes : ∀ j < p, t.mem (out + BitVec.ofNat 64 (k - 1 - j)) = BitVec.ofNat 8 (Ym / 256 ^ j)
  frame : ∀ x, (∀ j < p, x ≠ out + BitVec.ofNat 64 (k - 1 - j)) → t.mem x = s.mem x

theorem storeStep_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B ed) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (h15 : s.gpr .r15 = mask c) (hk' : k < 2 ^ 31) (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j))
    {p : Nat} (hp : p < k) {t : State}
    (hI : SInv s out k (if c then wv s.mem B ed w else 0) p t) :
    WP isa (.seq (.block [.mov .rbp (.reg .rdx), .alu .and .rbp (.imm 7)])
      (.seq (.ite .e (.block [.mov .rbp (.reg .rdx), .shift .shr .rbp 3, .mov .rax (.mem (ix .rbx .rbp)),
          .alu .and .rax (.reg .r15)]) (.block []))
        (.block [.alu .sub .r14 (.imm 1), .store8 (at0 .r14) .rax, .shift .shr .rax 8,
          .alu .add .rdx (.imm 1), .alu .cmp .rdx (.reg .rcx)]))) t fun t' =>
      t'.zf = some (decide (p + 1 = k)) ∧ SInv s out k (if c then wv s.mem B ed w else 0) (p + 1) t' := by
  have hn := hs.nowrap
  set Ym := if c then wv s.mem B ed w else 0 with hYm
  have tbx : t.gpr .rbx = off B ed := (hI.keep.gpr (by decide)).trans hbx
  have tcx : t.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  have t15 : t.gpr .r15 = mask c := (hI.keep.gpr (by decide)).trans h15
  have hts : Scr t B Z := hs.congr hI.wr
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t₁ => t₁.zf = some (decide (p % 8 = 0)) ∧ t₁.mem = t.mem)
    (by xrun [hI.rdx, sx7, and7_eq p (by omega)]) rfl) fun t₁ ⟨⟨hz₁, hm₁⟩, k₁⟩ => ?_)
  -- After the optional load: `rax` holds bytes `p, …` of `Y_m` up to the word's end.
  have hload : WP isa (.ite .e (.block [.mov .rbp (.reg .rdx), .shift .shr .rbp 3,
      .mov .rax (.mem (ix .rbx .rbp)), .alu .and .rax (.reg .r15)]) (.block [])) t₁ fun t₂ =>
      (t₂.gpr .rax).toNat = Ym / 256 ^ p % 256 ^ (8 - p % 8) ∧ t₂.mem = t.mem ∧
      Keep [.rax, .rbp] t₁ t₂ := by
    by_cases hz : p % 8 = 0
    · refine WP.ite true (by simp [eval, hz₁, hz]) (fun _ => ?_) (by simp)
      have t₁dx : t₁.gpr .rdx = BitVec.ofNat 64 p := (k₁.gpr (by decide)).trans hI.rdx
      have t₁bx : t₁.gpr .rbx = off B ed := (k₁.gpr (by decide)).trans tbx
      have t₁15 : t₁.gpr .r15 = mask c := (k₁.gpr (by decide)).trans t15
      have hq : p / 8 < w := by omega
      have hwd : word t₁.mem B (ed + 8 * (p / 8)) = word s.mem B (ed + 8 * (p / 8)) := by
        rw [hm₁]
        exact Mem.readW_congr fun i hi => (hI.frame _ fun j hj => by
          intro he
          have h1 := hsep (k - 1 - j) (by omega)
          rw [← he, ofs_off B (by omega)] at h1
          omega).symm |>.symm
      refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₂ =>
          t₂.gpr .rax = word s.mem B (ed + 8 * (p / 8)) &&& mask c ∧ t₂.mem = t₁.mem) (by
        xrun [State.ea, ix, t₁dx, shr3_eq p (by omega), addr0 t₁bx rfl, t₁15,
          (by rw [k₁.2.1, k₁.2.2, hI.rd, hI.wr]; exact hs.ld (show ed + 8 * (p / 8) + 8 ≤ Z by omega) :
            InRegions (t₁.rd ++ t₁.wr) (off B (ed + 8 * (p / 8))) 8), hwd]) rfl)
        fun t₂ ⟨⟨hax, hm₂⟩, k₂⟩ => ⟨?_, hm₂.trans hm₁, k₂⟩
      rw [hax, and_mask_toNat, word_of_wv _ _ _ _ hq, show 8 - p % 8 = 8 by omega, VG.Proof.Bignum.pow256_8,
        show 64 * (p / 8) = 8 * p by omega, show (256 : Nat) ^ p = 2 ^ (8 * p) by
          rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]]
      simp only [hYm]
      cases c <;> simp
    · refine WP.ite false (by simp [eval, hz₁, hz]) (by simp) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [(k₁.gpr (by decide) : t₁.gpr .rax = t.gpr .rax)]; exact hI.rax hz, hm₁, Keep.refl _ _⟩
  refine WP.seq (WP.mono hload fun t₂ ⟨hax₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have t₂14 : t₂.gpr .r14 = out + BitVec.ofNat 64 (k - p) := (k12.gpr (by decide)).trans hI.r14
  have t₂dx : t₂.gpr .rdx = BitVec.ofNat 64 p := (k12.gpr (by decide)).trans hI.rdx
  have t₂cx : t₂.gpr .rcx = BitVec.ofNat 64 k := (k12.gpr (by decide)).trans tcx
  have e14 : out + BitVec.ofNat 64 (k - p) - 1 = out + BitVec.ofNat 64 (k - 1 - p) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_ofNat_sub out (by omega),
      show k - p - 1 = k - 1 - p by omega]
  have hst : InRegions t₂.wr (out + BitVec.ofNat 64 (k - 1 - p)) 1 := by
    rw [k12.2.2, hI.wr]; exact hout _ (by omega)
  refine WP.mono (WP.keep [.rax, .rdx, .r14] (Q := fun t' =>
      t'.mem = t₂.mem.writeW (out + BitVec.ofNat 64 (k - 1 - p)) ((t₂.gpr .rax).setWidth 8) ∧
      t'.gpr .rax = t₂.gpr .rax >>> 8 ∧ t'.gpr .rdx = BitVec.ofNat 64 (p + 1) ∧
      t'.gpr .r14 = out + BitVec.ofNat 64 (k - 1 - p) ∧ t'.zf = some (decide (p + 1 = k))) (by
    xrun [State.ea, at0, t₂14, t₂dx, t₂cx, e14, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst,
      ofNat_add_one, ofNat_sub_beq (show p + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hax', hdx', h14', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  have hbyte : (t₂.gpr .rax).setWidth 8 = BitVec.ofNat 8 (Ym / 256 ^ p) := by
    rw [← BitVec.ofNat_toNat, hax₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Dvd.intro_left
      (256 ^ (8 - p % 8 - 1)) (by rw [← Nat.pow_succ]; congr 1; omega))]
  refine ⟨k'.2.2.trans (k12.2.2.trans hI.wr), k'.2.1.trans (k12.2.1.trans hI.rd),
    ((hI.keep.trans k12).trans k').mono (by decide), hdx', by rw [h14']; congr 2; omega, ?_, ?_, ?_⟩
  · intro hz
    rw [hax', shr8_toNat, hax₂, show 8 - p % 8 = 1 + (8 - (p + 1) % 8) by omega, Nat.pow_add,
      Nat.pow_one, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · intro j hj
    rw [hm', hm₂, writeW8_apply]
    by_cases hjp : j = p
    · subst hjp; simp [hbyte]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (by omega)))]
      exact hI.bytes j (by omega)
  · intro x hx
    rw [hm', hm₂, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx p (by omega)))]
    exact hI.frame x fun j hj => hx j (by omega)

/-- `storeBE`: the number at `rbx` (`w` words), masked by `r15 = mask c`, as
`k` bytes at `rsi`, most significant first: I2OSP of it, or of 0. -/
theorem storeBE_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B ed) (hsi : s.gpr .rsi = out)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (h15 : s.gpr .r15 = mask c) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa storeBE s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ Keep [.rax, .rdx, .rbp, .r14] s t := by
  unfold storeBE
  refine WP.seq (WP.mono (WP.keep [.rdx, .r14] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 0 ∧
      t.gpr .r14 = out + BitVec.ofNat 64 k ∧ t.mem = s.mem) (by xrun [hsi, hcx]) rfl)
    fun s₁ ⟨⟨hdx, h14, hm₁⟩, k₁⟩ => ?_)
  refine wp_upto (a := 0) (N := k) (by omega) (SInv s out k (if c then wv s.mem B ed w else 0)) ?_
    (fun t hI => ⟨?_, ?_, hI.wr, hI.rd, hI.keep⟩)
    ⟨k₁.2.2, k₁.2.1, k₁.mono (by decide), hdx, by rw [h14, Nat.sub_zero], fun h => absurd rfl h,
      fun j hj => absurd hj (by omega), fun x _ => by rw [hm₁]⟩
  · intro p _ hp t hI
    exact storeStep_ok hs hbx hcx h15 hk' hw hed hout hsep hp hI
  · apply List.ext_getElem (by simp [Spec.Rsa.i2osp])
    intro i h1 h2
    have hik : i < k := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Spec.Rsa.i2osp]
    have := hI.bytes (k - 1 - i) (by omega)
    rwa [show k - 1 - (k - 1 - i) = i by omega] at this
  · intro x hx
    exact hI.frame x fun j hj => hx _ (by omega)

end VG.Proof.Bignum.X86_64
