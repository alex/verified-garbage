import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base

/-!
# Interleaved counter mode and GHASH: the GHASH loads

`ghLoad_ok`: `ghLoad k` loads the `k`-th pair of powers from the working
space into `ymm12`, and then does what `vg_ghash_vpclmul`'s `k`-th load does
(`Vpclmul.load_ok`). The products after the loads of a body, in the order of
an encryption body (`ordE`: the product with `Y` last) or of a decryption
body (`ordD`), are `accN`; reduced, the two lanes' add up to `GHASH` over the
sixteen blocks (`finE`, `finD`).
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce φ_reduce prod)
open VG.Proof.Gcm.X86_64.Vpclmul (restV ldacc load_ok step16 load256_lo load256_hi)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (ghLoad ordE ordD)
open VG.Spec.Gcm (Block blockAt mul)

theorem lane_ld12 {k : Nat} (hk : k < 8) :
    laneSseBlock (restV k .xmm12) = some (ldacc (decide (k = 0)) .xmm12) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The `k`-th pair of powers into `ymm12`, and blocks `2k` and `2k + 1` at
`rdx + 32 k` added to the lanes' products with them. -/
theorem ghLoad_ok {k : Nat} (hk : k < 8) (t : State) (h0 : ∀ l < 2, t.lane .xmm0 l = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32) :
    WP isa (.block (ghLoad k)) t fun t' =>
      (∀ l < 2, prod (t'.proj l) = (prod (t.proj l)).acc
        ((if k = 0 then t.lane .xmm2 l else 0) ^^^
          blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let a := t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)
  let v := t.mem.readW a 256
  let t₁ := t.setV .l256 .xmm12 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [ghLoad, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load256, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hpin, ite_true,
    Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → ∀ l < 2, t₁.lane r l = t.lane r l := fun r hr l _ => by
    simp [t₁, State.lane_setV256, hr]
  have l12 : ∀ l < 2, t₁.lane .xmm12 l = t.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [t₁, State.lane_setV256, v, load256_lo]
    · simp [t₁, State.lane_setV256, v, load256_hi]
  refine WP.mono (load_ok (lane_ld12 hk) (by decide) t₁ (fun l hl => by rw [keep _ (by decide) l hl]; exact h0 l hl)
    (by simpa [t₁] using hin)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [p' l hl, l12 l hl, keep _ (by decide) l hl]
    have hp : prod (t₁.proj l) = prod (t.proj l) := by
      simp only [prod, State.proj_xmm, keep .xmm8 (by decide) l hl, keep .xmm9 (by decide) l hl,
        keep .xmm10 (by decide) l hl]
    rw [hp]; rfl
  · refine ⟨f'.gpr, f'.mem, f'.rd, f'.wr, fun r hr l hl => ?_⟩
    rw [f'.lane r (fun h => hr (List.mem_cons_of_mem _ h)) l hl, keep r (fun h => hr (h ▸ List.mem_cons_self)) l hl]

/-! ## The products of a body -/

/-- The input of the `k`-th load in lane `l`: block `2k + l`, with `Y` (`yl l`)
added to block 0. -/
def inp (X : Nat → Block) (yl : Nat → Block) (k l : Nat) : Block := (if k = 0 then yl l else 0) ^^^ X (2 * k + l)

/-- The products of lane `l` after the first `n` loads, in the order `ord`. -/
def accN (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) : Prod :=
  (List.range n).foldl (fun p i => p.acc (inp X yl (ord i) l) (P (ord i) l)) Prod.zero

theorem accN_zero (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l : Nat) :
    accN ord X P yl l 0 = Prod.zero := rfl

theorem accN_succ (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) :
    accN ord X P yl l (n + 1) = (accN ord X P yl l n).acc (inp X yl (ord n) l) (P (ord n) l) := by
  simp only [accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Sixteen blocks, in `Q`, the products in the order of a decryption body. -/
theorem step16D (H Y X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂ X₁₃ X₁₄ X₁₅ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ T₁₀ T₁₁ T₁₂ T₁₃ T₁₄ T₁₅ T₁₆ : Block)
    (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3) (h₄ : x * φ T₄ = φ H ^ 4) (h₅ : x * φ T₅ = φ H ^ 5) (h₆ : x * φ T₆ = φ H ^ 6) (h₇ : x * φ T₇ = φ H ^ 7) (h₈ : x * φ T₈ = φ H ^ 8) (h₉ : x * φ T₉ = φ H ^ 9) (h₁₀ : x * φ T₁₀ = φ H ^ 10) (h₁₁ : x * φ T₁₁ = φ H ^ 11) (h₁₂ : x * φ T₁₂ = φ H ^ 12) (h₁₃ : x * φ T₁₃ = φ H ^ 13) (h₁₄ : x * φ T₁₄ = φ H ^ 14) (h₁₅ : x * φ T₁₅ = φ H ^ 15) (h₁₆ : x * φ T₁₆ = φ H ^ 16) :
    reduce ((((((((Prod.zero.acc X₂ T₁₄).acc X₄ T₁₂).acc X₆ T₁₀).acc (Y ^^^ X₀) T₁₆).acc X₈ T₈).acc X₁₀ T₆).acc X₁₂ T₄).acc X₁₄ T₂) ^^^
        reduce ((((((((Prod.zero.acc X₃ T₁₃).acc X₅ T₁₁).acc X₇ T₉).acc X₁ T₁₅).acc X₉ T₇).acc X₁₁ T₅).acc X₁₃ T₃).acc X₁₅ T₁) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((Y ^^^ X₀)) H ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H ^^^ X₅) H ^^^ X₆) H ^^^ X₇) H ^^^ X₈) H ^^^ X₉) H ^^^ X₁₀) H ^^^ X₁₁) H ^^^ X₁₂) H ^^^ X₁₃) H ^^^ X₁₄) H ^^^ X₁₅) H := by
  apply φ_inj
  simp only [φ_xor, φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul]
  linear_combination (φ Y + φ X₀) * h₁₆ + φ X₁ * h₁₅ + φ X₂ * h₁₄ + φ X₃ * h₁₃ + φ X₄ * h₁₂ + φ X₅ * h₁₁ + φ X₆ * h₁₀ + φ X₇ * h₉ + φ X₈ * h₈ + φ X₉ * h₇ + φ X₁₀ * h₆ + φ X₁₁ * h₅ + φ X₁₂ * h₄ + φ X₁₃ * h₃ + φ X₁₄ * h₂ + φ X₁₅ * h₁

theorem zero_xor_b (a : Block) : (0 : Block) ^^^ a = a := by simp

/-- The two lanes' products of an encryption body, reduced and added: `GHASH`
over the sixteen blocks. -/
theorem finE (H : Block) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (hy1 : yl 1 = 0)
    (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) :
    reduce (accN ordE X P yl 0 8) ^^^ reduce (accN ordE X P yl 1 8) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H := by
  have h₁ := hP 7 (by decide) 1 (by decide)
  rw [show 16 - 2 * 7 - 1 = 1 from rfl, pow_one] at h₁
  have h₂ := hP 7 (by decide) 0 (by decide)
  rw [show 16 - 2 * 7 - 0 = 2 from rfl] at h₂
  have h₃ := hP 6 (by decide) 1 (by decide)
  rw [show 16 - 2 * 6 - 1 = 3 from rfl] at h₃
  have h₄ := hP 6 (by decide) 0 (by decide)
  rw [show 16 - 2 * 6 - 0 = 4 from rfl] at h₄
  have h₅ := hP 5 (by decide) 1 (by decide)
  rw [show 16 - 2 * 5 - 1 = 5 from rfl] at h₅
  have h₆ := hP 5 (by decide) 0 (by decide)
  rw [show 16 - 2 * 5 - 0 = 6 from rfl] at h₆
  have h₇ := hP 4 (by decide) 1 (by decide)
  rw [show 16 - 2 * 4 - 1 = 7 from rfl] at h₇
  have h₈ := hP 4 (by decide) 0 (by decide)
  rw [show 16 - 2 * 4 - 0 = 8 from rfl] at h₈
  have h₉ := hP 3 (by decide) 1 (by decide)
  rw [show 16 - 2 * 3 - 1 = 9 from rfl] at h₉
  have h₁₀ := hP 3 (by decide) 0 (by decide)
  rw [show 16 - 2 * 3 - 0 = 10 from rfl] at h₁₀
  have h₁₁ := hP 2 (by decide) 1 (by decide)
  rw [show 16 - 2 * 2 - 1 = 11 from rfl] at h₁₁
  have h₁₂ := hP 2 (by decide) 0 (by decide)
  rw [show 16 - 2 * 2 - 0 = 12 from rfl] at h₁₂
  have h₁₃ := hP 1 (by decide) 1 (by decide)
  rw [show 16 - 2 * 1 - 1 = 13 from rfl] at h₁₃
  have h₁₄ := hP 1 (by decide) 0 (by decide)
  rw [show 16 - 2 * 1 - 0 = 14 from rfl] at h₁₄
  have h₁₅ := hP 0 (by decide) 1 (by decide)
  rw [show 16 - 2 * 0 - 1 = 15 from rfl] at h₁₅
  have h₁₆ := hP 0 (by decide) 0 (by decide)
  rw [show 16 - 2 * 0 - 0 = 16 from rfl] at h₁₆
  simp only [accN, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ordE, inp, hy1, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero, zero_xor_b]
  exact step16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆

/-- The same for a decryption body. -/
theorem finD (H : Block) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (hy1 : yl 1 = 0)
    (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) :
    reduce (accN ordD X P yl 0 8) ^^^ reduce (accN ordD X P yl 1 8) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H := by
  have h₁ := hP 7 (by decide) 1 (by decide)
  rw [show 16 - 2 * 7 - 1 = 1 from rfl, pow_one] at h₁
  have h₂ := hP 7 (by decide) 0 (by decide)
  rw [show 16 - 2 * 7 - 0 = 2 from rfl] at h₂
  have h₃ := hP 6 (by decide) 1 (by decide)
  rw [show 16 - 2 * 6 - 1 = 3 from rfl] at h₃
  have h₄ := hP 6 (by decide) 0 (by decide)
  rw [show 16 - 2 * 6 - 0 = 4 from rfl] at h₄
  have h₅ := hP 5 (by decide) 1 (by decide)
  rw [show 16 - 2 * 5 - 1 = 5 from rfl] at h₅
  have h₆ := hP 5 (by decide) 0 (by decide)
  rw [show 16 - 2 * 5 - 0 = 6 from rfl] at h₆
  have h₇ := hP 4 (by decide) 1 (by decide)
  rw [show 16 - 2 * 4 - 1 = 7 from rfl] at h₇
  have h₈ := hP 4 (by decide) 0 (by decide)
  rw [show 16 - 2 * 4 - 0 = 8 from rfl] at h₈
  have h₉ := hP 3 (by decide) 1 (by decide)
  rw [show 16 - 2 * 3 - 1 = 9 from rfl] at h₉
  have h₁₀ := hP 3 (by decide) 0 (by decide)
  rw [show 16 - 2 * 3 - 0 = 10 from rfl] at h₁₀
  have h₁₁ := hP 2 (by decide) 1 (by decide)
  rw [show 16 - 2 * 2 - 1 = 11 from rfl] at h₁₁
  have h₁₂ := hP 2 (by decide) 0 (by decide)
  rw [show 16 - 2 * 2 - 0 = 12 from rfl] at h₁₂
  have h₁₃ := hP 1 (by decide) 1 (by decide)
  rw [show 16 - 2 * 1 - 1 = 13 from rfl] at h₁₃
  have h₁₄ := hP 1 (by decide) 0 (by decide)
  rw [show 16 - 2 * 1 - 0 = 14 from rfl] at h₁₄
  have h₁₅ := hP 0 (by decide) 1 (by decide)
  rw [show 16 - 2 * 0 - 1 = 15 from rfl] at h₁₅
  have h₁₆ := hP 0 (by decide) 0 (by decide)
  rw [show 16 - 2 * 0 - 0 = 16 from rfl] at h₁₆
  simp only [accN, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ordD, inp, hy1, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero, zero_xor_b]
  exact step16D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆

end VG.Proof.Gcm.X86_64.Stitch
