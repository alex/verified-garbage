import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# Multiword arithmetic on x86-64: a block of the BMI2/ADX multiplication

A block of `montMulAdx` (`Impl/Bignum/X86_64/Adx.lean`) adds `a_i` times
four words of `b` and `u` times four words of `m` to four words of the
window, with the carries `rcx` and `rbp` in and out (`block_ok`). Its first
half (`halfA_ok`) and its second (`halfB_ok`) each end their two chains in
their carry register, which their sums' bounds (`halfA_arith`,
`halfB_arith`) keep from overflowing, so the flags are clear after each.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep sx4)

/-! ## Addresses -/

theorem ea_ixk (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (k : Nat) :
    s.ea (ix b i (8 * (k : Int))) = off p (e + 8 * j + 8 * k) := by
  rw [show (8 * (k : Int)) = Int.ofNat (8 * k) by rw [Int.ofNat_eq_natCast, Int.natCast_mul]; rfl]
  exact ea_ix s hb hi _

theorem ea_below (s : State) {b : Reg} {p : Addr} {e d : Nat} (hb : s.gpr b = off p e) (hd : d ≤ e) :
    s.ea { base := b, disp := -(d : Int) } = off p (e - d) := by
  simp only [State.ea, hb, off, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.sub_eq_add_neg, show e = (e - d) + d by omega, BitVec.ofNat_add,
    BitVec.add_sub_cancel, show e - d + d - d = e - d by omega]

/-- A word of the working space, read through a memory operand. -/
theorem readSrc_word {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) {m : MemOp} {d : Nat}
    (he : s.ea m = off B d) (hd : d + 8 ≤ Z) : readSrc s (.mem m) = some (word s.mem B d) := by
  simp only [readSrc, State.load64, he, hs.ld hd, ite_true]

/-! ## The arithmetic -/

/-- A block's first half: `T + X B + h` over four words fits in five, so the
chains end with their carries zero. -/
theorem halfA_arith {X b₀ b₁ b₂ b₃ t₀ t₁ t₂ t₃ h C₀ C₁ C₂ C₃ H₀ H₁ H₂ H₃ h' : Nat}
    {c₁ c₂ c₃ c₄ o₁ o₂ o₃ o₄ c₅ o₅ : Nat}
    (hb₀ : X * b₀ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hb₁ : X * b₁ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hb₂ : X * b₂ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hb₃ : X * b₃ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (ht₀ : t₀ < 2 ^ 64) (ht₁ : t₁ < 2 ^ 64) (ht₂ : t₂ < 2 ^ 64) (ht₃ : t₃ < 2 ^ 64) (hh : h < 2 ^ 64)
    (hC₀ : C₀ < 2 ^ 64) (hC₁ : C₁ < 2 ^ 64) (hC₂ : C₂ < 2 ^ 64) (hC₃ : C₃ < 2 ^ 64) (hh' : h' < 2 ^ 64)
    (e₀ : C₀ + 2 ^ 64 * c₁ + 2 ^ 64 * o₁ + 2 ^ 64 * H₀ = X * b₀ + t₀ + 0 + h + 0)
    (e₁ : C₁ + 2 ^ 64 * c₂ + 2 ^ 64 * o₂ + 2 ^ 64 * H₁ = X * b₁ + t₁ + c₁ + H₀ + o₁)
    (e₂ : C₂ + 2 ^ 64 * c₃ + 2 ^ 64 * o₃ + 2 ^ 64 * H₂ = X * b₂ + t₂ + c₂ + H₁ + o₂)
    (e₃ : C₃ + 2 ^ 64 * c₄ + 2 ^ 64 * o₄ + 2 ^ 64 * H₃ = X * b₃ + t₃ + c₃ + H₂ + o₃)
    (e₄ : h' + 2 ^ 64 * c₅ + 2 ^ 64 * o₅ = H₃ + c₄ + o₄) :
    c₅ = 0 ∧ o₅ = 0 ∧
      C₀ + 2 ^ 64 * C₁ + 2 ^ 128 * C₂ + 2 ^ 192 * C₃ + 2 ^ 256 * h' =
        X * b₀ + 2 ^ 64 * (X * b₁) + 2 ^ 128 * (X * b₂) + 2 ^ 192 * (X * b₃) +
          (t₀ + 2 ^ 64 * t₁ + 2 ^ 128 * t₂ + 2 ^ 192 * t₃) + h := by
  omega

/-- A block's second half: `C + U M + h` over four words fits in five. -/
theorem halfB_arith {U m₀ m₁ m₂ m₃ C₀ C₁ C₂ C₃ h D₀ D₁ D₂ D₃ G₀ G₁ G₂ G₃ h' : Nat}
    {c₁ c₂ c₃ c₄ o₁ o₂ o₃ o₄ c₅ o₅ : Nat}
    (hm₀ : U * m₀ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hm₁ : U * m₁ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hm₂ : U * m₂ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hm₃ : U * m₃ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hC₀ : C₀ < 2 ^ 64) (hC₁ : C₁ < 2 ^ 64) (hC₂ : C₂ < 2 ^ 64) (hC₃ : C₃ < 2 ^ 64) (hh : h < 2 ^ 64)
    (hD₀ : D₀ < 2 ^ 64) (hD₁ : D₁ < 2 ^ 64) (hD₂ : D₂ < 2 ^ 64) (hD₃ : D₃ < 2 ^ 64) (hh' : h' < 2 ^ 64)
    (e₀ : D₀ + 2 ^ 64 * c₁ + 2 ^ 64 * o₁ + 2 ^ 64 * G₀ = C₀ + U * m₀ + 0 + h + 0)
    (e₁ : D₁ + 2 ^ 64 * c₂ + 2 ^ 64 * o₂ + 2 ^ 64 * G₁ = C₁ + U * m₁ + c₁ + G₀ + o₁)
    (e₂ : D₂ + 2 ^ 64 * c₃ + 2 ^ 64 * o₃ + 2 ^ 64 * G₂ = C₂ + U * m₂ + c₂ + G₁ + o₂)
    (e₃ : D₃ + 2 ^ 64 * c₄ + 2 ^ 64 * o₄ + 2 ^ 64 * G₃ = C₃ + U * m₃ + c₃ + G₂ + o₃)
    (e₄ : h' + 2 ^ 64 * c₅ + 2 ^ 64 * o₅ = G₃ + c₄ + o₄) :
    D₀ + 2 ^ 64 * D₁ + 2 ^ 128 * D₂ + 2 ^ 192 * D₃ + 2 ^ 256 * h' =
      (C₀ + 2 ^ 64 * C₁ + 2 ^ 128 * C₂ + 2 ^ 192 * C₃) +
        (U * m₀ + 2 ^ 64 * (U * m₁) + 2 ^ 128 * (U * m₂) + 2 ^ 192 * (U * m₃)) + h := by
  omega

/-! ## The first half -/

/-- `a_i` times four words of `b` added to four words of the window and the
carry `rcx`: the sum into `r11`, `r12`, `r13`, `r15` and `rcx`. -/
def halfA : List Instr :=
  [.alu32 .xor .rsi (.reg .rsi), .mov .rdx (.mem xSlot)] ++ (wordA 0 .rax .r11 .rcx ++
    (wordA 1 .rsi .r12 .rax ++ (wordA 2 .rax .r13 .rsi ++ (wordA 3 .rcx .r15 .rax ++ close .rcx))))

theorem halfA_ok {s : State} {B : Addr} {Z e eb j : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B eb) (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (he : 16 ≤ e) (hZ : e + 8 * j + 32 ≤ Z)
    (hZb : eb + 8 * j + 32 ≤ Z) :
    WP isa (.block halfA) s fun t => t.cf = some false ∧ t.of = some false ∧
      t.gpr .rdx = word s.mem B (e - 16) ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .r13).toNat +
          2 ^ 192 * (t.gpr .r15).toNat + 2 ^ 256 * (t.gpr .rcx).toNat =
        (word s.mem B (e - 16)).toNat * (word s.mem B (eb + 8 * j + 8 * 0)).toNat +
          2 ^ 64 * ((word s.mem B (e - 16)).toNat * (word s.mem B (eb + 8 * j + 8 * 1)).toNat) +
          2 ^ 128 * ((word s.mem B (e - 16)).toNat * (word s.mem B (eb + 8 * j + 8 * 2)).toNat) +
          2 ^ 192 * ((word s.mem B (e - 16)).toNat * (word s.mem B (eb + 8 * j + 8 * 3)).toNat) +
          ((word s.mem B (e + 8 * j + 8 * 0)).toNat + 2 ^ 64 * (word s.mem B (e + 8 * j + 8 * 1)).toNat +
            2 ^ 128 * (word s.mem B (e + 8 * j + 8 * 2)).toNat + 2 ^ 192 * (word s.mem B (e + 8 * j + 8 * 3)).toNat) +
          (s.gpr .rcx).toNat ∧
      Keeps [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx] s t := by
  have rb : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r9 .r14 (8 * (k : Int)))) = some (word s.mem B (eb + 8 * j + 8 * k)) :=
    fun k hk => readSrc_word hs (ea_ixk s h9 h14 k) (by omega)
  have rt : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r8 .r14 (8 * (k : Int)))) = some (word s.mem B (e + 8 * j + 8 * k)) :=
    fun k hk => readSrc_word hs (ea_ixk s h8 h14 k) (by omega)
  have rx : readSrc s (.mem xSlot) = some (word s.mem B (e - 16)) :=
    readSrc_word hs (ea_below s (d := 16) h8 he) (by omega)
  -- Reads through registers the steps keep.
  have kr : ∀ {rs : List Reg} {t : State}, Keeps rs s t → .r8 ∉ rs → .r9 ∉ rs → .r14 ∉ rs →
      (∀ k : Nat, k < 4 → readSrc t (.mem (ix .r9 .r14 (8 * (k : Int)))) = some (word s.mem B (eb + 8 * j + 8 * k))) ∧
      (∀ k : Nat, k < 4 → readSrc t (.mem (ix .r8 .r14 (8 * (k : Int)))) = some (word s.mem B (e + 8 * j + 8 * k))) :=
    fun K a b c => ⟨fun k hk => (K.readMem (by simpa [ix] using b) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rb k hk),
      fun k hk => (K.readMem (by simpa [ix] using a) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rt k hk)⟩
  unfold halfA
  rw [WP.block_append_iff, show ([.alu32 .xor .rsi (.reg .rsi), .mov .rdx (.mem xSlot)] : List Instr) =
    [.alu32 .xor .rsi (.reg .rsi)] ++ [.mov .rdx (.mem xSlot)] from rfl, WP.block_append_iff]
  refine WP.mono (xorRsi_ok s) fun s₁ ⟨_, c₁, o₁, k₁⟩ => ?_
  refine WP.mono (movMem_ok s₁ (dst := .rdx) ((k₁.readMem (by decide) (by intro i h; cases h)).trans rx))
    fun s₂ ⟨d₂, c₂, o₂, k₂⟩ => ?_
  have K₂ := (k₁.trans k₂)
  obtain ⟨rb₂, rt₂⟩ := kr K₂ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₂ (rb₂ 0 (by decide)) (rt₂ 0 (by decide)) (c₂.trans c₁) (o₂.trans o₁)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₃ ⟨a₁, p₁, ca₁, oa₁, e₀, k₃⟩ => ?_
  have K₃ := K₂.trans k₃
  obtain ⟨rb₃, rt₃⟩ := kr K₃ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₃ (rb₃ 1 (by decide)) (rt₃ 1 (by decide)) ca₁ oa₁
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨a₂, p₂, ca₂, oa₂, e₁, k₄⟩ => ?_
  have K₄ := K₃.trans k₄
  obtain ⟨rb₄, rt₄⟩ := kr K₄ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₄ (rb₄ 2 (by decide)) (rt₄ 2 (by decide)) ca₂ oa₂
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨a₃, p₃, ca₃, oa₃, e₂, k₅⟩ => ?_
  have K₅ := K₄.trans k₅
  obtain ⟨rb₅, rt₅⟩ := kr K₅ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₅ (rb₅ 3 (by decide)) (rt₅ 3 (by decide)) ca₃ oa₃
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₆ ⟨a₄, p₄, ca₄, oa₄, e₃, k₆⟩ => ?_
  refine WP.mono (close_ok s₆ ca₄ oa₄ (by decide)) fun t ⟨a₅, p₅, ca₅, oa₅, e₄, k₇⟩ => ?_
  have K := (K₅.trans k₆).trans k₇
  -- The registers along the way.
  have x₂ : s₂.gpr .rdx = word s.mem B (e - 16) := d₂
  have x₃ : s₃.gpr .rdx = s₂.gpr .rdx := k₃.gpr (by decide)
  have x₄ : s₄.gpr .rdx = s₂.gpr .rdx := (k₄.gpr (by decide)).trans x₃
  have x₅ : s₅.gpr .rdx = s₂.gpr .rdx := (k₅.gpr (by decide)).trans x₄
  have c₀ : s₂.gpr .rcx = s.gpr .rcx := K₂.gpr (by decide)
  have r11 : t.gpr .r11 = s₃.gpr .r11 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans
    ((k₅.gpr (by decide)).trans (k₄.gpr (by decide))))
  have r12 : t.gpr .r12 = s₄.gpr .r12 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans (k₅.gpr (by decide)))
  have r13 : t.gpr .r13 = s₅.gpr .r13 := (k₇.gpr (by decide)).trans (k₆.gpr (by decide))
  have r15 : t.gpr .r15 = s₆.gpr .r15 := k₇.gpr (by decide)
  rw [x₂] at e₀
  rw [x₃, x₂] at e₁
  rw [x₄, x₂] at e₂
  rw [x₅, x₂] at e₃
  rw [c₀] at e₀
  simp only [Bool.toNat_false] at e₀
  have hb : ∀ k, (word s.mem B (e - 16)).toNat * (word s.mem B (eb + 8 * j + 8 * k)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun k => Nat.mul_le_mul (by have := (word s.mem B (e - 16)).isLt; omega)
        (by have := (word s.mem B (eb + 8 * j + 8 * k)).isLt; omega)
  obtain ⟨z₁, z₂, e⟩ := halfA_arith (hb 0) (hb 1) (hb 2) (hb 3) (word s.mem B (e + 8 * j + 8 * 0)).isLt
    (word s.mem B (e + 8 * j + 8 * 1)).isLt (word s.mem B (e + 8 * j + 8 * 2)).isLt
    (word s.mem B (e + 8 * j + 8 * 3)).isLt (s.gpr .rcx).isLt (s₃.gpr .r11).isLt (s₄.gpr .r12).isLt
    (s₅.gpr .r13).isLt (s₆.gpr .r15).isLt (t.gpr .rcx).isLt e₀ e₁ e₂ e₃ e₄
  refine ⟨?_, ?_, ?_, ?_, K.mono (by simp)⟩
  · rw [ca₅]; cases a₅ <;> simp_all
  · rw [oa₅]; cases p₅ <;> simp_all
  · rw [(k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans x₅)]
    exact x₂
  · rw [r11, r12, r13, r15]; exact e

/-! ## The second half -/

/-- `u` times four words of `m` added to `r11`, `r12`, `r13`, `r15` and the
carry `rbp`. -/
def halfB : List Instr :=
  [.mov .rdx (.mem uSlot)] ++ (wordB 0 .rax .r11 .rbp ++
    (wordB 1 .rbp .r12 .rax ++ (wordB 2 .rax .r13 .rbp ++ (wordB 3 .rbp .r15 .rax ++ close .rbp))))

theorem halfB_ok {s : State} {B : Addr} {Z e eN j : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e)
    (h10 : s.gpr .r10 = off B eN) (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (he : 16 ≤ e) (hZ : e ≤ Z)
    (hZN : eN + 8 * j + 32 ≤ Z) (hc : s.cf = some false) (ho : s.of = some false) :
    WP isa (.block halfB) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .r13).toNat +
          2 ^ 192 * (t.gpr .r15).toNat + 2 ^ 256 * (t.gpr .rbp).toNat =
        ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat + 2 ^ 128 * (s.gpr .r13).toNat +
          2 ^ 192 * (s.gpr .r15).toNat) +
        ((word s.mem B (e - 8)).toNat * (word s.mem B (eN + 8 * j + 8 * 0)).toNat +
          2 ^ 64 * ((word s.mem B (e - 8)).toNat * (word s.mem B (eN + 8 * j + 8 * 1)).toNat) +
          2 ^ 128 * ((word s.mem B (e - 8)).toNat * (word s.mem B (eN + 8 * j + 8 * 2)).toNat) +
          2 ^ 192 * ((word s.mem B (e - 8)).toNat * (word s.mem B (eN + 8 * j + 8 * 3)).toNat)) +
        (s.gpr .rbp).toNat ∧
      Keeps [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rbp] s t := by
  have rm : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r10 .r14 (8 * (k : Int)))) =
      some (word s.mem B (eN + 8 * j + 8 * k)) :=
    fun k hk => readSrc_word hs (ea_ixk s h10 h14 k) (by omega)
  have ru : readSrc s (.mem uSlot) = some (word s.mem B (e - 8)) :=
    readSrc_word hs (ea_below s (d := 8) h8 (by omega)) (by omega)
  have kr : ∀ {rs : List Reg} {t : State}, Keeps rs s t → .r10 ∉ rs → .r14 ∉ rs →
      ∀ k : Nat, k < 4 → readSrc t (.mem (ix .r10 .r14 (8 * (k : Int)))) = some (word s.mem B (eN + 8 * j + 8 * k)) :=
    fun K a c k hk => (K.readMem (by simpa [ix] using a) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rm k hk)
  unfold halfB
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok s (dst := .rdx) ru) fun s₁ ⟨d₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wordB_ok s₁ (kr k₁ (by decide) (by decide) 0 (by decide)) (c₁.trans hc) (o₁.trans ho)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₂ ⟨a₁, p₁, ca₁, oa₁, e₀, k₂⟩ => ?_
  have K₂ := k₁.trans k₂
  rw [WP.block_append_iff]
  refine WP.mono (wordB_ok s₂ (kr K₂ (by decide) (by decide) 1 (by decide)) ca₁ oa₁
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₃ ⟨a₂, p₂, ca₂, oa₂, e₁, k₃⟩ => ?_
  have K₃ := K₂.trans k₃
  rw [WP.block_append_iff]
  refine WP.mono (wordB_ok s₃ (kr K₃ (by decide) (by decide) 2 (by decide)) ca₂ oa₂
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨a₃, p₃, ca₃, oa₃, e₂, k₄⟩ => ?_
  have K₄ := K₃.trans k₄
  rw [WP.block_append_iff]
  refine WP.mono (wordB_ok s₄ (kr K₄ (by decide) (by decide) 3 (by decide)) ca₃ oa₃
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨a₄, p₄, ca₄, oa₄, e₃, k₅⟩ => ?_
  refine WP.mono (close_ok s₅ ca₄ oa₄ (by decide)) fun t ⟨a₅, p₅, ca₅, oa₅, e₄, k₆⟩ => ?_
  have K := (K₄.trans k₅).trans k₆
  have x₂ : s₂.gpr .rdx = s₁.gpr .rdx := k₂.gpr (by decide)
  have x₃ : s₃.gpr .rdx = s₁.gpr .rdx := (k₃.gpr (by decide)).trans x₂
  have x₄ : s₄.gpr .rdx = s₁.gpr .rdx := (k₄.gpr (by decide)).trans x₃
  have i11 : s₁.gpr .r11 = s.gpr .r11 := k₁.gpr (by decide)
  have i12 : s₂.gpr .r12 = s.gpr .r12 := K₂.gpr (by decide)
  have i13 : s₃.gpr .r13 = s.gpr .r13 := K₃.gpr (by decide)
  have i15 : s₄.gpr .r15 = s.gpr .r15 := K₄.gpr (by decide)
  have ib : s₁.gpr .rbp = s.gpr .rbp := k₁.gpr (by decide)
  have r11 : t.gpr .r11 = s₂.gpr .r11 := (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans
    ((k₄.gpr (by decide)).trans (k₃.gpr (by decide))))
  have r12 : t.gpr .r12 = s₃.gpr .r12 := (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans (k₄.gpr (by decide)))
  have r13 : t.gpr .r13 = s₄.gpr .r13 := (k₆.gpr (by decide)).trans (k₅.gpr (by decide))
  have r15 : t.gpr .r15 = s₅.gpr .r15 := k₆.gpr (by decide)
  rw [d₁, i11, ib] at e₀
  rw [x₂, d₁, i12] at e₁
  rw [x₃, d₁, i13] at e₂
  rw [x₄, d₁, i15] at e₃
  simp only [Bool.toNat_false] at e₀
  have hm : ∀ k, (word s.mem B (e - 8)).toNat * (word s.mem B (eN + 8 * j + 8 * k)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun k => Nat.mul_le_mul (by have := (word s.mem B (e - 8)).isLt; omega)
        (by have := (word s.mem B (eN + 8 * j + 8 * k)).isLt; omega)
  have e := halfB_arith (hm 0) (hm 1) (hm 2) (hm 3) (s.gpr .r11).isLt (s.gpr .r12).isLt (s.gpr .r13).isLt
    (s.gpr .r15).isLt (s.gpr .rbp).isLt (s₂.gpr .r11).isLt (s₃.gpr .r12).isLt (s₄.gpr .r13).isLt
    (s₅.gpr .r15).isLt (t.gpr .rbp).isLt e₀ e₁ e₂ e₃ e₄
  refine ⟨?_, K.mono (by simp)⟩
  rw [r11, r12, r13, r15]; exact e

/-! ## The stores and the count -/

/-- `b + 8 i + 16`, `b + 8 i + 24`, as `xrun` leaves them. -/
theorem addrD {p : Addr} {e j : Nat} (d : Nat) :
    off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 (d : Int) = off p (e + 8 * j + d) := by
  rw [ofNat_mul8, BitVec.ofInt_natCast, off, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add,
    ← BitVec.ofNat_add, Nat.add_assoc]

theorem addrK0 {p : Addr} {e j : Nat} :
    off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = off p (e + 8 * j + 8 * 0) := addrD 0
theorem addrK1 {p : Addr} {e j : Nat} :
    off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 8 = off p (e + 8 * j + 8 * 1) := addrD 8
theorem addrK2 {p : Addr} {e j : Nat} :
    off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 16 = off p (e + 8 * j + 8 * 2) := addrD 16
theorem addrK3 {p : Addr} {e j : Nat} :
    off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 24 = off p (e + 8 * j + 8 * 3) := addrD 24

theorem ofNat_add_four (j : Nat) : BitVec.ofNat 64 j + 4 = BitVec.ofNat 64 (j + 4) := by
  rw [BitVec.ofNat_add]; rfl

/-- The block's last six instructions. -/
def tail : List Instr :=
  [.store (ix .r8 .r14) .r11, .store (ix .r8 .r14 8) .r12, .store (ix .r8 .r14 16) .r13,
    .store (ix .r8 .r14 24) .r15, .alu .add .r14 (.imm 4), .alu .cmp .r14 (.reg .rbx)]

theorem tail_ok {s : State} {B : Addr} {Z e j w : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (hZ : e + 8 * j + 32 ≤ Z)
    (hjw : j + 4 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block tail) s fun t =>
      t.mem = (((s.mem.writeW (off B (e + 8 * j + 8 * 0)) (s.gpr .r11)).writeW (off B (e + 8 * j + 8 * 1))
        (s.gpr .r12)).writeW (off B (e + 8 * j + 8 * 2)) (s.gpr .r13)).writeW (off B (e + 8 * j + 8 * 3))
        (s.gpr .r15) ∧
      t.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧ t.zf = some (decide (j + 4 = w)) ∧ Keep [.r14] s t := by
  have hst : ∀ k, k < 4 → InRegions s.wr (off B (e + 8 * j + 8 * k)) 8 := fun k hk => hs.st (by omega)
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.mem = (((s.mem.writeW (off B (e + 8 * j + 8 * 0)) (s.gpr .r11)).writeW
      (off B (e + 8 * j + 8 * 1)) (s.gpr .r12)).writeW (off B (e + 8 * j + 8 * 2)) (s.gpr .r13)).writeW
      (off B (e + 8 * j + 8 * 3)) (s.gpr .r15) ∧
      t.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧ t.zf = some (decide (j + 4 = w))) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold tail
  xrun [State.ea, ix, h8, h14, hbx, addrK0, addrK1, addrK2, addrK3, hst 0 (by decide), hst 1 (by decide), hst 2 (by decide), hst 3 (by decide), ofNat_add_four,
    ofNat_sub_beq hjw hw]

/-! ## The block -/

theorem wv4 (m : Mem) (p : Addr) (d : Nat) :
    wv m p d 4 = (word m p (d + 8 * 0)).toNat + 2 ^ 64 * (word m p (d + 8 * 1)).toNat +
      2 ^ 128 * (word m p (d + 8 * 2)).toNat + 2 ^ 192 * (word m p (d + 8 * 3)).toNat := by
  simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]

theorem mul_w4 (X a b c d : Nat) : X * (a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d) =
    X * a + 2 ^ 64 * (X * b) + 2 ^ 128 * (X * c) + 2 ^ 192 * (X * d) := by
  simp only [Nat.mul_add, Nat.mul_left_comm X]

theorem Keeps.keep {rs : List Reg} {s t : State} (h : Keeps rs s t) : Keep rs s t := ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- Four words written at `d`: the number they make, and nothing else changed. -/
theorem write4 (m : Mem) (B : Addr) (d : Nat) (v₀ v₁ v₂ v₃ : BitVec 64) (hd : d + 32 ≤ 2 ^ 64) :
    let m' := (((m.writeW (off B (d + 8 * 0)) v₀).writeW (off B (d + 8 * 1)) v₁).writeW (off B (d + 8 * 2)) v₂).writeW
      (off B (d + 8 * 3)) v₃
    wv m' B d 4 = v₀.toNat + 2 ^ 64 * v₁.toNat + 2 ^ 128 * v₂.toNat + 2 ^ 192 * v₃.toNat ∧ Outside B d 32 m m' := by
  intro m'
  refine ⟨?_, ?_⟩
  · rw [show (4 : Nat) = 3 + 1 from rfl, wv_writeW_top _ _ _ _ _ (by omega), show (3 : Nat) = 2 + 1 from rfl,
      wv_writeW_top _ _ _ _ _ (by omega), show (2 : Nat) = 1 + 1 from rfl, wv_writeW_top _ _ _ _ _ (by omega),
      show (1 : Nat) = 0 + 1 from rfl, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
  · exact (((writeW_outside m B v₀ (d := d + 8 * 0) (by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ B v₁ (d := d + 8 * 1) (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ B v₂ (d := d + 8 * 2) (by omega)).mono (by omega) (by omega)) |>.trans
      ((writeW_outside _ B v₃ (d := d + 8 * 3) (by omega)).mono (by omega) (by omega))

/-- A block: `a_i` times four words of `b` and `u` times four words of `m`
added to four words of the window and the carries. -/
theorem block_ok {s : State} {B : Addr} {Z e eb eN j w : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B eb) (h10 : s.gpr .r10 = off B eN) (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (he : 16 ≤ e) (hZ : e + 8 * j + 32 ≤ Z) (hZb : eb + 8 * j + 32 ≤ Z)
    (hZN : eN + 8 * j + 32 ≤ Z) (hjw : j + 4 ≤ w) (hw : w < 2 ^ 60) :
    WP isa (.block Adx.block) s fun t =>
      wv t.mem B (e + 8 * j) 4 + 2 ^ 256 * ((t.gpr .rcx).toNat + (t.gpr .rbp).toNat) =
        wv s.mem B (e + 8 * j) 4 + (word s.mem B (e - 16)).toNat * wv s.mem B (eb + 8 * j) 4 +
          (word s.mem B (e - 8)).toNat * wv s.mem B (eN + 8 * j) 4 + (s.gpr .rcx).toNat + (s.gpr .rbp).toNat ∧
      Outside B (e + 8 * j) 32 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧
      t.zf = some (decide (j + 4 = w)) ∧
      Keep [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  rw [show Adx.block = halfA ++ (halfB ++ tail) from rfl, WP.block_append_iff]
  refine WP.mono (halfA_ok hs h8 h9 h14 he hZ hZb) fun a ⟨ca, oa, _, ea, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hsa : Scr a B Z := hs.congr ka.2.2.2
  refine WP.mono (halfB_ok hsa ((ka.gpr (by decide)).trans h8) ((ka.gpr (by decide)).trans h10)
    ((ka.gpr (by decide)).trans h14) he (by omega) hZN ca oa) fun b ⟨eb', kb⟩ => ?_
  have hsb : Scr b B Z := hsa.congr kb.2.2.2
  have kab := ka.trans kb
  refine WP.mono (tail_ok hsb ((kab.gpr (by decide)).trans h8) ((kab.gpr (by decide)).trans h14)
    ((kab.gpr (by decide)).trans hbx) hZ (by omega) (by omega)) fun t ⟨hm, h14', hz, kt⟩ => ?_
  obtain ⟨hv, ho⟩ := write4 b.mem B (e + 8 * j) (b.gpr .r11) (b.gpr .r12) (b.gpr .r13) (b.gpr .r15) (by omega)
  have mb : b.mem = s.mem := kab.2.1
  have ma : a.mem = s.mem := ka.2.1
  rw [← hm] at hv ho
  rw [mb] at ho
  rw [ma] at eb'
  have rcx : t.gpr .rcx = a.gpr .rcx := (kt.gpr (by decide)).trans (kb.gpr (by decide))
  have rbp : t.gpr .rbp = b.gpr .rbp := kt.gpr (by decide)
  have rbp₀ : a.gpr .rbp = s.gpr .rbp := ka.gpr (by decide)
  rw [rbp₀] at eb'
  refine ⟨?_, ho, h14', hz, (kab.keep.trans kt).mono (by simp)⟩
  rw [hv, rcx, rbp, wv4 s.mem B (e + 8 * j), wv4 s.mem B (eb + 8 * j), wv4 s.mem B (eN + 8 * j), mul_w4, mul_w4]
  omega

end VG.Proof.Bignum.X86_64
