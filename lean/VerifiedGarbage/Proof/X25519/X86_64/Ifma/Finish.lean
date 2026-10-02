import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step

/-!
# X25519 on x86-64 with AVX512_IFMA: after the loop

`vfinish` carries the lanes twice, then from the lowest limb up, and stores
each lane as four 64-bit words: the same number modulo `p`, below `2²⁵⁶`.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word val4 F E)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## Numbers -/

/-- The limbs from the lowest up, each but the top one's bits from 51 up
passed to the next (`pre`), and masked (`cur`). -/
def pre (x : Nat → Nat) : Nat → Nat
  | 0 => x 0
  | 1 => x 1 + x 0 / 2 ^ 51
  | 2 => x 2 + (x 1 + x 0 / 2 ^ 51) / 2 ^ 51
  | 3 => x 3 + (x 2 + (x 1 + x 0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51
  | _ => x 4 + (x 3 + (x 2 + (x 1 + x 0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51

/-- The four words of a lane, with the masks `m`, `m13`, `m26`, `m39`. -/
def packW (x : Nat → Nat) (m m13 m26 m39 : Nat) : Nat → Nat
  | 0 => (pre x 0 &&& m) ||| (pre x 1 &&& m &&& m13) * 2 ^ 51
  | 1 => (pre x 1 &&& m) / 2 ^ 13 ||| (pre x 2 &&& m &&& m26) * 2 ^ 38
  | 2 => (pre x 2 &&& m) / 2 ^ 26 ||| (pre x 3 &&& m &&& m39) * 2 ^ 25
  | _ => (pre x 3 &&& m) / 2 ^ 39 ||| pre x 4 * 2 ^ 12

def packS : Sym := symOf vpack

theorem packS_st : packS.st.map Prod.fst = [Z3, X3, Z2, X2] := by decide +kernel

/-- The term stored at `X2 + 32 m`. -/
def packT (m : Nat) : T := ((packS.st.reverse).getD m (0, .zero)).2

theorem packT_mem : ∀ m < 4, (X2 + 32 * m, packT m) ∈ packS.st := by decide +kernel

theorem packT_nat (E : Env) : ∀ m < 4, ∀ j < 4, (packT m).nat E j =
    packW (fun i => E.v i m) (E.m KM m) (E.m K13 m) (E.m K26 m) (E.m K39 m) j := by
  intro m hm j hj
  rcases VG.X86_64.cases4 hm with rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hj with rfl | rfl | rfl | rfl <;> rfl

def packB : Bnds :=
  ⟨fun r => if r < 5 then 2 ^ 51 + 18 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KM then 2 ^ 51 - 1 else if d = K13 then 2 ^ 13 - 1 else if d = K26 then 2 ^ 26 - 1
      else if d = K39 then 2 ^ 39 - 1 else 2 ^ 64 - 1, fun _ => 0⟩

theorem packT_ok : ∀ m < 4, ∀ j < 4, (packT m).ok packB j = true := by decide +kernel

theorem packS_small : ∀ x ∈ packS.st, x.1 < 2 ^ 62 := by decide +kernel
theorem packS_apart : Apart packS.st := by decide +kernel

theorem or_mul {a b n : Nat} (h : a < 2 ^ n) : a ||| b * 2 ^ n = a + b * 2 ^ n := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm]

/-- The four words stand for the limbs' number. -/
theorem packW_val (x : Nat → Nat) (hx : ∀ i < 5, x i ≤ 2 ^ 51 + 18) :
    packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 0 +
      2 ^ 64 * packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 1 +
      2 ^ 128 * packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 2 +
      2 ^ 192 * packW x (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) 3 = lv x := by
  have h0 := hx 0 (by decide); have h1 := hx 1 (by decide); have h2 := hx 2 (by decide)
  have h3 := hx 3 (by decide); have h4 := hx 4 (by decide)
  simp only [packW, pre, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 13 ∣ 2 ^ 51),
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 26 ∣ 2 ^ 51), Nat.mod_mod_of_dvd _ (by decide : 2 ^ 39 ∣ 2 ^ 51)]
  rw [or_mul (by omega), or_mul (by omega), or_mul (by omega), or_mul (by omega)]
  simp only [lv]
  omega

/-- A carry of limbs below `2⁵²` leaves limbs of at most `2⁵¹ + 18`. -/
theorem carryNat_le (x : Nat → Nat) (hx : ∀ i < 5, x i < 2 ^ 52) :
    ∀ i < 5, carryNat (2 ^ 51 - 1) 19 x i ≤ 2 ^ 51 + 18 := by
  have h0 := hx 0 (by decide); have h1 := hx 1 (by decide); have h2 := hx 2 (by decide)
  have h3 := hx 3 (by decide); have h4 := hx 4 (by decide)
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · simp only [carryNat, Nat.and_two_pow_sub_one_eq_mod]
    rcases (by omega : x 4 / 2 ^ 51 = 0 ∨ x 4 / 2 ^ 51 = 1) with e | e <;> rw [e] <;> omega
  all_goals simp only [carryNat, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem packB_env {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base)
    (hk : Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i ≤ 2 ^ 51 + 18) : EnvOK s packB := by
  refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
  · simp only [packB]
    split
    · have := hx l hl r (by omega); simp only [lanes, Nat.zero_add] at this; exact this
    · exact lt64 _
  · simp only [packB]
    split
    · subst_vars; rw [hk.km l hl]
    · split
      · subst_vars; rw [hk.k13 l hl]
      · split
        · subst_vars; rw [hk.k26 l hl]
        · split
          · subst_vars; rw [hk.k39 l hl]
          · exact lt64 _

/-- `vfinish`: each lane as four words, in the slots `x2, z2, x3, z3`. -/
theorem vfinish_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block vfinish) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mxcsr = s.mxcsr ∧ Outside base 96 128 s.mem s'.mem ∧
      ∀ m < 4, F s'.mem base (X2 + 32 * m) = fe5 (lanes s 0 m) := by
  have hr := hs.rdi
  simp only [vfinish, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hr (scr_ctx hs) hk.c fun l hl i hi => by have := hy l hl i hi; omega)
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁.rdi (scr_ctx hs₁) hk₁.c fun l hl i hi => by have := (u₁ l hl i hi).2; omega)
    fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have hk₂ : Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have b₂ : ∀ l < 4, ∀ i < 5, lanes s₂ 0 l i ≤ 2 ^ 51 + 18 := fun l hl i hi => by
    rw [(u₂ l hl i hi).1]; exact carryNat_le _ (fun j hj => (u₁ l hl j hj).2) i hi
  have hE := packB_env hs₂.rdi hk₂ b₂
  have e : Sym.init.run vpack = some packS := symOf_eq _ _
  refine WP.mono (run_ok (scr_ctx hs₂) e) fun s₃ h => ?_
  have v₃ : vm s₂ s₃ = s₃ := h.eq
  refine ⟨(vm_gpr v₃).trans ((vm_gpr v₂).trans (vm_gpr v₁)), (vm_rd v₃).trans ((vm_rd v₂).trans (vm_rd v₁)),
    (vm_wr v₃).trans ((vm_wr v₂).trans (vm_wr v₁)), ?_, ?_, fun m hm => ?_⟩
  · rw [h.mxcsr]; rw [← v₂, ← v₁]; rfl
  · rw [h.mem, hs₂.rdi, m₂, m₁]
    exact stores_outside _ _ _ (by decide) _ (by decide +kernel)
  · -- the words of lane `m`
    have w : ∀ j < 4, (word s₃.mem base (X2 + 32 * m + 8 * j)).toNat =
        packW (fun i => lanes s₂ 0 m i) (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) j := fun j hj => by
      rw [← mq_eq_word, h.mem, hs₂.rdi, stores_mq _ _ _ _ (packT_mem m hm) hj packS_small packS_apart,
        (nat_ok hE _ hj (packT_ok m hm j hj)).1, packT_nat _ m hm j hj, envOf_m hs₂.rdi, envOf_m hs₂.rdi,
        envOf_m hs₂.rdi, envOf_m hs₂.rdi, hk₂.km m hm, hk₂.k13 m hm, hk₂.k26 m hm, hk₂.k39 m hm]
      rfl
    have fe : VG.Proof.X25519.X86_64.fe s₃.mem base (X2 + 32 * m) = lv (lanes s₂ 0 m) := by
      simp only [VG.Proof.X25519.X86_64.fe, val4]
      have w0 := w 0 (by decide); have w1 := w 1 (by decide); have w2 := w 2 (by decide)
      have w3 := w 3 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at w0 w1 w2 w3
      rw [w0, show X2 + 32 * m + 16 = X2 + 32 * m + 8 * 2 by rfl, w2, w1, w3]
      exact packW_val _ (b₂ m hm)
    show toFe _ = _
    rw [fe]
    rw [show toFe (lv (lanes s₂ 0 m)) = fe5 (lanes s₂ 0 m) from rfl,
      fe5_congr (fun i hi => (u₂ m hm i hi).1), fe5_carry _ (by have := (u₁ m hm 4 (by decide)).2; omega),
      fe5_congr (fun i hi => (u₁ m hm i hi).1), fe5_carry _ (by have := hy m hm 4 (by decide); omega)]

end VG.Proof.X25519.X86_64.Ifma
