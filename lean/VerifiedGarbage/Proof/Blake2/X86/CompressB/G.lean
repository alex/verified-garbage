import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.X86.CompressB

/-!
# BLAKE2b on x86 (32-bit): `G`

Untrusted: everything here is checked by Lean. The weakest-precondition
rules for the 64-bit operations of `VG.Impl.Blake2.X86.CompressB` that
`Proof/Sha512/X86/Rounds.lean` does not have (the exclusive or of two pairs,
and the rotations), and `g_ok`: one symbolic execution of `G` for any
offsets of its words in `scratch`.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86
open VG.Impl.Blake2.X86.CompressB (xor64 mask rorPair g)
open VG.Impl.Sha512.X86 (ld st add64 add64m)
open VG.Proof.Sha512.X86 (Only Pair Acc rd64 write64 wp_ld wp_st wp_add64 wp_add64m wp_xorS
  wp_andS wp_movS wp_ror rd64_write64_self rd64_write64_ne frame_write64)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_rotr hi_rotr lo_rotr' hi_rotr')
open VG.Proof.Sha256.X86.Stream (Upd Mupd)

/-! ## Rotations of 64-bit words as pairs -/

/-- What `rorPair` computes in one half: `Q` rotated by `k`, with its low
`32 - k` bits replaced by those of `P` rotated by `k`. -/
def merge (P Q : BitVec 32) (k : Nat) : BitVec 32 :=
  Q.rotateRight k ^^^ ((P.rotateRight k ^^^ Q.rotateRight k) &&& mask k)

theorem merge_eq (P Q : BitVec 32) {k : Nat} (h0 : 0 < k) (h : k < 32) :
    merge P Q k = P >>> k ^^^ Q <<< (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [merge, mask, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    Nat.mod_eq_of_lt h]
  by_cases hc : i < 32 - k
  · simp [hc, hi, show k + i < 32 by omega]
    cases P[k + i] <;> cases Q[k + i] <;> rfl
  · simp [hc, hi, show ¬ k + i < 32 by omega, BitVec.getLsbD_of_ge P (k + i) (by omega)]

theorem lo_rotr32 (x : BitVec 64) : lo (x.rotateRight 32) = hi x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi']

theorem hi_rotr32 (x : BitVec 64) : hi (x.rotateRight 32) = lo x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi', show ¬ 32 + i < 32 by omega, show 32 + i - 32 = i by omega, show 32 + i < 64 by omega]

/-- A rotation by 32 swaps the halves. -/
theorem _root_.VG.Proof.Sha512.X86.Pair.swap {s : State} {l h : Reg} {x : BitVec 64} (p : Pair s l h x) :
    Pair s h l (x.rotateRight 32) :=
  ⟨by rw [lo_rotr32]; exact p.2, by rw [hi_rotr32]; exact p.1⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : Pair s dl dh x) (py : Pair s l h y)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x ^^^ y) → WP isa (.block rest) s' Q) :
    WP isa (.block (xor64 dl dh l h ++ rest)) s Q := by
  simp only [xor64, List.cons_append, List.nil_append]
  refine wp_xorS rfl fun s₁ u₁ => ?_
  refine wp_xorS rfl fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_xor]
  · rw [u₂.gpr, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.2, py.2, hi_xor]

theorem wp_rorPair {l h t : Reg} {k : Nat} (h0 : 0 < k) (hk : k < 32) (hlh : l ≠ h) (hlt : l ≠ t)
    (hht : h ≠ t) {P R : BitVec 32} (hl : s.gpr l = P) (hh : s.gpr h = R)
    (K : ∀ s', Only [l, h, t] s s' → s'.gpr h = merge P R k → s'.gpr l = merge R P k →
      WP isa (.block rest) s' Q) :
    WP isa (.block (rorPair l h k t ++ rest)) s Q := by
  simp only [rorPair, List.cons_append, List.nil_append]
  refine wp_ror ⟨h0, by omega⟩ fun s₁ u₁ => wp_ror ⟨h0, by omega⟩ fun s₂ u₂ =>
    wp_movS rfl fun s₃ u₃ => wp_xorS rfl fun s₄ u₄ => wp_andS rfl fun s₅ u₅ =>
    wp_xorS rfl fun s₆ u₆ => wp_xorS rfl fun s₇ u₇ => ?_
  have O := (((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇))
  -- The rotated halves, and the mask of their bits to exchange.
  have eL : s₂.gpr l = P.rotateRight k := by rw [u₂.other _ hlh, u₁.gpr, hl]
  have eH : s₂.gpr h = R.rotateRight k := by rw [u₂.gpr, u₁.other _ (Ne.symm hlh), hh]
  have eT : s₅.gpr t = (P.rotateRight k ^^^ R.rotateRight k) &&& mask k := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ hht, eL, eH]
  refine K s₇ (O.mono (by simp)) ?_ ?_
  · rw [u₇.gpr, u₆.other _ (Ne.symm hlh), u₅.other _ hht, u₄.other _ hht, u₃.other _ hht, eH,
      u₆.other _ (Ne.symm hlt), eT]
    rfl
  · rw [u₇.other _ hlh, u₆.gpr, u₅.other _ hlt, u₄.other _ hlt, u₃.other _ hlt, eL, eT, merge,
      BitVec.xor_comm (R.rotateRight k)]

/-- A rotation by `0 < k < 32` of the word in `(l, h)` (low half in `l`) leaves it in `(h, l)`. -/
theorem wp_rot {l h t : Reg} {k : Nat} (h0 : 0 < k) (hk : k < 32) (hlh : l ≠ h) (hlt : l ≠ t)
    (hht : h ≠ t) {x : BitVec 64} (p : Pair s l h x)
    (K : ∀ s', Only [l, h, t] s s' → Pair s' h l (x.rotateRight k) → WP isa (.block rest) s' Q) :
    WP isa (.block (rorPair l h k t ++ rest)) s Q :=
  wp_rorPair h0 hk hlh hlt hht p.1 p.2 fun s' o e₁ e₂ => K s' o
    ⟨by rw [e₁, merge_eq _ _ h0 hk, lo_rotr x h0 hk], by rw [e₂, merge_eq _ _ h0 hk, hi_rotr x h0 hk]⟩

/-- A rotation by `32 + k` (`0 < k < 32`) of the word in `(h, l)` (low half in `h`)
leaves it in `(h, l)`. -/
theorem wp_rot' {l h t : Reg} {k : Nat} (h0 : 0 < k) (hk : k < 32) (hlh : l ≠ h) (hlt : l ≠ t)
    (hht : h ≠ t) {x : BitVec 64} (p : Pair s h l x)
    (K : ∀ s', Only [l, h, t] s s' → Pair s' h l (x.rotateRight (k + 32)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (rorPair l h k t ++ rest)) s Q :=
  wp_rorPair h0 hk hlh hlt hht p.2 p.1 fun s' o e₁ e₂ => K s' o
    ⟨by rw [e₁, merge_eq _ _ h0 hk, lo_rotr' x (by omega) (by omega), show k + 32 - 32 = k by omega,
        show 64 - (k + 32) = 32 - k by omega],
      by rw [e₂, merge_eq _ _ h0 hk, hi_rotr' x (by omega) (by omega), show k + 32 - 32 = k by omega,
        show 64 - (k + 32) = 32 - k by omega]⟩

end

/-! ## `G` -/

/-- The registers `G` writes. -/
def temps : List Reg := [.eax, .ebx, .ecx, .edx, .edi, .ebp]

/-- Two 8-byte words at offsets `o` and `o'` do not overlap. -/
abbrev Sep8 (o o' : Nat) : Prop := o + 8 ≤ o' ∨ o' + 8 ≤ o

theorem Sep8.symm {o o' : Nat} (h : Sep8 o o') : Sep8 o' o := Or.symm h

/-- `s'` is `s` but for the registers `G` writes, and memory. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ∉ temps → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keep.only {s s₁ s₂ : State} {ds : List Reg} (k : Keep s s₁) (o : Only ds s₁ s₂)
    (h : ∀ r ∈ ds, r ∈ temps) : Keep s s₂ :=
  ⟨fun r hr => by rw [o.gpr r (fun hd => hr (h r hd)), k.gpr r hr], o.rd.trans k.rd, o.wr.trans k.wr⟩

theorem Keep.mupd {s s₁ s₂ : State} {m : Mem} (k : Keep s s₁) (u : Mupd s₁ s₂ m) : Keep s s₂ :=
  ⟨fun r hr => by rw [u.gpr, k.gpr r hr], u.rd.trans k.rd, u.wr.trans k.wr⟩

theorem Keep.trans {s s₁ s₂ : State} (k₁ : Keep s s₁) (k₂ : Keep s₁ s₂) : Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr⟩

theorem Keep.esi {s s' : State} {B : BitVec 32} (k : Keep s s') (h : s.gpr .esi = B) :
    s'.gpr .esi = B := (k.gpr _ (by decide)).trans h

theorem Keep.acc {s s' : State} {B : BitVec 32} {N : Nat} (k : Keep s s') (h : Acc s.wr B N) :
    Acc s'.wr B N := k.wr ▸ h

theorem _root_.VG.Proof.Sha512.X86.Pair.mupd {s s' : State} {m : Mem} {l h : Reg} {x : BitVec 64} (p : Pair s l h x)
    (u : Mupd s s' m) : Pair s' l h x :=
  ⟨by rw [u.gpr]; exact p.1, by rw [u.gpr]; exact p.2⟩

/-- The four words `G` computes, from `v[a], v[b], v[c], v[d]` and the message
words `x, y` (`Proof.Blake2.mix` for BLAKE2b). -/
abbrev gOut (va vb vc vd x y : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  Proof.Blake2.mix Spec.Blake2.b va vb vc vd x y

theorem g_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {a b c d x y : Nat}
    (ha : a + 8 ≤ 256) (hb : b + 8 ≤ 256) (hc : c + 8 ≤ 256) (hd : d + 8 ≤ 256)
    (hx : x + 8 ≤ 256) (hy : y + 8 ≤ 256)
    (sab : Sep8 a b) (sac : Sep8 a c) (sad : Sep8 a d) (sbc : Sep8 b c) (sbd : Sep8 b d)
    (scd : Sep8 c d) (syc : Sep8 y c) (syd : Sep8 y d)
    {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B 512) :
    WP isa (.block (g a b c d x y)) s fun s' => Keep s s' ∧
      rd64 s'.mem B a = (gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).1 ∧
      rd64 s'.mem B b = (gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).2.1 ∧
      rd64 s'.mem B c = (gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).2.2.1 ∧
      rd64 s'.mem B d = (gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).2.2.2 ∧
      (∀ o, o + 8 ≤ 512 → Sep8 a o → Sep8 b o → Sep8 c o → Sep8 d o →
        rd64 s'.mem B o = rd64 s.mem B o) ∧
      Frame [⟨B.setWidth 64, 256⟩] s.mem s'.mem := by
  rw [← List.append_nil (g a b c d x y)]
  unfold g
  simp only [List.append_assoc]
  -- a := a + b + x
  refine wp_ld (by decide) (by decide) h0 hA (by omega) fun s₁ o₁ p₁ => ?_
  have k₁ := (Keep.refl s).only o₁ (by decide)
  refine wp_add64m (by decide) (by decide) (k₁.esi h0) (k₁.acc hA) (by omega) p₁ fun s₂ o₂ p₂ => ?_
  have k₂ := k₁.only o₂ (by decide)
  refine wp_add64m (by decide) (by decide) (k₂.esi h0) (k₂.acc hA) (by omega) p₂ fun s₃ o₃ p₃ => ?_
  have k₃ := k₂.only o₃ (by decide)
  have e₃ : s₂.mem = s.mem := o₂.mem.trans o₁.mem
  rw [o₁.mem, e₃] at p₃
  -- d := (d ^ a) >>> 32
  refine wp_ld (by decide) (by decide) (k₃.esi h0) (k₃.acc hA) (by omega) fun s₄ o₄ p₄ => ?_
  have k₄ := k₃.only o₄ (by decide)
  have e₄ : s₃.mem = s.mem := o₃.mem.trans e₃
  rw [e₄] at p₄
  refine wp_xor64 (by decide) (by decide) p₄ (p₃.of_only o₄ (by decide) (by decide))
    fun s₅ o₅ p₅ => ?_
  have k₅ := k₄.only o₅ (by decide)
  have p₅' := p₅.swap
  -- c := c + d
  refine wp_ld (by decide) (by decide) (k₅.esi h0) (k₅.acc hA) (by omega) fun s₆ o₆ p₆ => ?_
  have k₆ := k₅.only o₆ (by decide)
  have e₆ : s₅.mem = s.mem := o₅.mem.trans (o₄.mem.trans e₄)
  rw [e₆] at p₆
  refine wp_add64 (by decide) (by decide) p₆ (p₅'.of_only o₆ (by decide) (by decide))
    fun s₇ o₇ p₇ => ?_
  have k₇ := k₆.only o₇ (by decide)
  refine wp_st (k₇.esi h0) (k₇.acc hA) (by omega) ((p₅'.of_only o₆ (by decide) (by decide)).of_only
    o₇ (by decide) (by decide)) fun s₈ u₈ => ?_
  have k₈ := k₇.mupd u₈
  have e₈ := u₈.mem
  rw [o₇.mem, o₆.mem, e₆] at e₈
  -- b := (b ^ c) >>> 24
  refine wp_ld (by decide) (by decide) (k₈.esi h0) (k₈.acc hA) (by omega) fun s₉ o₉ p₉ => ?_
  have k₉ := k₈.only o₉ (by decide)
  rw [e₈, rd64_write64_ne _ _ (by omega) (by omega) sbd.symm] at p₉
  refine wp_xor64 (by decide) (by decide) p₉ ((p₇.mupd u₈).of_only o₉ (by decide) (by decide))
    fun s₁₀ o₁₀ p₁₀ => ?_
  have k₁₀ := k₉.only o₁₀ (by decide)
  refine wp_st (k₁₀.esi h0) (k₁₀.acc hA) (by omega)
    (((p₇.mupd u₈).of_only o₉ (by decide) (by decide)).of_only o₁₀ (by decide) (by decide))
    fun s₁₁ u₁₁ => ?_
  have k₁₁ := k₁₀.mupd u₁₁
  have e₁₁ := u₁₁.mem
  rw [o₁₀.mem, o₉.mem, e₈] at e₁₁
  refine wp_rot (by decide) (by decide) (by decide) (by decide) (by decide) (p₁₀.mupd u₁₁)
    fun s₁₂ o₁₂ p₁₂ => ?_
  have k₁₂ := k₁₁.only o₁₂ (by decide)
  -- a := a + b + y
  have pa : Pair s₁₂ .eax .ebx _ :=
    ((((((((p₃.of_only o₄ (by decide) (by decide)).of_only o₅ (by decide) (by decide)).of_only o₆
      (by decide) (by decide)).of_only o₇ (by decide) (by decide)).mupd u₈).of_only o₉ (by decide)
      (by decide)).of_only o₁₀ (by decide) (by decide)).mupd u₁₁).of_only o₁₂ (by decide) (by decide)
  refine wp_add64 (by decide) (by decide) pa p₁₂ fun s₁₃ o₁₃ p₁₃ => ?_
  have k₁₃ := k₁₂.only o₁₃ (by decide)
  refine wp_add64m (by decide) (by decide) (k₁₃.esi h0) (k₁₃.acc hA) (by omega) p₁₃
    fun s₁₄ o₁₄ p₁₄ => ?_
  have k₁₄ := k₁₃.only o₁₄ (by decide)
  have e₁₃ := o₁₃.mem.trans (o₁₂.mem.trans e₁₁)
  rw [e₁₃, rd64_write64_ne _ _ (by omega) (by omega) syc.symm,
    rd64_write64_ne _ _ (by omega) (by omega) syd.symm] at p₁₄
  -- d := (d ^ a) >>> 16
  refine wp_ld (by decide) (by decide) (k₁₄.esi h0) (k₁₄.acc hA) (by omega) fun s₁₅ o₁₅ p₁₅ => ?_
  have k₁₅ := k₁₄.only o₁₅ (by decide)
  rw [o₁₄.mem, e₁₃, rd64_write64_ne _ _ (by omega) (by omega) scd,
    rd64_write64_self _ _ (by omega)] at p₁₅
  refine wp_xor64 (by decide) (by decide) p₁₅ (p₁₄.of_only o₁₅ (by decide) (by decide))
    fun s₁₆ o₁₆ p₁₆ => ?_
  have k₁₆ := k₁₅.only o₁₆ (by decide)
  refine wp_st (k₁₆.esi h0) (k₁₆.acc hA) (by omega)
    ((p₁₄.of_only o₁₅ (by decide) (by decide)).of_only o₁₆ (by decide) (by decide))
    fun s₁₇ u₁₇ => ?_
  have k₁₇ := k₁₆.mupd u₁₇
  have e₁₇ := u₁₇.mem
  rw [o₁₆.mem, o₁₅.mem, o₁₄.mem, e₁₃] at e₁₇
  refine wp_rot (by decide) (by decide) (by decide) (by decide) (by decide) (p₁₆.mupd u₁₇)
    fun s₁₈ o₁₈ p₁₈ => ?_
  have k₁₈ := k₁₇.only o₁₈ (by decide)
  -- c := c + d
  refine wp_ld (by decide) (by decide) (k₁₈.esi h0) (k₁₈.acc hA) (by omega) fun s₁₉ o₁₉ p₁₉ => ?_
  have k₁₉ := k₁₈.only o₁₉ (by decide)
  rw [o₁₈.mem, e₁₇, rd64_write64_ne _ _ (by omega) (by omega) sac,
    rd64_write64_self _ _ (by omega)] at p₁₉
  refine wp_add64 (by decide) (by decide) p₁₉ (p₁₈.of_only o₁₉ (by decide) (by decide))
    fun s₂₀ o₂₀ p₂₀ => ?_
  have k₂₀ := k₁₉.only o₂₀ (by decide)
  refine wp_st (k₂₀.esi h0) (k₂₀.acc hA) (by omega)
    ((p₁₈.of_only o₁₉ (by decide) (by decide)).of_only o₂₀ (by decide) (by decide))
    fun s₂₁ u₂₁ => ?_
  have k₂₁ := k₂₀.mupd u₂₁
  -- b := (b ^ c) >>> 63
  have pb : Pair s₂₁ .edx .ecx _ :=
    (((((((((p₁₂.of_only o₁₃ (by decide) (by decide)).of_only o₁₄ (by decide) (by decide)).of_only
      o₁₅ (by decide) (by decide)).of_only o₁₆ (by decide) (by decide)).mupd u₁₇).of_only o₁₈
      (by decide) (by decide)).of_only o₁₉ (by decide) (by decide)).of_only o₂₀ (by decide)
      (by decide)).mupd u₂₁)
  refine wp_xor64 (by decide) (by decide) pb (p₂₀.mupd u₂₁) fun s₂₂ o₂₂ p₂₂ => ?_
  have k₂₂ := k₂₁.only o₂₂ (by decide)
  refine wp_st (k₂₂.esi h0) (k₂₂.acc hA) (by omega)
    ((p₂₀.mupd u₂₁).of_only o₂₂ (by decide) (by decide)) fun s₂₃ u₂₃ => ?_
  have k₂₃ := k₂₂.mupd u₂₃
  refine wp_rot' (by decide) (by decide) (by decide) (by decide) (by decide) (p₂₂.mupd u₂₃)
    fun s₂₄ o₂₄ p₂₄ => ?_
  have k₂₄ := k₂₃.only o₂₄ (by decide)
  refine wp_st (k₂₄.esi h0) (k₂₄.acc hA) (by omega) p₂₄ fun s₂₅ u₂₅ => WP.block_nil ?_
  have k₂₅ := k₂₄.mupd u₂₅
  have e₂₅ := u₂₅.mem
  rw [o₂₄.mem, u₂₃.mem, o₂₂.mem, u₂₁.mem, o₂₀.mem, o₁₉.mem, o₁₈.mem, e₁₇] at e₂₅
  refine ⟨k₂₅, ?_, ?_, ?_, ?_, fun o ho h1 h2 h3 h4 => ?_, ?_⟩
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) sab.symm,
      rd64_write64_ne _ _ (by omega) (by omega) sac.symm,
      rd64_write64_ne _ _ (by omega) (by omega) sad.symm, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) sbc, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) sbd,
      rd64_write64_ne _ _ (by omega) (by omega) scd, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) h2,
      rd64_write64_ne _ _ (by omega) (by omega) h3, rd64_write64_ne _ _ (by omega) (by omega) h4,
      rd64_write64_ne _ _ (by omega) (by omega) h1, rd64_write64_ne _ _ (by omega) (by omega) h3,
      rd64_write64_ne _ _ (by omega) (by omega) h4]
  · rw [e₂₅]
    have hm : (⟨B.setWidth 64, 256⟩ : Region) ∈ [(⟨B.setWidth 64, 256⟩ : Region)] :=
      List.mem_singleton_self _
    have f : ∀ {m m' : Mem} {o : Nat} (v : BitVec 64), o + 8 ≤ 256 →
        Frame [⟨B.setWidth 64, 256⟩] m m' → Frame [⟨B.setWidth 64, 256⟩] m (write64 m' B o v) :=
      fun v ho h => frame_write64 h hm (by omega) ho v
    exact f _ hb (f _ hc (f _ hd (f _ ha (f _ hc (f _ hd (Frame.refl _ _))))))

end VG.Proof.Blake2.X86.CompressB
