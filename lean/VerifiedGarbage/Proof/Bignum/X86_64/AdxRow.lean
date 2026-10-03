import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring

/-!
# Multiword arithmetic on x86-64: a row of the BMI2/ADX multiplication

The blocks of a row (`blocks_ok`) add `a_i b + u m` to the window's `w` low
words and the carries, four words at a time.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## The blocks -/

/-- After `k` blocks of a row from `s₀`, the window at `e`: its `4 k` low
words and the carries are its old ones plus `X b + U m` over them. -/
structure BlkInv (s₀ : State) (B : Addr) (Z e eb eN : Nat) (k : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 (4 * k)
  out : Outside B e (8 * (4 * k)) s₀.mem t.mem
  val : wv t.mem B e (4 * k) + 2 ^ (64 * (4 * k)) * ((t.gpr .rcx).toNat + (t.gpr .rbp).toNat) =
    wv s₀.mem B e (4 * k) + (word s₀.mem B (e - 16)).toNat * wv s₀.mem B eb (4 * k) +
      (word s₀.mem B (e - 8)).toNat * wv s₀.mem B eN (4 * k) + (s₀.gpr .rcx).toNat + (s₀.gpr .rbp).toNat

theorem blkStep_ok {s₀ t : State} {B : Addr} {Z e eb eN w k : Nat} (hs : Scr s₀ B Z)
    (h8 : s₀.gpr .r8 = off B e) (h9 : s₀.gpr .r9 = off B eb) (h10 : s₀.gpr .r10 = off B eN)
    (hbx : s₀.gpr .rbx = BitVec.ofNat 64 w) (he : 16 ≤ e) (hw4 : w % 4 = 0) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z) (hZN : eN + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) (sN : eN + 8 * w ≤ e ∨ e + 8 * w ≤ eN) (hk : k < w / 4)
    (hI : BlkInv s₀ B Z e eb eN k t) :
    WP isa (.block Adx.block) t fun t' => t'.zf = some (decide (k + 1 = w / 4)) ∧ BlkInv s₀ B Z e eb eN (k + 1) t' := by
  have hn := hs.nowrap
  have hk4 : 4 * k + 4 ≤ w := by omega
  have kp := hI.keep
  refine WP.mono (block_ok (j := 4 * k) (w := w) hI.scr ((kp.gpr (by decide)).trans h8) ((kp.gpr (by decide)).trans h9)
    ((kp.gpr (by decide)).trans h10) hI.r14 ((kp.gpr (by decide)).trans hbx) he (by omega) (by omega) (by omega)
    (by omega) hw) fun t' ⟨hv, ho, h14, hz, k'⟩ => ⟨?_, ?_⟩
  · rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega)
  -- The words the block read, as in `s₀`.
  have rX : word t.mem B (e - 16) = word s₀.mem B (e - 16) := hI.out.word (by omega) (by omega)
  have rU : word t.mem B (e - 8) = word s₀.mem B (e - 8) := hI.out.word (by omega) (by omega)
  have rT : wv t.mem B (e + 8 * (4 * k)) 4 = wv s₀.mem B (e + 8 * (4 * k)) 4 := hI.out.wv (by omega) (by omega)
  have rB : wv t.mem B (eb + 8 * (4 * k)) 4 = wv s₀.mem B (eb + 8 * (4 * k)) 4 := hI.out.wv (by omega) (by omega)
  have rN : wv t.mem B (eN + 8 * (4 * k)) 4 = wv s₀.mem B (eN + 8 * (4 * k)) 4 := hI.out.wv (by omega) (by omega)
  have rL : wv t'.mem B e (4 * k) = wv t.mem B e (4 * k) := ho.wv (by omega) (by omega)
  rw [rX, rU, rT, rB, rN] at hv
  refine ⟨hI.scr.congr k'.2.2, (kp.trans k').mono (by simp), by rw [h14]; congr 1, ?_, ?_⟩
  · exact (hI.out.mono (o' := e) (n' := 8 * (4 * (k + 1))) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := e) (n' := 8 * (4 * (k + 1))) (by omega) (by omega))
  · have hval := hI.val
    rw [show 4 * (k + 1) = 4 * k + 4 by omega, wv_add, wv_add s₀.mem B e, wv_add s₀.mem B eb, wv_add s₀.mem B eN, rL,
      show 64 * (4 * k + 4) = 64 * (4 * k) + 256 by omega, Nat.pow_add]
    zify at hv hval ⊢
    linear_combination hval + 2 ^ (64 * (4 * k)) * hv

/-- The blocks: from `r14 = 0` and the carries 0, `X b + U m` added to the
window's `w` low words, with the carries out. -/
theorem blocks_ok {s₀ : State} {B : Addr} {Z e eb eN w : Nat} (hs : Scr s₀ B Z)
    (h8 : s₀.gpr .r8 = off B e) (h9 : s₀.gpr .r9 = off B eb) (h10 : s₀.gpr .r10 = off B eN)
    (hbx : s₀.gpr .rbx = BitVec.ofNat 64 w) (h14 : s₀.gpr .r14 = BitVec.ofNat 64 0) (he : 16 ≤ e)
    (hw4 : w % 4 = 0) (hw1 : 4 ≤ w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z) (hZN : eN + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) (sN : eN + 8 * w ≤ e ∨ e + 8 * w ≤ eN) :
    WP isa (.loop (.block Adx.block) .ne) s₀ (BlkInv s₀ B Z e eb eN (w / 4)) :=
  wp_upto (a := 0) (N := w / 4) (by omega) (BlkInv s₀ B Z e eb eN)
    (fun k _ hk t hI => blkStep_ok hs h8 h9 h10 hbx he hw4 hw hZ hZb hZN sb sN hk hI) (fun _ h => h)
    ⟨hs, Keep.refl _ _, h14, Outside.refl _ _ _ _, by simp [wv]⟩

/-! ## The row's start -/

theorem off_add16 (B : Addr) (q : Nat) : off B q + 16 = off B (q + 16) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- `a`'s base less the first window's: `rowBase`. -/
theorem rowBase_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {a : Nat} (ha : a < 8) :
    WP isa (.block (rowBase a)) s fun t =>
      t.gpr .rax = off B (slot w a) - off B (slot w aAcc + 16) ∧ t.mem = s.mem ∧ Keep [.rax, .rdx] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = off B (slot w a) - off B (slot w aAcc + 16) ∧
    t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold rowBase
  xrun [State.ea, hdr, hdi, hdrOff, hl (sArr a) (by unfold sArr; omega), hl (sArr aAcc) (by decide),
    hH.harr a ha, hH.harr aAcc (by decide), off_add16]

/-- `[rax + r8]` is `a_i`. -/
theorem rowX_addr (B : Addr) (p q d : Nat) :
    off B p - off B (q + 16) + off B (q + 16 + d) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = off B (p + d) := by
  rw [BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    show off B (q + 16 + d) = off B (q + 16) + BitVec.ofNat 64 d by simp only [off, BitVec.add_assoc, BitVec.ofNat_add],
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem rowX_addr' (B : Addr) {p q d e : Nat} (he : e = q + 16 + d) :
    off B p - off B (q + 16) + off B e * 1#64 = off B (p + d) := by
  have := rowX_addr B p q d
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  subst he; exact this

theorem off_below (B : Addr) {e d : Nat} (hd : d ≤ e) : off B e + BitVec.ofInt 64 (-(d : Int)) = off B (e - d) := by
  simp only [off, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.sub_eq_add_neg, show e = (e - d) + d by omega, BitVec.ofNat_add,
    BitVec.add_sub_cancel, show e - d + d - d = e - d by omega]

theorem off_m16 (B : Addr) {e : Nat} (hd : 16 ≤ e) : off B e + BitVec.ofInt 64 (-16) = off B (e - 16) :=
  off_below B (d := 16) hd
theorem off_m8 (B : Addr) {e : Nat} (hd : 8 ≤ e) : off B e + BitVec.ofInt 64 (-8) = off B (e - 8) :=
  off_below B (d := 8) hd

/-- `u` for the row's multiplier `X`, `b₀`, the window's low word `T₀` and
`-m⁻¹`. -/
def rowU (X b₀ T₀ minv : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.ofNat 64 (X.toNat * b₀.toNat) + T₀).toNat * minv.toNat)

/-- `rowHead`: `a_i` and `u` below the window, the carries and the word 0. -/
theorem rowHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {a b i e : Nat} (ha : a < 8) (hb : b < 8)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (he : e = slot w aAcc + 16 + 8 * i) (hi : i < w)
    (hax : s.gpr .rax = off B (slot w a) - off B (slot w aAcc + 16)) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B (slot w b)) :
    WP isa (.block rowHead) s fun t =>
      t.mem = (s.mem.writeW (off B (e - 16)) (word s.mem B (slot w a + 8 * i))).writeW (off B (e - 8))
        (rowU (word s.mem B (slot w a + 8 * i)) (word s.mem B (slot w b)) (word s.mem B e) minv) ∧
      t.gpr .rcx = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧
      Keep [.rdx, .rsi, .rax, .rcx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) ha
  have hB := slot_le (w := w) hb
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hge := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have sbX : slot w b + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w b := by
    have := slot_sep (w := w) hb1; have := slot_sep (w := w) hb2; unfold slot aAcc aTmp at *; omega
  have o1 := writeW_outside s.mem B (word s.mem B (slot w a + 8 * i)) (d := e - 16) (by omega)
  have r1 : (s.mem.writeW (off B (e - 16)) (word s.mem B (slot w a + 8 * i))).readW (off B (slot w b)) 64 =
      word s.mem B (slot w b) := o1.word (by omega) (by omega)
  have r2 : (s.mem.writeW (off B (e - 16)) (word s.mem B (slot w a + 8 * i))).readW (off B e) 64 =
      word s.mem B e := o1.word (by omega) (by omega)
  have r3 : (s.mem.writeW (off B (e - 16)) (word s.mem B (slot w a + 8 * i))).readW (off B (8 * sMinv)) 64 = minv :=
    (o1.word (by unfold sMinv; omega) (by unfold sMinv; omega)).trans hH.hminv
  refine WP.mono (WP.keep [.rdx, .rsi, .rax, .rcx, .rbp, .r14] (Q := fun t =>
      t.mem = (s.mem.writeW (off B (e - 16)) (word s.mem B (slot w a + 8 * i))).writeW (off B (e - 8))
        (rowU (word s.mem B (slot w a + 8 * i)) (word s.mem B (slot w b)) (word s.mem B e) minv) ∧
      t.gpr .rcx = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold rowHead
  xrun [State.ea, hdr, at0, xSlot, uSlot, hdi, hdrOff, hax, h8, h9, execMulx, rowX_addr' B (p := slot w a) he,
    off_m16 B (show 16 ≤ e by omega), off_m8 B (show 8 ≤ e by omega),
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld (show slot w a + 8 * i + 8 ≤ Z by omega),
    hs.st (show e - 16 + 8 ≤ Z by omega), hs.st (show e - 8 + 8 ≤ Z by omega), hs.ld (show slot w b + 8 ≤ Z by omega),
    hs.ld (show e + 8 ≤ Z by omega), hs.ld (show 8 * sMinv + 8 ≤ Z by unfold sMinv; omega), r1, r2, r3, rowU]

/-! ## The row's end -/

theorem off_add8 (B : Addr) (q : Nat) : off B q + 8 = off B (q + 8) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem off_sub_beq (B : Addr) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (off B x - off B y == 0) = decide (x = y) := by
  rw [sub_beq_zero]
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have ox := ofs_off B (d := x) (i := 0) (by omega)
    have oy := ofs_off B (d := y) (i := 0) (by omega)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at ox oy
    rw [← h', ox] at oy
    omega

/-- `rowTail`: the carries added into the window's words `w` and `w + 1`, and
the window up a word. -/
theorem rowTail_ok {s : State} {B : Addr} {Z e w : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 w) (hZ : e + 8 * w + 16 ≤ Z) :
    WP isa (.block rowTail) s fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (off B (e + 8 * w)) lo).writeW (off B (e + 8 * w + 8)) hi ∧
      ((word s.mem B (e + 8 * w)).toNat + 2 ^ 64 * (word s.mem B (e + 8 * w + 8)).toNat +
          (s.gpr .rcx).toNat + (s.gpr .rbp).toNat < 2 ^ 128 →
        lo.toNat + 2 ^ 64 * hi.toNat = (word s.mem B (e + 8 * w)).toNat +
          2 ^ 64 * (word s.mem B (e + 8 * w + 8)).toNat + (s.gpr .rcx).toNat + (s.gpr .rbp).toNat) ∧
      t.gpr .r8 = off B (e + 8) ∧ Keep [.rax, .rsi, .r8] s t := by
  have hn := hs.nowrap
  generalize hTw : word s.mem B (e + 8 * w) = Tw
  generalize hT1 : word s.mem B (e + 8 * w + 8) = T1
  generalize hc : s.gpr .rcx = c
  generalize hp : s.gpr .rbp = p
  have hX : ∀ v, (s.mem.writeW (off B (e + 8 * w)) v).readW (off B (e + 8 * w + 8)) 64 = T1 := fun v =>
    ((writeW_outside s.mem B v (by omega)).word (Or.inr (Nat.le_refl _)) (by omega)).trans hT1
  refine WP.mono (WP.keep [.rax, .rsi, .r8] (Q := fun t =>
      t.mem = (s.mem.writeW (off B (e + 8 * w)) (Tw + c + p)).writeW (off B (e + 8 * w + 8))
        (T1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ Tw.toNat + c.toNat))).setWidth 64 + 0 +
          (BitVec.ofBool (decide (2 ^ 64 ≤ (Tw + c).toNat + p.toNat))).setWidth 64) ∧
      t.gpr .r8 = off B (e + 8)) ?_ rfl) fun t ⟨⟨hm, h8'⟩, k⟩ => ⟨_, _, hm, fun hfit => by
      have e1 := addc_toNat Tw T1 c (by omega)
      have e2 := addc_toNat (Tw + c) (T1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ Tw.toNat + c.toNat))).setWidth 64) p
        (by omega)
      omega, h8', k⟩
  unfold rowTail
  xrun [State.ea, ix, addr0 h8 h14, addr8 h8 h14, hs.ld (show e + 8 * w + 8 ≤ Z by omega),
    hs.st (show e + 8 * w + 8 ≤ Z by omega), hs.ld (show e + 8 * w + 8 + 8 ≤ Z by omega),
    hs.st (show e + 8 * w + 8 + 8 ≤ Z by omega), hTw, hT1, hc, hp, sx0, show s.gpr .r8 + 8 = off B (e + 8) by rw [h8, off_add8]]

/-- `rowEnd`: ZF set when the window `r8 = e` has reached `aTmp`. -/
theorem rowEnd_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {e : Nat} (h8 : s.gpr .r8 = off B e) (heZ : e < Z) :
    WP isa (.block rowEnd) s fun t =>
      t.zf = some (decide (e = slot w aTmp)) ∧ t.mem = s.mem ∧ t.gpr .r8 = off B e ∧ Keep [.rax, .r8] s t := by
  have hn := hs.nowrap
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.zf = some (decide (e = slot w aTmp)) ∧ t.mem = s.mem ∧
      t.gpr .r8 = off B e) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold rowEnd
  xrun [State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * sArr aTmp + 8 ≤ Z by have := hdr_lt_slot w 8 (show sArr aTmp < 32 by decide); omega),
    hH.harr aTmp (by decide), h8, off_sub_beq B (show e < 2 ^ 64 by omega) (show slot w aTmp < 2 ^ 64 by omega)]

/-! ## A row -/

/-- `u` makes the low word of `T + X b + u m` zero. -/
theorem rowU_low (X b₀ T₀ m₀ minv : BitVec 64) (h : (m₀.toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    (T₀.toNat + X.toNat * b₀.toNat + (rowU X b₀ T₀ minv).toNat * m₀.toNat) % 2 ^ 64 = 0 := by
  have hl := mont_low ((X.toNat * b₀.toNat % 2 ^ 64 + T₀.toNat) % 2 ^ 64) minv.toNat m₀.toNat h
  simp only [rowU, BitVec.toNat_ofNat, BitVec.toNat_add] at hl ⊢
  generalize X.toNat * b₀.toNat = P at hl ⊢
  generalize ((P % 2 ^ 64 + T₀.toNat) % 2 ^ 64 * minv.toNat % 2 ^ 64) * m₀.toNat = Q at hl ⊢
  omega

/-- A number's low word and the rest. -/
theorem wv_low (m : Mem) (B : Addr) (d n : Nat) :
    wv m B d (n + 1) = (word m B d).toNat + 2 ^ 64 * wv m B (d + 8) n := by
  rw [Nat.add_comm n 1, wv_add]; simp [wv]

/-- The header, after changes above it. -/
theorem Hdr.of_outside {m m' : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv) {o n : Nat}
    (h : Outside B o n m m') (ho : hdrBytes ≤ o) : Hdr m' B w minv := by
  have hh : ∀ i < 32, word m' B (8 * i) = word m B (8 * i) := fun i hi =>
    h.word (Or.inl (by have := hdr_lt_slot w 0 hi; unfold slot at this; omega)) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- Row `i` of `a`, with the window at `e`: `2⁶⁴ T' = T + a_i b + u m` for the
window `T'` a word up, if the word above the window is zero. -/
theorem row_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {a b i e : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (he : e = slot w aAcc + 16 + 8 * i) (hi : i < w) (hw4 : w % 4 = 0) (hw1 : 4 ≤ w) (hw : w < 2 ^ 60)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B (slot w b)) (h10 : s.gpr .r10 = off B (slot w aN))
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) :
    WP isa (row a) s fun t =>
      (((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
        word s.mem B (e + 8 * (w + 2)) = 0 →
        wv s.mem B e (w + 2) < 2 * wv s.mem B (slot w aN) w →
        wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w → ∃ u < 2 ^ 64, 2 ^ 64 * wv t.mem B (e + 8) (w + 2) = wv s.mem B e (w + 2) +
        (word s.mem B (slot w a + 8 * i)).toNat * wv s.mem B (slot w b) w + u * wv s.mem B (slot w aN) w) ∧
      Outside B (e - 16) (8 * (w + 4)) s.mem t.mem ∧ t.gpr .r8 = off B (e + 8) ∧
      t.zf = some (decide (i + 1 = w)) ∧
      Keep [.rax, .rdx, .rsi, .rcx, .rbp, .r14, .r11, .r12, .r13, .r15, .r8] s t := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) ha
  have hBs := slot_le (w := w) hb
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hTs := slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hge := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have hg0 : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  have sbX : slot w b + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w b := by
    have := slot_sep (w := w) hb1; have := slot_sep (w := w) hb2; unfold slot aAcc aTmp at *; omega
  have saX : slot w a + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w a := by
    have := slot_sep (w := w) ha1; have := slot_sep (w := w) ha2; unfold slot aAcc aTmp at *; omega
  have sNX : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hw4' : 4 * (w / 4) = w := by omega
  unfold row
  -- `a`'s base.
  refine WP.seq (WP.mono (rowBase_ok hs hdi hH hZ ha) fun s₁ ⟨hax, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  -- `a_i`, `u`.
  refine WP.seq (WP.mono (rowHead_ok hs₁ ((k₁.gpr (by decide)).trans hdi) (hm₁ ▸ hH) hZ ha hb hb1 hb2 he hi hax
    ((k₁.gpr (by decide)).trans h8) ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨hm₂, hcx, hbp, h14, k₂⟩ => ?_)
  rw [hm₁] at hm₂
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  generalize hX : word s.mem B (slot w a + 8 * i) = X at hm₂
  generalize hU : rowU X (word s.mem B (slot w b)) (word s.mem B e) minv = U at hm₂
  have o₂ : Outside B (e - 16) 16 s.mem s₂.mem := by
    rw [hm₂]
    exact ((writeW_outside s.mem B X (d := e - 16) (by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ B U (d := e - 8) (by omega)).mono (by omega) (by omega))
  have wX : word s₂.mem B (e - 16) = X := by
    rw [hm₂, (writeW_outside _ B U (d := e - 8) (by omega)).word (by omega) (by omega), word_writeW_self]
  have wU : word s₂.mem B (e - 8) = U := by rw [hm₂, word_writeW_self]
  -- The blocks.
  refine WP.seq (WP.mono (blocks_ok hs₂ ((k12.gpr (by decide)).trans h8) ((k12.gpr (by decide)).trans h9)
    ((k12.gpr (by decide)).trans h10) ((k12.gpr (by decide)).trans hbx) h14 (by omega) hw4 hw1 hw (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun s₃ hI => ?_)
  have hval := hI.val
  rw [hw4', wX, wU, hcx, hbp, o₂.wv (by omega) (by omega), o₂.wv (by omega) (by omega),
    o₂.wv (by omega) (by omega), show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at hval
  have k3 := hI.keep
  have o₃ : Outside B (e - 16) (8 * (w + 4)) s.mem s₃.mem :=
    (o₂.mono (o' := e - 16) (n' := 8 * (w + 4)) (Nat.le_refl _) (by omega)).trans
      (hI.out.mono (o' := e - 16) (n' := 8 * (w + 4)) (by omega) (by rw [hw4']; omega))
  have wTw : word s₃.mem B (e + 8 * w) = word s.mem B (e + 8 * w) :=
    (hI.out.word (by rw [hw4']; omega) (by omega)).trans (o₂.word (by omega) (by omega))
  have wT1 : word s₃.mem B (e + 8 * w + 8) = word s.mem B (e + 8 * w + 8) :=
    (hI.out.word (by rw [hw4']; omega) (by omega)).trans (o₂.word (by omega) (by omega))
  -- The bound: the sum fits in `w + 2` words.
  have hN := wv_lt s.mem B (slot w aN) w
  have hXl := X.isLt
  have hUl := U.isLt
  have h2 := wv_top2 s.mem B e w
  have hR : 2 ^ (64 * w) * ((word s.mem B (e + 8 * w)).toNat + 2 ^ 64 * (word s.mem B (e + 8 * w + 8)).toNat +
      (s₃.gpr .rcx).toNat + (s₃.gpr .rbp).toNat) + wv s₃.mem B e w =
      wv s.mem B e (w + 2) + X.toNat * wv s.mem B (slot w b) w + U.toNat * wv s.mem B (slot w aN) w := by
    rw [h2]; zify at hval ⊢; linear_combination hval
  -- The carries into words `w` and `w + 1`.
  have hs₃ := hI.scr
  have k123 := k12.trans k3
  refine WP.seq (WP.mono (rowTail_ok (w := w) hs₃ ((k123.gpr (by decide)).trans h8) (by rw [hI.r14, hw4'])
    (by omega)) fun s₄ ⟨lo, hi', hm₄, hlh, h8₄, k₄⟩ => ?_)
  rw [wTw, wT1] at hlh
  have o₄ : Outside B (e + 8 * w) 16 s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((writeW_outside s₃.mem B lo (d := e + 8 * w) (by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ B hi' (d := e + 8 * w + 8) (by omega)).mono (by omega) (by omega))
  have o₄' : Outside B (e - 16) (8 * (w + 4)) s.mem s₄.mem :=
    o₃.trans (o₄.mono (o' := e - 16) (n' := 8 * (w + 4)) (by omega) (by omega))
  -- The test.
  have hs₄ := hs₃.congr k₄.2.2
  refine WP.mono (rowEnd_ok hs₄ ((k123.trans k₄).gpr (by decide) |>.trans hdi) (hH.of_outside o₄' (by omega)) hZ
    h8₄ (by omega)) fun t ⟨hz, hmt, h8t, k₅⟩ => ?_
  have ot : Outside B (e - 16) (8 * (w + 4)) s.mem t.mem := hmt ▸ o₄'
  refine ⟨fun hinv htop hT hB => ⟨U.toNat, hUl, ?_⟩, ot, h8t, by rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega),
    (((k123.trans k₄).trans k₅)).mono (by simp)⟩
  have hsum := VG.Proof.Bignum.round_sum_lt hT hXl hB hUl
  have hfit : (word s.mem B (e + 8 * w)).toNat + 2 ^ 64 * (word s.mem B (e + 8 * w + 8)).toNat +
      (s₃.gpr .rcx).toNat + (s₃.gpr .rbp).toNat < 2 ^ 128 := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * w)) ?_
    have : 2 ^ 65 * wv s.mem B (slot w aN) w ≤ 2 ^ (64 * w) * 2 ^ 128 := by
      rw [Nat.mul_comm (2 ^ (64 * w))]; exact Nat.mul_le_mul (by decide) (by omega)
    omega
  replace hlh := hlh hfit
  have hV : wv s₄.mem B e (w + 2) = wv s.mem B e (w + 2) + X.toNat * wv s.mem B (slot w b) w +
      U.toNat * wv s.mem B (slot w aN) w := by
    rw [wv_top2, hm₄, word_writeW_self,
      (writeW_outside _ B hi' (d := e + 8 * w + 8) (by omega)).word (Or.inl (Nat.le_refl _)) (by omega),
      word_writeW_self, (writeW_outside _ B hi' (d := e + 8 * w + 8) (by omega)).wv (Or.inl (by omega)) (by omega),
      (writeW_outside _ B lo (d := e + 8 * w) (by omega)).wv (Or.inl (Nat.le_refl _)) (by omega), hlh, ← hR]
    ring
  rw [← hmt] at hV
  -- The low word is zero, and the word above the window too.
  have hlow : wv t.mem B e (w + 2) % 2 ^ 64 = 0 := by
    rw [hV]
    have dT := wv_low s.mem B e (w + 1)
    have dB := wv_low s.mem B (slot w b) (w - 1)
    have dN := wv_low s.mem B (slot w aN) (w - 1)
    rw [show w - 1 + 1 = w by omega] at dB dN
    rw [dT, dB, dN]
    have := rowU_low X (word s.mem B (slot w b)) (word s.mem B e) (word s.mem B (slot w aN)) minv hinv
    rw [hU] at this
    generalize wv s.mem B (e + 8) (w + 1) = A' at *
    generalize wv s.mem B (slot w b + 8) (w - 1) = B' at *
    generalize wv s.mem B (slot w aN + 8) (w - 1) = N' at *
    rw [show (word s.mem B e).toNat + 2 ^ 64 * A' + X.toNat * ((word s.mem B (slot w b)).toNat + 2 ^ 64 * B') +
        U.toNat * ((word s.mem B (slot w aN)).toNat + 2 ^ 64 * N') =
        (word s.mem B e).toNat + X.toNat * (word s.mem B (slot w b)).toNat +
          U.toNat * (word s.mem B (slot w aN)).toNat + 2 ^ 64 * (A' + X.toNat * B' + U.toNat * N') by ring,
      Nat.add_mul_mod_self_left, this]
  have htop' : word t.mem B (e + 8 * (w + 2)) = 0 := (ot.word (by omega) (by omega)).trans htop
  have d3 := wv_low t.mem B e (w + 2)
  rw [wv, htop'] at d3
  have := (word t.mem B e).isLt
  rw [← hV]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at d3
  omega

end VG.Proof.Bignum.X86_64
