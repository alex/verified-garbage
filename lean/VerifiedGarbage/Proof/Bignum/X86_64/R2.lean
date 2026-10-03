import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import Mathlib.Tactic.Positivity

/-!
# Multiword arithmetic on x86-64: `R² mod m`

* `setWord o i`: `[o] := rdx · 2^(64 i)` (`setWord_ok`).
* `topBit`: the top bit of the nonzero `rax`: `rdx := 2^j`, `rcx := 64 - j`
  (`topBit_ok`).
* `doubles`: `[o] := 2^c [o] mod m` for the count `c` in `rcx` (`doubles_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `[o] := v 2^(64 i)` for `v` in `rdx` and the word index `i` in `ri`. -/
theorem setWord_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {o : Nat} (ho : o < 8) {ri : Reg} (hri : ri ∉ [.rax, .r8, .r14])
    {i : Nat} (hi : i < w) (hix : s.gpr ri = BitVec.ofNat 64 i) :
    WP isa (setWord o ri) s fun t =>
      wv t.mem B (slot w o) w = (s.gpr .rdx).toNat * 2 ^ (64 * i) ∧
      Outside B (slot w o) (8 * (w + 2)) s.mem t.mem ∧ Keep [.rax, .r8, .r14] s t := by
  have hn := hs.nowrap
  have sl : slot w o + 8 * (w + 2) ≤ Z := (slot_le ho).trans hZ
  unfold setWord
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off B (slot w o) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * sArr o + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sArr o < 32 by unfold sArr; omega); omega), hH.harr o ho]) rfl)
    fun s₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroAccLoop_ok (hs.congr k₁.2.2) h8 ((k₁.gpr (by decide)).trans h12) hw hw' sl)
    fun s₂ ⟨hz, ho₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have s₂8 : s₂.gpr .r8 = off B (slot w o) := (k₂.gpr (by decide)).trans h8
  have s₂i : s₂.gpr ri = BitVec.ofNat 64 i := (k12.gpr (fun h => hri ((List.Perm.swap Reg.rax Reg.r8 [Reg.r14]).mem_iff.1 h))).trans hix
  have s₂dx : s₂.gpr .rdx = s.gpr .rdx := k12.gpr (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (off B (slot w o + 8 * i)) (s.gpr .rdx))
    (by xrun [State.ea, ix, addr0 s₂8 s₂i, (hs.congr (k12.2.2)).st (show slot w o + 8 * i + 8 ≤ Z by omega),
      s₂dx]) rfl) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k12.trans k).mono (by decide)⟩
  · -- `[o]` is zero but word `i`.
    have hz' := (wv_eq_zero_iff _ _ _ _).mp hz
    rw [wv_single t.mem B (slot w o) w hi fun q hq hne => by
      rw [hm, (writeW_outside s₂.mem B _ (by omega)).word (by omega) (by omega)]
      exact hz' q (by omega), hm, word_writeW_self]
  · rw [hm]
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega)]
    exact ho₂ x hx |>.trans (by rw [hm₁])

/-! ## The top bit -/

theorem shr1_ofNat (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem cmp1_eq (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n - 1 == 0) = decide (n = 1) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
  exact ofNat_sub_beq hn (by decide)

theorem div_pow_succ (T j : Nat) : T / 2 ^ j / 2 = T / 2 ^ (j + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- `topBit`: `rdx := 2^j`, `rcx := 64 - j` for `j` the top bit of `rax ≠ 0`. -/
theorem topBit_ok {s : State} {T : Nat} (hT : s.gpr .rax = BitVec.ofNat 64 T) (hT0 : 0 < T)
    (hT1 : T < 2 ^ 64) :
    WP isa topBit s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (2 ^ T.log2) ∧ t.gpr .rcx = BitVec.ofNat 64 (64 - T.log2) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hL : T.log2 < 64 := (Nat.log2_lt (by omega)).mpr hT1
  have hle := Nat.log2_self_le (n := T) (by omega)
  have hlt := Nat.lt_log2_self (n := T)
  unfold topBit
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 (2 ^ 0) ∧
      t.gpr .rcx = BitVec.ofNat 64 (64 - 0) ∧ t.zf = some (decide (T = 1)) ∧ t.mem = s.mem ∧
      t.gpr .rax = BitVec.ofNat 64 (T / 2 ^ 0))
    (by xrun [hT, cmp1_eq T hT1]; simp) rfl) fun s₁ ⟨⟨hdx, hcx, hz, hm, s₁ax⟩, k₁⟩ => ?_)
  by_cases h1 : T = 1
  · subst h1
    refine WP.ite true (by simp [eval, hz]) (fun _ => WP.block_nil ⟨?_, ?_, hm, k₁.mono (by decide)⟩) (by simp)
    · rw [hdx]; rfl
    · rw [hcx]; rfl
  refine WP.ite false (by simp [eval, hz, h1]) (by simp) (fun _ => ?_)
  -- The loop: after `j` halvings, `rax = T / 2^j`, `rdx = 2^j`, `rcx = 64 - j`.
  refine WP.loop (M := isa) (fun n t => ∃ j, n = T.log2 - j ∧ j < T.log2 ∧
      t.gpr .rax = BitVec.ofNat 64 (T / 2 ^ j) ∧ t.gpr .rdx = BitVec.ofNat 64 (2 ^ j) ∧
      t.gpr .rcx = BitVec.ofNat 64 (64 - j) ∧ t.mem = s.mem ∧ Keep [.rax, .rcx, .rdx] s t) ?_ _ s₁
    ⟨0, rfl, by
      have : 2 ^ 1 ≤ T := by omega
      exact (Nat.le_log2 (by omega)).mpr this, s₁ax, hdx, hcx, hm, k₁.mono (by decide)⟩
  rintro n t ⟨j, rfl, hj, hax, hdx', hcx', hm', k⟩
  have hTj : T / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1
  have hpj : 2 ^ j < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (T / 2 ^ (j + 1)) ∧
      t'.gpr .rdx = BitVec.ofNat 64 (2 ^ (j + 1)) ∧ t'.gpr .rcx = BitVec.ofNat 64 (64 - (j + 1)) ∧
      t'.zf = some (decide (T / 2 ^ (j + 1) = 1)) ∧ t'.mem = t.mem) (by
    xrun [hax, hdx', hcx', shr1_ofNat _ hTj, div_pow_succ, ← BitVec.ofNat_add]
    refine ⟨by rw [Nat.pow_succ, Nat.mul_two], ?_, ?_⟩
    · rw [ofNat64_pred (by omega) (by omega)]; congr 1
    · exact ofNat_sub_beq (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1) (by decide)) rfl) fun t' ⟨⟨hax', hdx'', hcx'', hz', hm''⟩, k'⟩ => ?_
  -- `T / 2^(j+1) = 1` iff `j + 1` is the top bit.
  have key : T / 2 ^ (j + 1) = 1 ↔ j + 1 = T.log2 := by
    constructor
    · intro h
      have h1 : 2 ^ (j + 1) ≤ T := by
        have := Nat.div_mul_le_self T (2 ^ (j + 1)); rw [h, Nat.one_mul] at this; exact this
      have h2 : T < 2 ^ (j + 2) := by
        have := Nat.lt_mul_div_succ T (show 0 < 2 ^ (j + 1) by positivity)
        rw [h] at this; rw [Nat.pow_succ]; omega
      have := (Nat.le_log2 (by omega)).mpr h1
      have := (Nat.log2_lt (by omega)).mpr h2
      omega
    · intro h
      rw [← h] at hle hlt
      exact Nat.div_eq_of_lt_le (by rw [Nat.one_mul]; exact hle) (by rw [Nat.pow_succ] at hlt; omega)
  by_cases he : j + 1 = T.log2
  · refine .inl ⟨by simp [eval, hz', key.mpr he], ?_, ?_, hm''.trans hm', (k.trans k').mono (by decide)⟩
    · rw [hdx'', he]
    · rw [hcx'', he]
  · refine .inr ⟨by simp [eval, hz', (not_congr key).mpr he], T.log2 - (j + 1), by omega, j + 1, rfl, by omega,
      hax', hdx'', hcx'', hm''.trans hm', (k.trans k').mono (by decide)⟩

/-! ## Repeated doubling -/

/-- After `j` of `c` doublings of `O` modulo `N` from `s`, counted in slot
`sl`. -/
structure DblsInv (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (mo acc tmp o sl c O N j : Nat)
    (t : State) : Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  hdr : Hdr t.mem B w minv
  cnt : word t.mem B (8 * sl) = BitVec.ofNat 64 (c - j)
  ov : wv t.mem B (slot w o) w = 2 ^ j * O % N
  nv : wv t.mem B (slot w mo) w = N
  frm : Frm B [(slot w acc, 8 * (w + 2)), (slot w tmp, 8 * (w + 2)), (slot w o, 8 * (w + 2)), (8 * sl, 8)]
    s.mem t.mem
  keep : Keep mmRegs s t

/-- `doubles`' count of `double`s. -/
abbrev dblCount (sl : Nat) : List Instr :=
  [.mov .rcx (.mem (hdr sl)), .alu .sub .rcx (.imm 1), .store (hdr sl) .rcx]

/-- One doubling of `doubles`, and its count. -/
theorem dblIter_ok {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {c O N j : Nat} (hc' : c < 2 ^ 31) (hN0 : 0 < N) (hj : j < c)
    (hI : DblsInv s B Z w minv mo acc tmp o sl c O N j t) :
    WP isa (.seq (double mo acc tmp o) (.block (dblCount sl))) t fun t' =>
      t'.zf = some (decide (j + 1 = c)) ∧ DblsInv s B Z w minv mo acc tmp o sl c O N (j + 1) t' := by
  have hn := hI.scr.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => (slot_le hj).trans hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hhs : ∀ j, 8 * sl + 8 ≤ slot w j := fun j => hdr_lt_slot w j hsl'
  refine WP.seq (WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 (by
      rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t₁ ⟨hv₁, ha₁, k₁'⟩ => ?_)
  have hst₁ := hI.scr.congr k₁'.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁'.gpr (by decide)).trans hI.rdi
  have hH₁ := ha₁.hdr hI.hdr
  have hcnt₁ : word t₁.mem B (8 * sl) = BitVec.ofNat 64 (c - j) := by
    rw [ha₁.word_eq (fun j' hj' => Or.inl (by simp at hj'; rcases hj' with rfl | rfl | rfl <;> exact hhs _))
      (by omega), hI.cnt]
  have hld : InRegions (t₁.rd ++ t₁.wr) (off B (8 * sl)) 8 := hst₁.ld (by have := hhs 8; omega)
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.mem = t₁.mem.writeW (off B (8 * sl))
      (BitVec.ofNat 64 (c - (j + 1))) ∧ t'.zf = some (decide (c - (j + 1) = 0))) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hld, hst₁.st (show 8 * sl + 8 ≤ Z by have := hhs 8; omega), hcnt₁,
      ofNat64_pred (show 1 ≤ c - j by omega) (by omega), ofNat64_beq_zero (show c - j - 1 < 2 ^ 64 by omega)]
    exact ⟨by congr 2, by congr 1⟩) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨?_, ?_⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  have o' : Outside B (8 * sl) 8 t₁.mem t'.mem := by rw [hm']; exact writeW_outside _ _ _ (by omega)
  refine ⟨hst₁.congr k'.2.2, (k'.gpr (by decide)).trans hdi₁, by rw [hm']; exact Hdr.store hH₁ hsl hsl' _,
    by rw [hm', word_writeW_self], ?_, ?_, ?_, ((hI.keep.trans k₁').trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs o; omega) (by have := sl8 o ho; omega), hv₁, hI.ov, hI.nv, Nat.mul_mod,
      Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.pow_succ']
  · rw [o'.wv (by have := hhs mo; omega) (by have := sl8 mo hmo; omega),
      ha₁.wv_eq (fun j' hj' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
        rcases hj' with rfl | rfl | rfl
        · have := sp d1; omega
        · have := sp d6; omega
        · have := sp d8; omega) (by have := sl8 mo hmo; omega), hI.nv]
  · exact (hI.frm.trans (Frm.of_arrays ha₁ (by simp))).trans (Frm.of_outside o' (by simp))

/-- `doubles`' start: the count `c` into slot `sl`. -/
theorem dblStart_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {mo acc tmp o sl : Nat}
    (hmo : mo < 8) (ho : o < 8) (hsl : 16 ≤ sl) (hsl' : sl < 32) {c : Nat}
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hO : wv s.mem B (slot w o) w < wv s.mem B (slot w mo) w) :
    WP isa (.block [.store (hdr sl) .rcx]) s (DblsInv s B Z w minv mo acc tmp o sl c
      (wv s.mem B (slot w o) w) (wv s.mem B (slot w mo) w) 0) := by
  have hn := hs.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => (slot_le hj).trans hZ
  have hhs : ∀ j, 8 * sl + 8 ≤ slot w j := fun j => hdr_lt_slot w j hsl'
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sl)) (s.gpr .rcx))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.st (show 8 * sl + 8 ≤ Z by have := hhs 8; omega)]) rfl)
    fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ : Outside B (8 * sl) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by omega)
  exact ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, by rw [hm₁]; exact Hdr.store hH hsl hsl' _,
    by rw [hm₁, word_writeW_self, hcx, Nat.sub_zero],
    by rw [o₁.wv (by have := hhs o; omega) (by have := sl8 o ho; omega), Nat.pow_zero, Nat.one_mul,
      Nat.mod_eq_of_lt hO],
    o₁.wv (by have := hhs mo; omega) (by have := sl8 mo hmo; omega),
    Frm.of_outside o₁ (by simp), k₁.mono (by decide)⟩

theorem doubles_eq (mo acc tmp o sl : Nat) : doubles mo acc tmp o sl =
    .seq (.block [.store (hdr sl) .rcx]) (.loop (.seq (double mo acc tmp o) (.block (dblCount sl))) .ne) := rfl

/-- `doubles`: `[o] := 2^c [o] mod m`, for the count `c ≥ 1` in `rcx`. -/
theorem doubles_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 31)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hO : wv s.mem B (slot w o) w < wv s.mem B (slot w mo) w) :
    WP isa (doubles mo acc tmp o sl) s fun t =>
      wv t.mem B (slot w o) w = 2 ^ c * wv s.mem B (slot w o) w % wv s.mem B (slot w mo) w ∧
      Frm B [(slot w acc, 8 * (w + 2)), (slot w tmp, 8 * (w + 2)), (slot w o, 8 * (w + 2)), (8 * sl, 8)]
        s.mem t.mem ∧ Hdr t.mem B w minv ∧ Keep mmRegs s t := by
  rw [doubles_eq]
  refine WP.seq (WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hs hdi hH hZ hmo ho hsl hsl' hcx hO)
    fun s₁ h₁ => ?_)
  exact wp_upto (a := 0) (N := c) (by omega) _ (fun j _ hj t hI => dblIter_ok hZ hw hw' hmo hacc htmp ho
    d1 d2 d3 d6 d7 d8 hsl hsl' hc' (by omega) hj hI) (fun t hI => ⟨hI.ov, hI.frm, hI.hdr, hI.keep⟩) h₁

end VG.Proof.Bignum.X86_64
