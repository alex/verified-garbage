import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import Mathlib.Data.Int.GCD

/-!
# `vg_rsa_public_precomputed` on x86-64: the computation

The load of `m` and `R² mod m` from `pre`, and the checks that refuse values
no modulus has (`pdLoad_ok`); then the input, `-m⁻¹`, the exponentiation and
the result, for any values that pass the checks (`pdRest_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Precomputed
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## The load and the checks -/

theorem check_eq (a top : BitVec 64) (c : Bool) :
    (a &&& 1 &&& mask c &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (top.toNat < BitVec.toNat (1 : BitVec 64)))) + 1 &&&
      (a &&& 1 &&& mask c &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (top.toNat < BitVec.toNat (1 : BitVec 64)))) + 1)
      == 0) = !(decide (a.toNat % 2 = 1) && c && decide (top ≠ 0)) := by
  have h1 : a &&& 1 = BitVec.ofNat 64 (a.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat]
    omega
  have h2 : decide (top.toNat < BitVec.toNat (1 : BitVec 64)) = decide (top = 0) :=
    decide_eq_decide.mpr ⟨fun h => BitVec.eq_of_toNat_eq (by
      rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at h; rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
      omega),
      fun h => by subst h; decide⟩
  rw [h1, h2, decide_not]
  generalize decide (top = 0) = z
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h | h <;> rw [h] <;> cases c <;> cases z <;> decide

/-- The checks' last block: ZF clear iff `m` (at `r10`, `w` words) is odd, its
top word is not zero, and `rbp` is the mask of a true `c`. -/
theorem checkBlk_ok {t : State} {B : Addr} {Z w : Nat} (hs : Scr t B Z) (h10 : t.gpr .r10 = off B (slot w aN))
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hZ : slot w 8 ≤ Z) {c : Bool}
    (hbp : t.gpr .rbp = mask c) :
    WP isa (.block [.mov .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .and .rax (.reg .rbp),
      .mov .rdx (.mem (ix .r10 .r12 (-8))), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
      .alu .add .rdx (.imm 1), .alu .and .rax (.reg .rdx), .alu .test .rax (.reg .rax)]) t fun t' =>
      t'.zf = some (!(decide ((word t.mem B (slot w aN)).toNat % 2 = 1) && c &&
        decide (word t.mem B (slot w aN + 8 * (w - 1)) ≠ 0))) ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t' := by
  have hn := hs.nowrap
  have := slot_le (w := w) (show aN < 8 by decide)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.zf = some (!(decide ((word t.mem B (slot w aN)).toNat % 2 = 1) && c &&
        decide (word t.mem B (slot w aN + 8 * (w - 1)) ≠ 0))) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩
  xrun [State.ea, ix, at0, addrm8 (b := off B (slot w aN)) rfl h12 (by omega), h10, hbp,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by omega), hs.ld (show slot w aN + 8 ≤ Z by omega)]
  rw [check_eq]

/-- What the load changes. -/
def pdLoadRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (slot w aR2, 8 * (w + 2))]

theorem pdLoadRanges_le (w : Nat) : ∀ r ∈ pdLoadRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  have := slot_le (w := w) (show aR2 < 8 by decide)
  simp only [pdLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr] at * <;> omega

theorem pdLoadRanges_fixed (w : Nat) :
    ∀ r ∈ pdLoadRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h1 : slot w 0 ≤ slot w aN := by unfold slot; omega
  have h2 : slot w 0 ≤ slot w aR2 := by unfold slot; omega
  simp only [pdLoadRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sW, sArr] at * <;> omega

/-- The load: `w`, the bases, `m` and `R² mod m` from `pre` (at `pp`, the
`2 w` words outside the working space), and ZF clear iff they pass the
checks. -/
theorem pdLoad_ok {s : State} {B : Addr} {Z k : Nat} {pp : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = pp)
    (hpr : ∀ i < 2 * ((k + 7) / 8), InRegions (s.rd ++ s.wr) (off pp (8 * i)) 8)
    (hps : ∀ j < 16 * ((k + 7) / 8), Z ≤ ofs B (pp + BitVec.ofNat 64 j)) :
    WP isa (seqs Precomputed.load) s fun t =>
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) ∧
      wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      t.zf = some (!(decide ((word t.mem B (slot ((k + 7) / 8) aN)).toNat % 2 = 1) &&
        decide (wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) < wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8)) &&
        decide (word t.mem B (slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 - 1)) ≠ 0))) ∧
      Frm B (pdLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  have hsR := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide)
  have hNR : slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 + 2) ≤ slot ((k + 7) / 8) aR2 := by
    unfold slot aN aR2; omega
  have h0N : slot ((k + 7) / 8) 0 ≤ slot ((k + 7) / 8) aN := by unfold slot; omega
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have hsl : ∀ r ∈ pdLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => (pdLoadRanges_le _ r hr).trans hZ
  -- A word of `pre` is outside the working space.
  have hpsep : ∀ e, e + 8 * ((k + 7) / 8) ≤ 16 * ((k + 7) / 8) → ∀ j < (k + 7) / 8, ∀ b < 8,
      Z ≤ ofs B (off pp (e + 8 * j) + BitVec.ofNat 64 b) := fun e he j hj b hb => by
    have := hps (e + 8 * j + b) (by omega)
    rwa [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  unfold Precomputed.load
  refine WP.seq (WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN)
    fun t₁ ⟨h12, _, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hf₁' : Frm B (pdLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [pdLoadRanges])
  have hi₁ := InScr.of_frm hf₁' hsl
  -- `m`.
  refine WP.seq (WP.mono (copyWords_ok (S := pp) (eS := 0) (by rw [hsi]; simp [off]) hbx h12 (by omega) (by omega)
    (by omega) (fun j hj => by rw [k₁.2.1, k₁.2.2, Nat.zero_add]; exact hpr j (by omega))
    (fun j hj => by rw [k₁.2.2]; exact hs.st (by omega))
    (fun j hj b hb => Or.inr (by have := hpsep 0 (by omega) j hj b hb; omega))) fun t₂ ⟨hv₂, _, ho₂, k₂⟩ => ?_)
  have hm₂ : wv t₁.mem pp 0 ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) :=
    wv_congr fun i hi => Mem.readW_congr fun b hb => hi₁ _ (hpsep 0 (by omega) i hi b (by omega))
  rw [hm₂] at hv₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₂.word (by omega) (by omega)]; exact hW₁
  have hb₂ : ∀ j < 8, word t₂.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₂.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega)]; exact hb₁ j hj
  have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 ((k + 7) / 8) → r + r + (r + r) + (r + r + (r + r)) =
      BitVec.ofNat 64 (8 * ((k + 7) / 8)) := by
    rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
  -- `R² mod m`'s registers.
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = off pp (8 * ((k + 7) / 8)) ∧
      t.gpr .rbx = off B (slot ((k + 7) / 8) aR2) ∧ t.mem = t₂.mem) (by
    unfold eightW
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega), hb₂ aR2 (by decide),
      (k₂.gpr (by decide)).trans h12, (k₂.gpr (by decide)).trans hsi, hax8 _ rfl]) rfl)
    fun t₃ ⟨⟨hsi₃, hbx₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  -- `R² mod m`.
  refine WP.seq (WP.mono (copyWords_ok hsi₃ hbx₃ ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))
    (by omega) (by omega) (by omega)
    (fun j hj => by rw [k13.2.1, k13.2.2, show 8 * ((k + 7) / 8) + 8 * j = 8 * ((k + 7) / 8 + j) by omega]
                    exact hpr _ (by omega))
    (fun j hj => by rw [k13.2.2]; exact hs.st (by omega))
    (fun j hj b hb => Or.inr (by have := hpsep (8 * ((k + 7) / 8)) (by omega) j hj b hb; omega)))
    fun t₄ ⟨hv₄, _, ho₄, k₄⟩ => ?_)
  have hm₄ : wv t₃.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) := by
    rw [hm₃]
    exact wv_congr fun i hi => Mem.readW_congr fun b hb => (ho₂ _ (Or.inr (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega) i hi b (by omega); omega))).trans (hi₁ _ (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega) i hi b (by omega); omega))
  rw [hm₄] at hv₄
  have k14 := k13.trans k₄
  have hs₄ := hs.congr k14.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k14.gpr (by decide)).trans hdi
  have hN₄ : wv t₄.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) := by
    rw [ho₄.wv (by omega) (by omega), hm₃]; exact hv₂
  have hb₄ : ∀ j < 8, word t₄.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₄.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega), hm₃]; exact hb₂ j hj
  have hW₄ : word t₄.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₄.word (by omega) (by omega), hm₃]; exact hW₂
  have h12₄ : t₄.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) :=
    (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12))
  have hbx₄ : t₄.gpr .rbx = off B (slot ((k + 7) / 8) aR2) := (k₄.gpr (by decide)).trans hbx₃
  -- The comparison's registers.
  refine WP.seq (WP.mono (WP.keep [.r10, .rbp] (Q := fun t => t.gpr .r10 = off B (slot ((k + 7) / 8) aN) ∧
      t.gpr .rbp = mask false ∧ t.mem = t₄.mem) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.ld (d := 8 * sArr aN) (by unfold sArr aN; omega), hb₄ aN (by decide)])
    rfl) fun t₅ ⟨⟨h10₅, hbp₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  refine WP.seq (WP.mono (cmpLoop_ok hs₅ ((k₅.gpr (by decide)).trans hbx₄) h10₅ ((k₅.gpr (by decide)).trans h12₄)
    hbp₅ (by omega) (by omega) (by omega) (by omega)) fun t₆ ⟨hbp₆, hm₆, k₆⟩ => ?_)
  rw [hm₅] at hbp₆
  have hs₆ := hs₅.congr k₆.2.2
  rw [seqs_one]
  refine WP.mono (checkBlk_ok hs₆ ((k₆.gpr (by decide)).trans h10₅)
    ((k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans h12₄)) (by omega) hZ hbp₆) fun t ⟨hz, hm, k₇⟩ => ?_
  have hmm : t.mem = t₄.mem := by rw [hm, hm₆, hm₅]
  refine ⟨by rw [hmm]; exact hN₄, by rw [hmm]; exact hv₄, by rw [hmm]; exact hW₄,
    fun j hj => by rw [hmm]; exact hb₄ j hj, by rw [hz, hm₆, hm₅, hmm], ?_,
    ((((k14.trans k₅).trans k₆).trans k₇)).mono (by decide)⟩
  rw [hmm]
  have f₂ : Frm B (pdLoadRanges ((k + 7) / 8)) t₁.mem t₂.mem :=
    Frm.of_outside (ho₂.mono (o' := slot ((k + 7) / 8) aN) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega))
      (by simp [pdLoadRanges])
  have f₄ : Frm B (pdLoadRanges ((k + 7) / 8)) t₃.mem t₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot ((k + 7) / 8) aR2) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega))
      (by simp [pdLoadRanges])
  rw [hm₃] at f₄
  exact (hf₁'.trans f₂).trans f₄

/-! ## The computation -/

/-- The input's load. -/
def pdIn : List (Prog isa) :=
  [.block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))], loadBE]

/-- `X = input R`, the exponentiation and `Y R⁻¹`. -/
def pdExp (M : Mont) : List (Prog isa) := [M.mm aXm aX aR2, Precomputed.expLoop M.mm, Precomputed.finish M.mm]

theorem pdRest_eq (M : Mont) : Precomputed.rest M.mm = seqs ((pdIn ++ restSteps) ++ (pdExp M ++ outSteps)) := rfl

/-- What `rest` starts from: the header `entry` leaves, `m` and `R² mod m`
(here any `R < N`) in their arrays, as the checks accepted them. -/
structure PdPre (s : State) (B : Addr) (Z k : Nat) (op ep ip : Addr) (L : Nat) (eb xb : List Byte) (N R : Nat) :
    Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : slot ((k + 7) / 8) 8 ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : word s.mem B (8 * sOut) = op
  hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hE : word s.mem B (8 * sE) = ep
  hL : word s.mem B (8 * sElen) = BitVec.ofNat 64 L
  hIn : word s.mem B (8 * sIn) = ip
  hW : word s.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8)
  hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)
  n : wv s.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = N
  r : wv s.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R
  odd : N % 2 = 1
  n1 : 1 < N
  rlt : R < N
  x : Src s B Z ip xb
  e : Src s B Z ep eb
  xl : xb.length = k
  el : eb.length = L
  L1 : 1 ≤ L
  L2 : L ≤ k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)

/-- `x` with `x R ≡ X`, for `R` invertible modulo `N > 1`. -/
theorem exists_mont {R N : Nat} (hR : Nat.Coprime R N) (hN1 : 1 < N) (X : Nat) :
    ∃ x, X % N = x * R % N := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hN1
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

/-- The input into its array. -/
theorem pdIn_ok {s : State} {B : Addr} {Z k : Nat} {ip : Addr} {xb : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hIn : word s.mem B (8 * sIn) = ip)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) (hx : Src s B Z ip xb)
    (hxl : xb.length = k) :
    WP isa (seqs pdIn) s fun t => wv t.mem B (slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      Arrays B ((k + 7) / 8) [aX] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eIn : sIn = 21 := rfl
  have eAX : sArr aX = 9 := rfl
  unfold pdIn
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = ip ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = off B (slot ((k + 7) / 8) aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sIn) (by omega), hs.ld (d := 8 * sK) (by omega),
      hs.ld (d := 8 * sArr aX) (by omega), hIn, hK, hb aX (by decide)]) rfl)
    fun t₁ ⟨⟨hsi, hcx, hbx, hm₁⟩, k₁⟩ => ?_)
  rw [seqs_one]
  refine WP.mono (loadArr_ok (hs.congr k₁.2.2) (by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hxl (by omega) hk hsi hcx hbx)
    fun t ⟨hv, ha, k₂⟩ => ⟨hv, by rw [hm₁] at ha; exact ha, (k₁.trans k₂).mono (by decide)⟩

/-- What `rest` changes. -/
def pdAll (w : Nat) : List (Nat × Nat) :=
  [(slot w aX, 8 * (w + 2)), (8 * sMinv, 8), (8 * sMask, 8), (slot w aOne, 8 * (w + 2)),
    (slot w aXm, 8 * (w + 2))] ++ pExpRanges w

theorem pdAll_le (w : Nat) : ∀ r ∈ pdAll w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have := slot_le (w := w) (show aX < 8 by decide)
  have := slot_le (w := w) (show aOne < 8 by decide)
  have := slot_le (w := w) (show aXm < 8 by decide)
  have := slot_le (w := w) (show aAcc < 8 by decide)
  have := slot_le (w := w) (show aTmp < 8 by decide)
  have := slot_le (w := w) (show aY < 8 by decide)
  simp only [pdAll, pExpRanges, pBitRanges, bitRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sMinv, sMask, sI, sV, sBit, sStarted, sFn] at * <;> omega

theorem pdAll_fixed (w : Nat) : ∀ r ∈ pdAll w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aX (show 31 < 32 by decide)
  have := hdr_lt_slot w aOne (show 31 < 32 by decide)
  have := hdr_lt_slot w aXm (show 31 < 32 by decide)
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aY (show 31 < 32 by decide)
  simp only [pdAll, pExpRanges, pBitRanges, bitRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sMinv, sMask, sI, sV, sBit, sStarted, sFn] at * <;> omega

/-- The input, the mask of `input < N`, `-m⁻¹` and the number 1. -/
theorem pdSetup_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (seqs (pdIn ++ restSteps)) s fun t => ∃ minv,
      SetupOut t B Z ((k + 7) / 8) minv N (Spec.Rsa.os2ip xb) ∧ Frm B (pdAll ((k + 7) / 8)) s.mem t.mem ∧
      Keep mmRegs s t ∧ wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  -- The input.
  refine wp_seqs_append (by simp [pdIn]) (by simp [restSteps])
    (WP.mono (pdIn_ok hs h.rdi hZ (by omega) (by omega) h.hK h.hIn h.hb h.x h.xl) fun t₁ ⟨hX₁, ha₁, k₁⟩ => ?_)
  have f₁ : Frm B (pdAll ((k + 7) / 8)) s.mem t₁.mem := Frm.of_arrays ha₁ (by simp [pdAll])
  -- The mask, `-m⁻¹` and 1.
  refine WP.mono (setupRest_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h.rdi) hZ (by omega) (by omega)
      (by rw [ha₁.hslot (by decide)]; exact h.hW) (fun j hj => by rw [ha₁.hslot (by unfold sArr; omega)]; exact h.hb j hj)
      (by rw [ha₁.wv_of_not_mem (by decide) (by decide) hn']; exact h.n) hX₁ h.odd)
      fun t₂ ⟨minv, so, f₂', k₂⟩ => ⟨minv, so, f₁.trans (f₂'.mono (by simp [pdAll])), (k₁.trans k₂).mono (by decide), ?_⟩
  rw [f₂'.wv_eq (fun r hr => by
      have := hdr_lt_slot ((k + 7) / 8) aR2 (show 31 < 32 by decide)
      have := slot_sep (w := (k + 7) / 8) (show aR2 ≠ aOne by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sMinv, sMask, sFn] at * <;> omega)
      (by have := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide); omega),
    ha₁.wv_of_not_mem (by decide) (by decide) hn']
  exact h.r

/-- `rest`, for values the checks accepted: `x^e mod N` (or zeros, if the
input is not below `N`) to `out`, for the `x` with `x R ≡ input R² R⁻¹`,
which is the input if `R ≡ R²`. -/
theorem pdRest_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (Precomputed.rest M.mm) s fun t => ∃ x : Nat,
      (R % N = 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N → x % N = Spec.Rsa.os2ip xb % N) ∧
      MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then x ^ Spec.Rsa.os2ip eb % N else 0)
        (decide (Spec.Rsa.os2ip xb < N)) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hw : 2 ≤ (k + 7) / 8 := by omega
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) N := VG.Proof.Bignum.coprime_pow2 h.odd _
  have hle := pdAll_le ((k + 7) / 8)
  have hle' : ∀ r ∈ pdAll ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => (hle r hr).trans hZ
  rw [pdRest_eq]
  refine wp_seqs_append (by simp [pdIn]) (by simp [pdExp])
    (WP.mono (pdSetup_ok h) fun t₂ ⟨minv, so, f₂, k₂, hR₂⟩ => ?_)
  refine wp_seqs_append (by simp [pdExp]) (by simp [outSteps]) ?_
  unfold pdExp
  -- `X = input R`.
  refine WP.seq (WP.mono (mmN_ok M (o := aXm) (a := aX) (b := aR2) so.good hZ hw (by omega) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) so.n so.inv (by rw [hR₂]; exact h.rlt))
    fun t₃ ⟨hg₃, hn₃, hinv₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [so.x, hR₂] at hm₃
  have f₃ : Frm B (pdAll ((k + 7) / 8)) t₂.mem t₃.mem := Frm.of_arrays ha₃ (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])
  have f₁₃ := f₂.trans f₃
  have x₁₃ := Fixed.of_frm f₁₃ (pdAll_fixed _)
  obtain ⟨x, hx⟩ := exists_mont hR h.n1 (wv t₃.mem B (slot ((k + 7) / 8) aXm) ((k + 7) / 8))
  have he₃ := h.e.congrK (InScr.of_frm f₁₃ hle') (k₂.trans k₃)
  -- The exponentiation.
  refine WP.seq (WP.mono (pExpLoop_ok (x := x) ⟨hg₃, hn₃, hinv₃, rfl⟩ hZ hw (by omega) hR hlt₃ hx
    (by rw [x₁₃ sE (by decide)]; exact h.hE) (by rw [x₁₃ sElen (by decide)]; exact h.hL) h.el h.L1 (by omega)
    (fun i hi => he₃.rd i (by rw [h.el]; exact hi)) (fun i hi => he₃.val i (by rw [h.el]; exact hi))
    (fun i hi => he₃.out i (by rw [h.el]; exact hi)))
    fun t₄ ⟨hc₄, hy₄, f₄', k₄⟩ => ?_)
  have f₄ : Frm B (pdAll ((k + 7) / 8)) t₃.mem t₄.mem := f₄'.mono fun _ hr => List.mem_append_right _ hr
  have hone₄ : wv t₄.mem B (slot ((k + 7) / 8) aOne) ((k + 7) / 8) = 1 := by
    rw [f₄'.wv_eq (fun r hr => by
        have := hdr_lt_slot ((k + 7) / 8) aOne (show 31 < 32 by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aAcc by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aTmp by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aY by decide)
        simp only [pExpRanges, pBitRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sI, sV, sBit, sStarted, sFn] at * <;>
          omega)
        (by have := slot_le (w := (k + 7) / 8) (show aOne < 8 by decide); omega),
      ha₃.wv_of_not_mem (by decide) (by decide) hn']
    exact so.one
  rw [seqs_one]
  refine WP.mono (pFinish_ok hc₄ hZ hw (by omega) hR h.n1 hone₄ hy₄) fun t₅ ⟨hg₅, hY₅, f₅', k₅⟩ => ?_
  have f₅ : Frm B (pdAll ((k + 7) / 8)) t₄.mem t₅.mem :=
    f₅'.mono (by simp [finRanges, pdAll, pExpRanges, pBitRanges, bitRanges])
  have f₁₅ := (f₁₃.trans f₄).trans f₅
  have x₁₅ := Fixed.of_frm f₁₅ (pdAll_fixed _)
  have k₁₅ := ((k₂.trans k₃).trans k₄).trans k₅
  have hM₅ : word t₅.mem B (8 * sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [f₅'.word_eq (fun r hr => by
        have := hdr_lt_slot ((k + 7) / 8) aAcc (show sMask < 32 by decide)
        have := hdr_lt_slot ((k + 7) / 8) aTmp (show sMask < 32 by decide)
        have := hdr_lt_slot ((k + 7) / 8) aY (show sMask < 32 by decide)
        simp only [finRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega) (by unfold sMask sFn; omega),
      f₄'.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega),
      ha₃.hslot (by decide)]
    exact so.mask
  refine WP.mono (outPhase_ok hg₅ hZ (by omega) (by omega) hY₅ (by rw [x₁₅ sOut (by decide)]; exact h.hO)
    (by rw [x₁₅ sK (by decide)]; exact h.hK) hM₅ (fun j hj => by rw [k₁₅.2.2]; exact h.out j hj) h.outSep)
    fun t ⟨hb, hax, hsv, hfr, k₆⟩ => ⟨x, fun hRR => ?_, ⟨?_, hax, fun i hi => by rw [hsv i hi]; exact x₁₅ i (by omega),
      fun y hy hy' => by rw [hfr y hy', InScr.of_frm f₁₅ hle' y hy], (k₁₅.trans k₆).mono (by decide)⟩⟩
  · apply VG.Proof.Bignum.mont_cancel hR
    apply VG.Proof.Bignum.mont_cancel hR
    calc x * 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N
        = x * 2 ^ (64 * ((k + 7) / 8)) % N * 2 ^ (64 * ((k + 7) / 8)) % N := (Nat.mod_mul_mod _ _ _).symm
      _ = wv t₃.mem B (slot ((k + 7) / 8) aXm) ((k + 7) / 8) % N * 2 ^ (64 * ((k + 7) / 8)) % N := by rw [hx]
      _ = Spec.Rsa.os2ip xb * R % N := by rw [Nat.mod_mul_mod, hm₃]
      _ = Spec.Rsa.os2ip xb * (R % N) % N := (Nat.mul_mod_mod _ _ _).symm
      _ = Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N := by
        rw [hRR, Nat.mul_mod_mod, Nat.mul_assoc]
  · rw [hb]
    by_cases hc : Spec.Rsa.os2ip xb < N <;> simp [hc]

end VG.Proof.Bignum.X86_64
