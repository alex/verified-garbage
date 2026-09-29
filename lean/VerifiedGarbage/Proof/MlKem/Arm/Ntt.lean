import VerifiedGarbage.Proof.MlKem.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_ntt`

Untrusted: everything here is checked by Lean. The registers saved and the
table of the zetas stored (`setup_ok`); then the three nested loops of
`nttLayer`, `nttBlock` and `nttBlockN` (`Proof/MlKem/Ntt.lean`), with an
invariant each (`LInv`, `BInv`, `FInv`) saying which polynomial `f` holds;
the butterfly is symbolically executed once for any pointers (`bfly_ok`),
and writes the coefficients `bfly` writes (`polyIs_bfly`); then the
registers restored. Layer `ℓ` has `len = 128 / 2^ℓ` and `2^ℓ` blocks.
-/

namespace VG.Proof.MlKem.Arm.Ntt

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## Values -/

theorem toNat_val (x : Zq) : (BitVec.ofNat 32 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

theorem bfly_vals (a b z : Zq) :
    fixq (BitVec.ofNat 32 a.val - red C (BitVec.ofNat 32 z.val * BitVec.ofNat 32 b.val)) =
      BitVec.ofNat 32 (a - z * b).val ∧
    fixq (BitVec.ofNat 32 a.val + red C (BitVec.ofNat 32 z.val * BitVec.ofNat 32 b.val) - 3328 - 1) =
      BitVec.ofNat 32 (a + z * b).val := by
  rw [red_mul]
  have ha := (toNat_val a).symm ▸ val_lt a
  have ht := (toNat_val (z * b)).symm ▸ val_lt (z * b)
  refine ⟨ofNat_val_eq ?_, ofNat_val_eq ?_⟩
  · rw [fixq_sub ha ht, toNat_val, toNat_val, val_sub', Nat.add_sub_assoc (Nat.le_of_lt (z * b).isLt)]
  · rw [fixq_add ha ht, toNat_val, toNat_val, val_add']

/-- A butterfly writes `f[j + len]`, then `f[j]`. -/
theorem polyIs_bfly {m : Mem} {F : Addr} {f : Poly} (h : PolyIs m F f) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) :
    PolyIs ((m.writeW (coeffAddr F (j + len)) (BitVec.ofNat 32 (f[j]! - z * f[j + len]!).val)).writeW
      (coeffAddr F j) (BitVec.ofNat 32 (f[j]! + z * f[j + len]!).val)) F (bfly f j len z) := by
  have h1 := polyIs_writeW h hj (f[j]! - z * f[j + len]!)
  have h2 := polyIs_writeW h1 (j := j) (by omega) (f[j]! + z * f[j + len]!)
  simp only [bfly]
  rwa [getElem!_set!_ne _ (by omega) (by omega)]

/-! ## The butterfly -/

section
variable {s : State} {x y z c : BitVec 32}

theorem bfly_ok (h2 : s.gpr .r2 = x) (h3 : s.gpr .r3 = y) (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = C)
    (h11 : s.gpr .r11 = c)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
    (oa : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ob : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4) :
    WP isa (.block bflyBody) s fun s' =>
      s'.gpr .r2 = x + 4 ∧ s'.gpr .r3 = y + 4 ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r7 = z ∧ s'.gpr .r8 = C ∧
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (fixq (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
            red C (z * s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32)))).writeW
        (State.addr (x + BitVec.ofNat 32 0))
          (fixq (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
            red C (z * s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32) - 3328 - 1)) := by
  run_block [bflyBody, reduce, barrett, subQ, fixup, red, bar, fixq, h2, h3, h7, h8, h11, ia, ib, oa, ob,
    and_self, and_true]

end

/-! ## Loops -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev ps : BitVec 32 := s₀.gpr .r1
abbrev F : Addr := State.addr (pf s₀)
abbrev S : Addr := State.addr (ps s₀)
abbrev P : Poly := polyAt s₀.mem (F s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s₀).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s₀.mem (F s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : Saved m₁ (S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (zetaTable.getD j 0)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps. -/
structure Env (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + 1024
  r8 : s.gpr .r8 = C
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (F s₀)] m₁ s.mem

/-- After `t` butterflies of the block from `st` with the zeta `zeta k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (k + 1))
  r2 : s.gpr .r2 = pf s₀ + BitVec.ofNat 32 (4 * (st + t))
  r3 : s.gpr .r3 = pf s₀ + BitVec.ofNat 32 (4 * (st + len + t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 (zeta k).val
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (len - t))
  poly : PolyIs s.mem (F s₀) (nttBlockN Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : Poly} {len k st t : Nat} (hl : 0 < len)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block bflyBody) s fun s' => FInv s₀ m₁ Q len k st (t + 1) s' ∧ s'.z = decide (t + 1 = len) := by
  have fF := hp.fitF
  have ea := addr_coeff (i := 4 * (st + t)) (o := 0) (j := st + t) fF (by omega) (by omega)
  have eb := addr_coeff (i := 4 * (st + len + t)) (o := 0) (j := st + t + len) fF (by omega) (by omega)
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega)
  have iW : ∀ {a : Addr}, (polyRegion (F s₀)).Contains a 4 → InRegions s.wr a 4 := fun hc => by
    rw [h.env.wr, hp.wr]; exact inRegions_of (by simp) hc
  have iR : ∀ {a : Addr}, (polyRegion (F s₀)).Contains a 4 → InRegions (s.rd ++ s.wr) a 4 := fun hc => by
    rw [h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) hc
  have va := polyIs_coeffAt h.poly (i := st + t) (by rw [n_eq]; omega)
  have vb := polyIs_coeffAt h.poly (i := st + t + len) (by rw [n_eq]; omega)
  refine WP.mono (bfly_ok h.r2 h.r3 h.r7 h.env.r8 h.r11 (by rw [ea]; exact iR ca) (by rw [eb]; exact iR cb)
    (by rw [ea]; exact iW ca) (by rw [eb]; exact iW cb))
    fun s' ⟨r2, r3, r11, z, r0, r1, r7, r8, r10, lr, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r0.trans h.env.r0, r8, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp,
        ?_⟩, r1.trans h.r1, ?_, ?_, r7, r10.trans h.r10, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r2, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r3, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub (k := 1) ht
  · rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, va, vb, (bfly_vals _ _ _).1, (bfly_vals _ _ _).2,
      nttBlockN_succ]
    exact polyIs_bfly h.poly hl (by rw [n_eq]; omega) _
  · rw [z]; exact count_z (k := 1) ht (by decide) (by omega)

/-! ## Blocks -/

section
variable {s : State} {x0 x1 x2 x10 y : BitVec 32}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h10 : s.gpr .r10 = x10)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldr .r7 .r1 0, .dp .add .r1 .r1 (.imm 4), .dp .add .r3 .r2 (.reg .r10),
        .mov .r11 (.shifted .r10 .lsr 2)]) s fun s' =>
      s'.gpr .r7 = s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 ∧ s'.gpr .r1 = x1 + 4 ∧
      s'.gpr .r3 = x2 + x10 ∧ s'.gpr .r11 = x10 >>> 2 ∧ s'.gpr .r2 = x2 ∧ s'.gpr .r10 = x10 ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h1, h2, h10, i1, and_self, and_true]

/-- The end of a block: the next block's start, compared with the end. -/
theorem bpost_ok (h0 : s.gpr .r0 = x0) (h3 : s.gpr .r3 = y) :
    WP isa (.block [.mov .r2 (.reg .r3), .cmp .r2 (.reg .r0)]) s fun s' =>
      s'.gpr .r2 = y ∧ s'.z = (y - x0 == 0) ∧ s'.gpr .r0 = x0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h0, h3, and_self, and_true]

end

theorem lsr2 {len : Nat} (h : 4 * len < 2 ^ 32) :
    BitVec.ofNat 32 (4 * len) >>> 2 = BitVec.ofNat 32 (1 * (len - 0)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  omega

theorem ptr_add_add (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Two pointers from `p` are equal exactly when their offsets are. -/
theorem ptr_sub_beq (p : BitVec 32) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (p + BitVec.ofNat 32 a - (p + BitVec.ofNat 32 b) == 0) = decide (a = b) := by
  rw [sub_beq_zero]
  by_cases h : a = b
  · subst h; simp
  · have : p + BitVec.ofNat 32 a ≠ p + BitVec.ofNat 32 b := fun e => h (by
      have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp e)
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    simp [this, h]

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * (nb + c))
  r2 : s.gpr .r2 = pf s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * len)
  poly : PolyIs s.mem (F s₀) (nttLayerN Q len c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : Poly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttBlockCode s fun s' => BInv s₀ m₁ Q len nb (c + 1) s' ∧ s'.z = decide (c + 1 = nb) := by
  have hl : 0 < len := by omega
  have fF := hp.fitF
  have fS := hp.fitS
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have hk : nb + c < 128 := by
    have : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
    omega
  have eS := addr_ptr (ps s₀) (4 * (nb + c)) 0 (by omega)
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (nb + c) + 0)) 4 :=
    contains_off (by omega) (by omega)
  have vz : s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (nb + c) + 0)) 32 =
      BitVec.ofNat 32 (zeta (128 / len + c)).val := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), Nat.add_zero, hm.tab _ hk, zetaTable_eq, zetas_getD hk, hdiv]
  refine WP.seq (WP.mono (bpre_ok h.r1 h.r2 h.r10 (by
    rw [eS, h.env.rd, h.env.wr, hp.rd, hp.wr]; exact inRegions_of (by simp) cS))
    fun s₁ ⟨r7, r1, r3, r11, r2, r10, r0, r8, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (nttLayerN Q len c) len (128 / len + c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r0.trans h.env.r0, r8.trans h.env.r8, lr.trans h.env.lr, rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_, m ▸ h.poly⟩
    · rw [r1, hdiv]
      exact (ptr_add_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega])
    · rw [r2, Nat.add_zero]
    · rw [r3, ptr_add_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega]
    · rw [r7, eS, vz]
    · rw [r11, lsr2 (by omega)]
  refine wp_loop_ne (FInv s₀ m₁ (nttLayerN Q len c) len (128 / len + c) (2 * len * c)) hl
    (fun t ht s h => fstep hp hl (by omega) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.env.r0 h₂.r3) fun s' ⟨r2, z, r0, r1, r8, r10, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0, r8.trans h₂.env.r8, lr.trans h₂.env.lr, rd.trans h₂.env.rd, wr.trans h₂.env.wr,
      sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.r10, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, hdiv, Nat.add_assoc]
  · rw [r2]; congr 2; rw [Nat.mul_succ]; omega
  · rw [m, nttLayerN_succ]; exact h₂.poly
  · rw [z, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, ptr_sub_beq _ (by omega) (by decide)]
    refine decide_eq_decide.mpr ⟨fun e => ?_, fun e => ?_⟩
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact Nat.eq_of_mul_eq_mul_left hl this
    · subst e; rw [Nat.mul_add, Nat.mul_one] at *; omega

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT`. -/
def layers (f : Poly) (ℓ : Nat) : Poly := (nttLens.take ℓ).foldl nttLayer f

theorem layers_succ (f : Poly) {ℓ : Nat} (h : ℓ < 7) :
    layers f (ℓ + 1) = nttLayer (layers f ℓ) (128 / 2 ^ ℓ) := by
  have e : ∀ ℓ < 7, nttLens[ℓ]? = some (128 / 2 ^ ℓ) := by decide
  rw [layers, List.take_add_one, List.foldl_append, e ℓ h]
  rfl

theorem layers_seven (f : Poly) : layers f 7 = ntt f := by
  rw [ntt_eq_layers]; rfl

/-- What the layers' loop counters are. -/
theorem layer_facts : ∀ ℓ < 7, 2 ≤ 128 / 2 ^ ℓ ∧ 128 / 2 ^ ℓ * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 2 ^ ℓ ≤ 64 ∧
    BitVec.ofNat 32 (4 * (128 / 2 ^ ℓ)) >>> 1 = BitVec.ofNat 32 (4 * (128 / 2 ^ (ℓ + 1))) ∧
    (BitVec.ofNat 32 (4 * (128 / 2 ^ (ℓ + 1))) - 4 == 0) = decide (ℓ + 1 = 7) := by
  decide

section
variable {s : State} {x0 x10 : BitVec 32}

theorem lpre_ok (h0 : s.gpr .r0 = x0) :
    WP isa (.block [.dp .sub .r2 .r0 (.imm 1024)]) s fun s' =>
      s'.gpr .r2 = x0 - 1024 ∧ s'.gpr .r0 = x0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧
      s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h0, and_self, and_true]

theorem lpost_ok (h10 : s.gpr .r10 = x10) :
    WP isa (.block [.mov .r10 (.shifted .r10 .lsr 1), .cmp .r10 (.imm 4)]) s fun s' =>
      s'.gpr .r10 = x10 >>> 1 ∧ s'.z = (x10 >>> 1 - 4 == 0) ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r8 = s.gpr .r8 ∧ s'.gpr .lr = s.gpr .lr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h10, and_self, and_true]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  r1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 (4 * 2 ^ ℓ)
  r10 : s.gpr .r10 = BitVec.ofNat 32 (4 * (128 / 2 ^ ℓ))
  poly : PolyIs s.mem (F s₀) (layers (P s₀) ℓ)

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ s'.z = decide (ℓ + 1 = 7) := by
  obtain ⟨f1, f2, f3, f4, -, f6, f7⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.r0) fun s₁ ⟨r2, r0, r1, r8, r10, lr, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (layers (P s₀) ℓ) (128 / 2 ^ ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r0, r8.trans h.env.r8, lr.trans h.env.lr, rd.trans h.env.rd, wr.trans h.env.wr,
      sp.trans h.env.sp, m ▸ h.env.frame⟩, by rw [r1, h.r1, Nat.add_zero], ?_, r10.trans h.r10, ?_⟩
    · rw [r2, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_ne (BInv s₀ m₁ (layers (P s₀) ℓ) (128 / 2 ^ ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.r10) fun s' ⟨r10, z, r0, r1, r8, lr, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r0.trans h₂.env.r0, r8.trans h₂.env.r8, lr.trans h₂.env.lr, rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r1, h₂.r1, f4]
  · rw [r10, f6]
  · have e : 128 / (128 / 2 ^ ℓ) = 2 ^ ℓ :=
      Nat.div_eq_of_eq_mul_left (by omega) (by rw [Nat.mul_comm]; exact f2.symm)
    rw [m, layers_succ _ hℓ, nttLayer, e]
    exact h₂.poly
  · rw [z, f6, f7]

/-! ## Setup and the end -/

/-- The registers saved and the table stored. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ table zetaTable .r1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o n : Nat}, o + n ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) n := fun h => by
    rw [hp.wr]; exact inRegions_of (by simp) (contains_off h (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r1 (off := 512) (by decide) (fit_le (by decide) fS) fun i hi => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  have g1 : (s₁.gpr .r1) = ps s₀ := by rw [h₁.gpr]
  refine WP.mono (table_ok zetaTable (by decide) (b := .r1) (by decide) (by rw [g1]; exact fit_le (by decide) fS)
    fun k hk => by rw [g1, h₁.wr]; exact wS (by omega)) fun s₂ h₂ => ?_
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr
      exact region_sub_off (by decide)
    · rw [List.mem_singleton] at hr; subst hr
      rw [g1, ← add_ofNat_zero (State.addr (ps s₀))]
      exact region_sub_off (by decide)
  have hm : Setup s₀ s₂.mem := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
    · rw [h₂.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact h₁.saved i hi
      · rw [List.mem_singleton] at hr; subst hr
        rw [g1, add_ofNat_add, ← add_ofNat_zero (State.addr (ps s₀))]
        exact region_disj_off (by omega) (by omega) (by omega) hS
    · have := h₂.tab j hj; rwa [g1] at this
    · exact polyIs_frame fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
        ⟨hp.red, rfl⟩
  exact ⟨hm, fun r hr => (h₂.gpr r hr).trans (by rw [h₁.gpr]), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ table zetaTable .r1 ++ consts ++
      ([.dp .add .r0 .r0 (.imm 1024), .dp .add .r1 .r1 (.imm 4), .mov .r10 (.imm 512)] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have elr := e .lr (by decide)
  run_block [consts, e0, e1, elr, rd, wr, sp, consts_val, hm, true_and]
  exact ⟨⟨rfl, rfl, by simp [elr], rfl, rfl, rfl, Frame.refl _ _⟩, rfl, rfl, hm.poly⟩

theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h : LInv s₀ m₁ 7 s) :
    WP isa (.block (restoreRegs .r1 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (F s₀) (ntt (P s₀)) := by
  have fS := hp.fitS
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 0 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h.r1, addr_add (by omega), add_ofNat_zero]
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 0) (by decide) (by rw [h.r1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [h.env.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega))
    fun i hi => by
      rw [e1, h.env.rd, h.env.wr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega) (by omega)))
    fun s' h' => ⟨preserved_of_restore h' h.env.lr, h'.sp.trans h.env.sp, ?_⟩
  rw [h'.mem, ← layers_seven]
  exact h.poly

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  exact wp_loop_ne (LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => restore_ok hp hm h) h₁

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.nttContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.ntt (Spec.MlKem.nttContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlKem.Arm.Ntt
