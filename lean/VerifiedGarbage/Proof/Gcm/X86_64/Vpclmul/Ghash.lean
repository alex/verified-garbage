import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Impl.Gcm.X86_64.Vpclmul
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-!
# GHASH with VPCLMULQDQ

`ghash_verified` proves `Impl.Gcm.X86_64.Vpclmul.ghash` against
`Pclmul.ghashX86_64`.

The eight-block loop keeps `vg_ghash_pclmul`'s loop invariant (`Pclmul.Inv`,
about `xmm0`–`xmm6`) and the upper lanes of the mask, the reduction constant
and `Y`, and the powers in `ymm12`–`ymm15` (`Inv8`). Its body is, lane by
lane, `vg_ghash_pclmul`'s instructions (`WP.lanes`): the products of each lane
are accumulated as `Pclmul.acc_ok` says, and reduced as `Pclmul.reduce_ok`
says; the two lanes' blocks add up to `Y` after eight blocks (`step8`). After
the loop, `vzeroupper` keeps `Pclmul.Inv`, and `vg_ghash_pclmul`'s loops
finish (`Pclmul.tail_ok`).
-/

namespace VG.Proof.Gcm.X86_64.Vpclmul

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce φ_reduce Only prod zero_ok acc_ok reduce_ok pxor72_ok
  mul_ok Pre Inv pre_of nb hA dp blkAddr H₀ Y₀ tail_ok prologue_ok ghashX86_64 ea_at ofInt_natCast
  toNat_ofNat_lt addr_add ofNat_sub_ofNat add_ofNat_ofNat satState)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Vpclmul (preg powers zero acc reduce load combine next body8 ghash)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Eight blocks, in `Q` -/

theorem step8 (H Y X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ : Block)
    (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3)
    (h₄ : x * φ T₄ = φ H ^ 4) (h₅ : x * φ T₅ = φ H ^ 5) (h₆ : x * φ T₆ = φ H ^ 6)
    (h₇ : x * φ T₇ = φ H ^ 7) (h₈ : x * φ T₈ = φ H ^ 8) :
    reduce ((((Prod.zero.acc (Y ^^^ X₀) T₈).acc X₂ T₆).acc X₄ T₄).acc X₆ T₂) ^^^
        reduce ((((Prod.zero.acc X₁ T₇).acc X₃ T₅).acc X₅ T₃).acc X₇ T₁) =
      mul (mul (mul (mul (mul (mul (mul (mul (Y ^^^ X₀) H ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H
        ^^^ X₅) H ^^^ X₆) H ^^^ X₇) H := by
  apply φ_inj
  simp only [φ_xor, φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul]
  linear_combination (φ Y + φ X₀) * h₈ + φ X₁ * h₇ + φ X₂ * h₆ + φ X₃ * h₅ + φ X₄ * h₄ +
    φ X₅ * h₃ + φ X₆ * h₂ + φ X₇ * h₁

/-! ## Lane by lane -/

/-- `vinserti128`'s and `vextracti128`'s immediate 1 selects the upper lane. -/
theorem getLsbD_one8 : (1 : BitVec 8).getLsbD 0 = true := rfl

/-- A block of lane-wise instructions whose SSE block leaves each lane's
registers but `rs` alone leaves the vector registers but `rs` alone. -/
theorem yframe_of_lanes {rs : List XReg} {s s' : State} (hk : VKeep s s')
    (ho : ∀ l < 2, ∀ r, r ∉ rs → (s'.proj l).xmm r = (s.proj l).xmm r) : YFrame rs s s' :=
  ⟨hk.gpr, hk.mem, hk.rd, hk.wr, fun r hr l hl => by simpa using ho l hl r hr⟩

theorem zero_lanes (s : State) :
    WP isa (.block zero) s fun s' => (∀ l < 2, prod (s'.proj l) = Prod.zero) ∧
      YFrame [.xmm8, .xmm9, .xmm10] s s' ∧ VKeep s s' := by
  refine WP.mono (WP.lanes (ss := Impl.Gcm.X86_64.Pclmul.zero) rfl fun l _ => zero_ok (s.proj l))
    fun s' ⟨hk, hq⟩ => ⟨fun l hl => (hq l hl).1, yframe_of_lanes hk fun l hl r hr => (hq l hl).2.xmm r hr,
      hk⟩

/-- `pshufb xmm7, xmm0`. -/
theorem pshufb7_ok (t : State) :
    WP isa (.block [.xop (.bin .pshufb .xmm7 .xmm0)]) t fun t' =>
      t'.xmm .xmm7 = XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0) ∧ Only [.xmm7] t t' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

/-- The SSE block of a load's lane-wise instructions. -/
def ldacc (first : Bool) (b : XReg) : List Instr :=
  [.xop (.bin .pshufb .xmm7 .xmm0)] ++ (if first then [.xop (.bin .pxor .xmm7 .xmm2)] else []) ++
    Impl.Gcm.X86_64.Pclmul.acc .xmm7 b

theorem ldacc_ok (first : Bool) (b : XReg) (t : State) (hb7 : b ≠ .xmm7) (hb8 : b ≠ .xmm8)
    (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11) :
    WP isa (.block (ldacc first b)) t fun t' =>
      prod t' = (prod t).acc
        ((if first then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0))
        (t.xmm b) ∧
      Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  rw [ldacc, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pshufb7_ok t) fun t₁ ⟨e₁, o₁⟩ => ?_
  have hp₁ : prod t₁ = prod t := o₁.prod (by decide) (by decide) (by decide)
  have hb₁ : t₁.xmm b = t.xmm b := o₁.xmm b (by simp [hb7])
  have h2₁ : t₁.xmm .xmm2 = t.xmm .xmm2 := o₁.xmm _ (by decide)
  have fin : ∀ t₂, Only [.xmm7] t₁ t₂ → t₂.xmm .xmm7 =
      (if first then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0) →
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.acc .xmm7 b)) t₂ fun t' =>
        prod t' = (prod t).acc
          ((if first then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0))
          (t.xmm b) ∧ Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
    intro t₂ o₂ e₂
    refine WP.mono (acc_ok .xmm7 b t₂ (by decide) (by decide) (by decide) (by decide) hb8 hb9 hb10 hb11)
      fun t' ⟨p', o'⟩ => ⟨?_, ?_⟩
    · rw [p', o₂.prod (by decide) (by decide) (by decide), hp₁, e₂, o₂.xmm b (by simp [hb7]), hb₁]
    · exact ((o₁.trans o₂).trans o').weaken fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with (h | h) | (h | h | h | h) <;> simp [h]
  cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] at fin ⊢
  · exact WP.block_nil (fin t₁ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by rw [e₁]; simp))
  · refine WP.mono (pxor72_ok t₁) fun t₂ ⟨e₂, o₂⟩ => fin t₂ o₂ (by rw [e₂, e₁, h2₁])

theorem load256_lo (m : Mem) (a : Addr) : (m.readW a 256).extractLsb' 0 128 = m.readW a 128 := by
  have e := readW_extract m a (w := 256) (k := 0) (n := 16) (by decide)
  simpa using e

theorem load256_hi (m : Mem) (a : Addr) :
    (m.readW a 256).extractLsb' 128 128 = m.readW (a + BitVec.ofNat 64 16) 128 := by
  have e := readW_extract m a (w := 256) (k := 16) (n := 16) (by decide)
  simpa using e

/-- The lane-wise instructions of a load. -/
abbrev restV (k : Nat) : List Instr :=
  [.vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)] ++
    (if k = 0 then [.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 (preg k)

theorem load_eq (k : Nat) : load k = .vmovdquLoad .l256 .xmm7 (at_ .rdx (32 * k)) :: restV k := by
  simp only [load, restV, List.cons_append]

theorem lane_load {k : Nat} (hk : k < 4) : laneSseBlock (restV k) = some (ldacc (decide (k = 0)) (preg k)) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem preg_ne {k : Nat} : preg k ≠ .xmm7 ∧ preg k ≠ .xmm8 ∧ preg k ≠ .xmm9 ∧ preg k ≠ .xmm10 ∧
    preg k ≠ .xmm11 ∧ preg k ≠ .xmm0 ∧ preg k ≠ .xmm1 ∧ preg k ≠ .xmm2 := by
  unfold preg; split <;> decide

/-- Blocks `2k` and `2k + 1` at `rdx + 32 k`, added to the lanes' products. -/
theorem load_ok {k : Nat} (hk : k < 4) (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32) :
    WP isa (.block (load k)) s fun s' =>
      (∀ l < 2, prod (s'.proj l) = (prod (s.proj l)).acc
        ((if k = 0 then s.lane .xmm2 l else 0) ^^^
          blockAt s.mem (s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (s.lane (preg k) l)) ∧
      YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  obtain ⟨n7, n8, n9, n10, n11, -, -, n2⟩ := preg_ne (k := k)
  let a := s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)
  let v := s.mem.readW a 256
  let s₁ := s.setV .l256 .xmm7 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [load_eq, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have l7 : ∀ l < 2, s₁.lane .xmm7 l = s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [s₁, State.lane_setV256, v, load256_lo]
    · simp [s₁, State.lane_setV256, v, load256_hi]
  have keep : ∀ r, r ≠ .xmm7 → ∀ l < 2, s₁.lane r l = s.lane r l := fun r hr l _ => by
    simp [s₁, State.lane_setV256, hr]
  refine WP.mono (WP.lanes (lane_load hk) fun l _ => ldacc_ok _ (preg k) (s₁.proj l) n7 n8 n9 n10 n11)
    fun s' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (s₁.proj l) = prod (s.proj l) := by
      simp only [prod, State.proj_xmm, keep .xmm8 (by decide) l hl, keep .xmm9 (by decide) l hl,
        keep .xmm10 (by decide) l hl]
    simp only [hp, State.proj_xmm, keep _ n7 l hl, l7 l hl, keep .xmm0 (by decide) l hl, h0 l hl,
      keep .xmm2 (by decide) l hl]
    rw [← blockAt_eq]
    by_cases h : k = 0 <;> simp only [a, h, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r hr
    simp only [State.proj_xmm] at this
    rw [this, keep r (fun h => hr (h ▸ List.mem_cons_self)) l hl]

/-- Each lane's product, reduced, into that lane of `ymm7`. -/
theorem reduce_lanes (s : State) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (reduce .xmm7)) s fun s' =>
      (∀ l < 2, s'.lane .xmm7 l = Pclmul.reduce (prod (s.proj l))) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7] s s' := by
  refine WP.mono (WP.lanes (ss := Impl.Gcm.X86_64.Pclmul.reduce .xmm7) rfl fun l hl =>
      reduce_ok .xmm7 (s.proj l) (by decide) (by decide) (by decide) (by decide) (by simpa using h1 l hl))
    fun s' ⟨hk, hq⟩ => ⟨fun l hl => by simpa using (hq l hl).1,
      yframe_of_lanes hk fun l hl r hr => (hq l hl).2.xmm r hr⟩

/-- The two lanes' blocks added into `xmm2`, whose upper lane is cleared. -/
theorem combine_ok (s : State) :
    WP isa (.block combine) s
      fun s' => s'.lane .xmm2 0 = s.lane .xmm7 0 ^^^ s.lane .xmm7 1 ∧ s'.lane .xmm2 1 = 0 ∧
        YFrame [.xmm11, .xmm2] s s' := by
  rw [combine, WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨by simp [VBinOp.sse, Pclmul.eval_pxor, VOp.exec, State.setV, State.lane], by simp, by simp,
    by simp, by simp, by simp, fun r hr l hl => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
    simp [hr.1, hr.2, VOp.exec, State.setV, State.lane]

/-- The end of the eight-block body: `add rdx, 128`, `sub rcx, 8`, `cmp rcx, 8`. -/
theorem next_ok (s : State) :
    WP isa (.block next) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 128 ∧ s'.gpr .rcx = s.gpr .rcx - 8 ∧
        s'.cf = some (decide ((s.gpr .rcx - 8).toNat < 8)) ∧
        (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  rw [next]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-! ## The eight-block loop -/

/-- What holds after `i` blocks of the eight-block loop: `vg_ghash_pclmul`'s
invariant, the upper lanes, and the powers `x · Tₖ = Hᵏ` (`k` from 1 to 8)
in the lanes of `ymm12`–`ymm15`. -/
structure Inv8 (s₀ : State) (i : Nat) (s : State) : Prop where
  inv : Inv s₀ i s
  m0 : s.lane .xmm0 1 = revMask
  m1 : s.lane .xmm1 1 = poly
  y1 : s.lane .xmm2 1 = 0
  pw : ∀ k < 4, ∀ l < 2, x * φ (s.lane (preg k) l) = φ (H₀ s₀) ^ (8 - 2 * k - l)

theorem Inv8.l0 {s₀ : State} {i : Nat} {s : State} (h : Inv8 s₀ i s) : ∀ l < 2, s.lane .xmm0 l = revMask :=
  fun l hl => by rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [h.inv.x0, h.m0]

theorem Inv8.l1 {s₀ : State} {i : Nat} {s : State} (h : Inv8 s₀ i s) : ∀ l < 2, s.lane .xmm1 l = poly :=
  fun l hl => by rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [h.inv.x1, h.m1]

/-- Blocks `i + 2k` and `i + 2k + 1` are in the data. -/
theorem in_blk32 {s₀ : State} (hp : Pre s₀) {i k : Nat} (h : i + 2 * k + 2 ≤ nb s₀) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32 := by
  have := hp.nb_lt
  refine ⟨Pclmul.dR s₀, by simp [hp.rd], ?_⟩
  rw [addr_add]
  exact Pclmul.contains_offset (by omega) (by omega)

/-- The address of lane `l` of the `k`-th load of a body at block `i`. -/
theorem lane_addr (p : Addr) (i k l : Nat) :
    p + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      p + BitVec.ofNat 64 (16 * (i + (2 * k + l))) := by
  rw [addr_add, add_ofNat_ofNat p (c := 16 * (i + (2 * k + l))) (by omega)]

theorem zero_xor' (a : BitVec 128) : (0 : BitVec 128) ^^^ a = a := by simp

/-- Block `i + j` of the data. -/
abbrev X8 (s₀ : State) (i j : Nat) : Block := blockAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (i + j)))

/-- What a lane's products are after the four loads. -/
def lanes (s₀ s : State) (i l : Nat) : Prod :=
  (((Prod.zero.acc (s.lane .xmm2 l ^^^ X8 s₀ i l) (s.lane (preg 0) l)).acc (X8 s₀ i (2 + l))
    (s.lane (preg 1) l)).acc (X8 s₀ i (4 + l)) (s.lane (preg 2) l)).acc (X8 s₀ i (6 + l)) (s.lane (preg 3) l)

/-- One load of the eight-block body, from a state the earlier ones left. -/
theorem load_step {s₀ : State} (hp : Pre s₀) {i k : Nat} (hk : k < 4) (hi : i + 8 ≤ nb s₀) {s t : State}
    (h0 : ∀ l < 2, s.lane .xmm0 l = revMask) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hrdx : s.gpr .rdx = blkAddr s₀ i) (ht : YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s t) :
    WP isa (.block (load k)) t fun t' =>
      (∀ l < 2, prod (t'.proj l) = (prod (t.proj l)).acc
        ((if k = 0 then t.lane .xmm2 l else 0) ^^^ X8 s₀ i (2 * k + l)) (s.lane (preg k) l)) ∧
      YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s t' := by
  have := hp.nb_lt
  obtain ⟨n7, n8, n9, n10, n11, -, -, -⟩ := preg_ne (k := k)
  refine WP.mono (load_ok hk t (fun l hl => by rw [ht.lane _ (by decide) l hl]; exact h0 l hl)
    (by rw [ht.rd, ht.wr, ht.gpr, hrd, hwr, hrdx]; exact in_blk32 hp (by omega))) fun t' ⟨a, f⟩ => ⟨?_, ht.trans f⟩
  intro l hl
  rw [a l hl, ht.mem, ht.gpr, hm, hrdx, blkAddr, lane_addr,
    ht.lane (preg k) (by simp [n7, n8, n9, n10, n11]) l hl]

theorem loads_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i + 8 ≤ nb s₀) {s : State}
    (h0 : ∀ l < 2, s.lane .xmm0 l = revMask) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hrdx : s.gpr .rdx = blkAddr s₀ i) :
    WP isa (.block (zero ++ (load 0 ++ (load 1 ++ (load 2 ++ load 3))))) s fun t =>
      (∀ l < 2, prod (t.proj l) = lanes s₀ s i l) ∧ YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_
  have F₁ := f₁.mono (rs' := [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11]) (by decide)
  have y₁ : ∀ l < 2, s₁.lane .xmm2 l = s.lane .xmm2 l := fun l hl => F₁.lane _ (by decide) l hl
  rw [WP.block_append_iff]
  refine WP.mono (load_step hp (k := 0) (by decide) hi h0 hm hrd hwr hrdx F₁) fun s₂ ⟨a₂, f₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_step hp (k := 1) (by decide) hi h0 hm hrd hwr hrdx f₂) fun s₃ ⟨a₃, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_step hp (k := 2) (by decide) hi h0 hm hrd hwr hrdx f₃) fun s₄ ⟨a₄, f₄⟩ => ?_
  refine WP.mono (load_step hp (k := 3) (by decide) hi h0 hm hrd hwr hrdx f₄) fun s₅ ⟨a₅, f₅⟩ => ⟨?_, f₅⟩
  intro l hl
  rw [a₅ l hl, a₄ l hl, a₃ l hl, a₂ l hl, z₁ l hl, y₁ l hl]
  simp only [lanes, ↓reduceIte, Nat.one_ne_zero, Nat.reduceEqDiff, zero_xor', Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul]

/-- `GHASH` over eight more blocks. -/
theorem ghashFrom_succ8 (h y : Block) (m : Mem) (p : Addr) (i : Nat) :
    ghashFrom h y (blocksAt m p (i + 8)) =
      let X : Nat → Block := fun j => blockAt m (p + BitVec.ofNat 64 (16 * (i + j)))
      mul (mul (mul (mul (mul (mul (mul (mul (ghashFrom h y (blocksAt m p i) ^^^ X 0) h ^^^ X 1) h ^^^ X 2) h
        ^^^ X 3) h ^^^ X 4) h ^^^ X 5) h ^^^ X 6) h ^^^ X 7) h := by
  rw [show i + 8 = i + 7 + 1 from rfl, ghashFrom_blocksAt_succ, show i + 7 = i + 6 + 1 from rfl,
    ghashFrom_blocksAt_succ, show i + 6 = i + 5 + 1 from rfl, ghashFrom_blocksAt_succ,
    show i + 5 = i + 4 + 1 from rfl, ghashFrom_blocksAt_succ, show i + 4 = i + 3 + 1 from rfl,
    ghashFrom_blocksAt_succ, show i + 3 = i + 2 + 1 from rfl, ghashFrom_blocksAt_succ,
    show i + 2 = i + 1 + 1 from rfl, ghashFrom_blocksAt_succ, ghashFrom_blocksAt_succ]
  rfl

/-- The two lanes' reductions, after the four loads, are `Y` after eight more
blocks. -/
theorem lanes_eq {s₀ s : State} {i : Nat} (hI : Inv8 s₀ i s) :
    reduce (lanes s₀ s i 0) ^^^ reduce (lanes s₀ s i 1) =
      ghashFrom (H₀ s₀) (Pclmul.Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 8)) := by
  have e2 : s.lane .xmm2 0 = ghashFrom (H₀ s₀) (Pclmul.Y₀ s₀) (blocksAt s₀.mem (dp s₀) i) := hI.inv.y
  rw [ghashFrom_succ8]
  simp only [lanes, hI.y1, zero_xor', e2, Nat.add_zero]
  have h₁ := hI.pw 3 (by decide) 1 (by decide)
  have h₂ := hI.pw 3 (by decide) 0 (by decide)
  have h₃ := hI.pw 2 (by decide) 1 (by decide)
  have h₄ := hI.pw 2 (by decide) 0 (by decide)
  have h₅ := hI.pw 1 (by decide) 1 (by decide)
  have h₆ := hI.pw 1 (by decide) 0 (by decide)
  have h₇ := hI.pw 0 (by decide) 1 (by decide)
  have h₈ := hI.pw 0 (by decide) 0 (by decide)
  rw [show 8 - 2 * 3 - 1 = 1 from rfl, pow_one] at h₁
  rw [show 8 - 2 * 3 - 0 = 2 from rfl] at h₂
  rw [show 8 - 2 * 2 - 1 = 3 from rfl] at h₃
  rw [show 8 - 2 * 2 - 0 = 4 from rfl] at h₄
  rw [show 8 - 2 * 1 - 1 = 5 from rfl] at h₅
  rw [show 8 - 2 * 1 - 0 = 6 from rfl] at h₆
  rw [show 8 - 2 * 0 - 1 = 7 from rfl] at h₇
  rw [show 8 - 2 * 0 - 0 = 8 from rfl] at h₈
  exact step8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈

theorem body8_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i + 8 ≤ nb s₀) {s : State}
    (hI : Inv8 s₀ i s) :
    WP isa (.block body8) s fun s' =>
      Inv8 s₀ (i + 8) s' ∧ s'.cf = some (decide (nb s₀ - (i + 8) < 8)) := by
  have hn := hp.nb_lt
  rw [show body8 = (zero ++ (load 0 ++ (load 1 ++ (load 2 ++ load 3)))) ++
      (reduce .xmm7 ++ (combine ++ next)) by simp only [body8, List.append_assoc], WP.block_append_iff]
  refine WP.mono (loads_ok hp hi hI.l0 hI.inv.mem hI.inv.rd hI.inv.wr hI.inv.rdx) fun s₅ ⟨p₅, F₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_lanes s₅ (fun l hl => by rw [F₅.lane _ (by decide) l hl]; exact hI.l1 l hl))
    fun s₆ ⟨r₆, f₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (combine_ok s₆) fun s₇ ⟨c₇, y₇, f₇⟩ => ?_
  have F₇ := (F₅.comp f₆).comp f₇
  refine WP.mono (next_ok s₇) fun s' ⟨frdx, frcx, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  have kl : ∀ r, r ≠ .xmm2 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 →
      ∀ l < 2, s'.lane r l = s.lane r l := fun r h2 h7 h8 h9 h10 h11 l hl => by
    rw [fl, F₇.lane r (by simp [h2, h7, h8, h9, h10, h11]) l hl]
  have kx : ∀ r, r ≠ .xmm2 → r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 →
      s'.xmm r = s.xmm r := fun r h2 h7 h8 h9 h10 h11 => by
    simpa [State.lane] using kl r h2 h7 h8 h9 h10 h11 0 (by decide)
  have y' : s'.xmm .xmm2 = ghashFrom (H₀ s₀) (Pclmul.Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 8)) := by
    show s'.lane .xmm2 0 = _
    rw [fl, c₇, r₆ 0 (by decide), r₆ 1 (by decide), p₅ 0 (by decide), p₅ 1 (by decide), lanes_eq hI]
  have hrdx : s₇.gpr .rdx = blkAddr s₀ i := by rw [F₇.gpr, hI.inv.rdx]
  have hrcx : s₇.gpr .rcx - 8 = BitVec.ofNat 64 (nb s₀ - (i + 8)) := by
    rw [F₇.gpr, hI.inv.rcx]
    exact ofNat_sub_ofNat (k := 8) (by omega) (by have := (s₀.gpr .rcx).isLt; omega)
  have k2 := fun r h2 h7 h8 h9 h10 h11 => kx r h2 h7 h8 h9 h10 h11
  refine ⟨⟨⟨by omega, by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.inv.x0], by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.inv.x1], by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.inv.t1], by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.inv.t2], by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.inv.t3], by rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.inv.t4], y', fun r ha hd hc => by rw [fg r hd hc, F₇.gpr, hI.inv.gpr r ha hd hc],
      by rw [frdx, hrdx]; exact add_ofNat_ofNat (b := 128) _ (by omega), by rw [frcx, hrcx],
      by rw [fm, F₇.mem, hI.inv.mem], by rw [frd, F₇.rd, hI.inv.rd], by rw [fwr, F₇.wr, hI.inv.wr]⟩,
    by rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide), hI.m0],
    by rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide), hI.m1],
    by rw [fl, y₇], fun k hk l hl => ?_⟩, ?_⟩
  · obtain ⟨n7, n8, n9, n10, n11, -, -, n2⟩ := preg_ne (k := k)
    rw [kl _ n2 n7 n8 n9 n10 n11 l hl]; exact hI.pw k hk l hl
  · rw [fcf, hrcx, toNat_ofNat_lt (by omega)]

/-! ## The powers -/

/-- The lanes paired, and the upper lanes of the mask, the reduction constant
and `Y`. -/
theorem pairs_ok (s : State) :
    WP isa (.block [.vop (.vinserti128 .xmm15 .xmm15 .xmm14 1), .vop (.vinserti128 .xmm14 .xmm13 .xmm12 1),
        .vop (.vinserti128 .xmm13 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm12 .xmm4 .xmm3 1),
        .vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1),
        .vop (.vmovdqa .l128 .xmm2 .xmm2)]) s fun s' =>
      s'.lane .xmm15 0 = s.xmm .xmm15 ∧ s'.lane .xmm15 1 = s.xmm .xmm14 ∧
      s'.lane .xmm14 0 = s.xmm .xmm13 ∧ s'.lane .xmm14 1 = s.xmm .xmm12 ∧
      s'.lane .xmm13 0 = s.xmm .xmm6 ∧ s'.lane .xmm13 1 = s.xmm .xmm5 ∧
      s'.lane .xmm12 0 = s.xmm .xmm4 ∧ s'.lane .xmm12 1 = s.xmm .xmm3 ∧
      s'.lane .xmm0 1 = s.xmm .xmm0 ∧ s'.lane .xmm1 1 = s.xmm .xmm1 ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ r, r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, getLsbD_one8, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa,
    State.setV, State.lane, Option.some.injEq, exists_eq_left', and_self]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r h12 h13 h14 h15 => ?_, trivial⟩
  by_cases h0 : r = .xmm0
  · subst h0; rfl
  by_cases h1 : r = .xmm1
  · subst h1; rfl
  by_cases h2 : r = .xmm2
  · subst h2; rfl
  simp [h0, h1, h2, h12, h13, h14, h15]

/-- `H'⁵`–`H'⁸`, and the eight powers in the lanes of `ymm12`–`ymm15`. -/
theorem powers_ok {s₀ : State} {i : Nat} {s : State} (hI : Inv s₀ i s) :
    WP isa (.block powers) s (Inv8 s₀ i) := by
  simp only [powers, List.append_assoc]
  have h1 := hI.x1
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm12 .xmm6 .xmm3 s (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1)
    fun s₁ ⟨m₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm13 .xmm12 .xmm3 s₁ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [o₁.xmm _ (by decide), h1])) fun s₂ ⟨m₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm14 .xmm13 .xmm3 s₂ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1])) fun s₃ ⟨m₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok .xmm15 .xmm14 .xmm3 s₃ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [o₃.xmm _ (by decide), o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1])) fun s₄ ⟨m₄, o₄⟩ => ?_
  have O := (o₁.trans o₂).trans (o₃.trans o₄)
  refine WP.mono (pairs_ok s₄) fun s' ⟨p15, q15, p14, q14, p13, q13, p12, q12, p0, p1, p2, kx, g, m, rd, wr⟩ => ?_
  have k : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → r ≠ .xmm12 → r ≠ .xmm13 → r ≠ .xmm14 →
      r ≠ .xmm15 → s'.xmm r = s.xmm r := fun r h8 h9 h10 h11 h12 h13 h14 h15 => by
    rw [kx r h12 h13 h14 h15, O.xmm r (by simp [h8, h9, h10, h11, h12, h13, h14, h15])]
  have e3 : ∀ t : State, Only [.xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t → t.xmm .xmm3 = s.xmm .xmm3 :=
    fun t o => o.xmm _ (by decide)
  -- The powers.
  have H1 := hI.t1
  have H4 := hI.t4
  have H5 : x * φ (s₁.xmm .xmm12) = φ (H₀ s₀) ^ 5 := by
    rw [m₁, show ∀ a b : Q, x * (x * a * b) = (x * a) * (x * b) from fun a b => by ring, H4, H1]; ring
  have H6 : x * φ (s₂.xmm .xmm13) = φ (H₀ s₀) ^ 6 := by
    rw [m₂, o₁.xmm .xmm3 (by decide),
      show ∀ a b : Q, x * (x * a * b) = (x * a) * (x * b) from fun a b => by ring, H5, H1]; ring
  have H7 : x * φ (s₃.xmm .xmm14) = φ (H₀ s₀) ^ 7 := by
    rw [m₃, (o₁.trans o₂).xmm .xmm3 (by decide),
      show ∀ a b : Q, x * (x * a * b) = (x * a) * (x * b) from fun a b => by ring, H6, H1]; ring
  have H8 : x * φ (s₄.xmm .xmm15) = φ (H₀ s₀) ^ 8 := by
    rw [m₄, ((o₁.trans o₂).trans o₃).xmm .xmm3 (by decide),
      show ∀ a b : Q, x * (x * a * b) = (x * a) * (x * b) from fun a b => by ring, H7, H1]; ring
  have r12 : s₄.xmm .xmm12 = s₁.xmm .xmm12 := by rw [(o₂.trans (o₃.trans o₄)).xmm _ (by decide)]
  have r13 : s₄.xmm .xmm13 = s₂.xmm .xmm13 := by rw [(o₃.trans o₄).xmm _ (by decide)]
  have r14 : s₄.xmm .xmm14 = s₃.xmm .xmm14 := by rw [o₄.xmm _ (by decide)]
  have s3 : ∀ r, r = .xmm3 ∨ r = .xmm4 ∨ r = .xmm5 ∨ r = .xmm6 → s₄.xmm r = s.xmm r := by
    rintro r (rfl | rfl | rfl | rfl) <;> exact O.xmm _ (by decide)
  refine ⟨⟨hI.le, by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hI.x0], by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hI.x1], by rw [k _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hI.t1], by rw [k _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hI.t2], by rw [k _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.t3], by rw [k _ (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.t4],
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI.y], fun r ha hd hc => by rw [g, O.gpr r ha, hI.gpr r ha hd hc],
      by rw [g, O.gpr _ (by decide), hI.rdx], by rw [g, O.gpr _ (by decide), hI.rcx],
      by rw [m, O.mem, hI.mem], by rw [rd, O.rd, hI.rd], by rw [wr, O.wr, hI.wr]⟩,
    by rw [p0, O.xmm _ (by decide), hI.x0], by rw [p1, O.xmm _ (by decide), hI.x1], p2, fun k hk l hl => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · show x * φ (s'.lane .xmm15 0) = φ (H₀ s₀) ^ 8; rw [p15]; exact H8
  · show x * φ (s'.lane .xmm15 1) = φ (H₀ s₀) ^ 7; rw [q15, r14]; exact H7
  · show x * φ (s'.lane .xmm14 0) = φ (H₀ s₀) ^ 6; rw [p14, r13]; exact H6
  · show x * φ (s'.lane .xmm14 1) = φ (H₀ s₀) ^ 5; rw [q14, r12]; exact H5
  · show x * φ (s'.lane .xmm13 0) = φ (H₀ s₀) ^ 4; rw [p13, s3 .xmm6 (by decide)]; exact H4
  · show x * φ (s'.lane .xmm13 1) = φ (H₀ s₀) ^ 3; rw [q13, s3 .xmm5 (by decide)]; exact hI.t3
  · show x * φ (s'.lane .xmm12 0) = φ (H₀ s₀) ^ 2; rw [p12, s3 .xmm4 (by decide)]; exact hI.t2
  · show x * φ (s'.lane .xmm12 1) = φ (H₀ s₀) ^ 1; rw [q12, s3 .xmm3 (by decide), H1, pow_one]

/-! ## The whole function -/

/-- `cmp rcx, c`, after `i` blocks. -/
theorem cmp_ok {s₀ : State} (hp : Pre s₀) {i : Nat} {s : State} (hI : Inv s₀ i s) (c : Nat) (hc : c < 2 ^ 31)
    (ec : BitVec.signExtend 64 (BitVec.ofNat 32 c) = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .cmp .rcx (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      Inv s₀ i s' ∧ s'.cf = some (decide (nb s₀ - i < c)) := by
  have hn := hp.nb_lt
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, ec, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with }, ?_⟩
  simp only [toNat_ofNat_lt (show nb s₀ - i < 2 ^ 64 by omega), toNat_ofNat_lt (show c < 2 ^ 64 by omega)]

/-- `vzeroupper`, and `cmp rcx, 4`. -/
theorem mid_ok {s₀ : State} (hp : Pre s₀) {i : Nat} {s : State} (hI : Inv s₀ i s) :
    WP isa (.block [.vop .vzeroupper, .alu .cmp .rcx (.imm 4)]) s fun s' =>
      Inv s₀ i s' ∧ s'.cf = some (decide (nb s₀ - i < 4)) := by
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.mono (cmp_ok hp (c := 4) ?_ (by decide) (by decide)) fun s' h => h⟩
  exact { hI with }

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' := by
  have hn := hp.nb_lt
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok hp) fun s₁ ⟨hI₁, _⟩ => WP.mono (cmp_ok hp hI₁ 8 (by decide) (by decide)) fun s₂ ⟨hI₂, hcf⟩ => ?_
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 8 ∧ Inv s₀ i s) ?_ fun s₃ ⟨i, _, hI₃⟩ =>
    WP.seq (WP.mono (mid_ok hp hI₃) fun s₄ ⟨hI₄, hcf₄⟩ => tail_ok hp hI₄ hcf₄))
  refine WP.ite (decide (nb s₀ - 0 < 8)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨0, by simpa using h, hI₂⟩
  · refine WP.seq (WP.mono (powers_ok hI₂) fun s₃ hI₃ => ?_)
    let I8 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 8 ≤ nb s₀ ∧ Inv8 s₀ i s
    have hstep : ∀ m s, I8 m s → WP isa (.block body8) s (fun s' =>
        (eval .ae s' = some false ∧ ∃ i, nb s₀ - i < 8 ∧ Inv s₀ i s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body8_ok hp hi hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - (i + 8) < 8
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true], i + 8,
          hlt, hI'.inv⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - (i + 8), by omega, i + 8, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I8 hstep (nb s₀) s₃ ⟨0, rfl, by simp at h; omega, hI₃⟩

theorem ghash_correct (s : State) (hs : ghashX86_64.pre s) :
    ∃ t s', Exec isa ghash s t s' ∧ abiPreserved s s' ∧ ghashX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem ghash_ct : ConstantTime isa ghashX86_64.pre ghashX86_64.pub ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem ghash_verified :
    Verified X86_64.target ghash (Spec.Gcm.ghashContract X86_64.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.X86_64.Pclmul.ghashX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Gcm.X86_64.Pclmul.satState] using
      Proof.Gcm.X86_64.Pclmul.satState)

end VG.Proof.Gcm.X86_64.Vpclmul
