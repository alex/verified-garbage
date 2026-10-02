import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Finish

/-!
# X25519 on x86-64 with AVX512_IFMA: before the loop

`vsetup` puts the constants into the working space and the ladder's first
state `(1, 0, x₁, 1)` into the lanes of `ymm0–ymm4`, with `x₁` split into
limbs from its four words at `X1`.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word val4 F E fe)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## The constants into registers -/

/-- The registers `consts` writes. -/
def cregs : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12]

theorem consts_wp (s : State) :
    WP isa (.block consts) s fun s' =>
      s'.gpr .rax = 0x7ffffffffffff ∧ s'.gpr .rcx = 19 ∧ s'.gpr .rdx = 0x4000000000000000 - 38912 ∧
      s'.gpr .rbp = 0x4000000000000000 - 2048 ∧ s'.gpr .r8 = 0x1fff ∧ s'.gpr .r9 = 0x3ffffff ∧
      s'.gpr .r10 = 0x7fffffffff ∧ s'.gpr .r11 = 1 ∧ s'.gpr .r12 = 121665 ∧
      (∀ r, r ∉ cregs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [cregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## The vector block -/

def initS : Sym := symOf vinit

/-- Limb `j` of `x₁`, from its words (`w`) and the mask `m`. -/
def limbNat (w : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => w 0 &&& m
  | 1 => w 0 / 2 ^ 51 ||| (w 1 &&& m / 2 ^ 13) * 2 ^ 13
  | 2 => w 1 / 2 ^ 38 ||| (w 2 &&& m / 2 ^ 26) * 2 ^ 26
  | 3 => w 2 / 2 ^ 25 ||| (w 3 &&& m / 2 ^ 39) * 2 ^ 39
  | _ => w 3 / 2 ^ 12

theorem initS_regs (E : Env) : ∀ j < 5, ∀ l < 4, (initS.reg j).nat E l =
    if l = 2 then limbNat (fun k => E.m X1 k) (E.g .rax) j
    else if j = 0 ∧ (l = 0 ∨ l = 3) then E.g .r11 else 0 := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- The term `vinit` stores at `d`. -/
def initT (d : Nat) : T := ((initS.st.find? fun x => x.1 == d).getD (0, .zero)).2

theorem initT_mem : ∀ d ∈ [KM, K19, KB0, KB1, K13, K26, K39, KX1, KX1 + 32, KX1 + 64, KX1 + 96, KX1 + 128,
    KA24, KA24 + 32, KA24 + 64, KA24 + 96, KA24 + 128], (d, initT d) ∈ initS.st := by decide +kernel

theorem initT_kx1 (E : Env) : ∀ j < 5, ∀ l < 4, (initT (KX1 + 32 * j)).nat E l =
    if l = 3 then limbNat (fun k => E.m X1 k) (E.g .rax) j
    else if j = 0 ∧ (l = 0 ∨ l = 2) then E.g .r11 else 0 := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem initT_a24 (E : Env) : ∀ j < 5, ∀ l < 4, (initT (KA24 + 32 * j)).nat E l =
    if j = 0 ∧ l = 3 then E.g .r12 else 0 := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem initT_const : ∀ x ∈ [(KM, Reg.rax), (K19, .rcx), (KB0, .rdx), (KB1, .rbp), (K13, .r8), (K26, .r9),
    (K39, .r10)], initT x.1 = .bc (.lane0 (.gpr x.2)) := by decide +kernel

theorem initS_small : ∀ x ∈ initS.st, x.1 < 2 ^ 62 := by decide +kernel
theorem initS_apart : Apart initS.st := by decide +kernel
theorem initS_range : ∀ x ∈ initS.st, 1664 ≤ x.1 ∧ x.1 + 32 ≤ 1664 + 544 := by decide +kernel

def initB : Bnds :=
  ⟨fun _ => 2 ^ 64 - 1,
    fun g => if g = .rax then 2 ^ 51 - 1 else if g = .r11 then 1 else if g = .r12 then 121665 else 2 ^ 64 - 1,
    fun _ => 2 ^ 64 - 1, fun _ => 0⟩

theorem initS_ok : ∀ j < 5, ∀ l < 4, (initS.reg j).ok initB l = true ∧ (initS.reg j).bnd initB l < 2 ^ 52 := by
  decide +kernel

theorem initT_ok : ∀ d ∈ [KX1, KX1 + 32, KX1 + 64, KX1 + 96, KX1 + 128, KA24, KA24 + 32, KA24 + 64, KA24 + 96,
    KA24 + 128], ∀ l < 4, (initT d).ok initB l = true := by decide +kernel

/-- The limbs stand for the words' number. -/
theorem limbNat_lv (w : Nat → Nat) (hw : ∀ k < 4, w k < 2 ^ 64) :
    lv (limbNat w (2 ^ 51 - 1)) = w 0 + 2 ^ 64 * w 1 + 2 ^ 128 * w 2 + 2 ^ 192 * w 3 := by
  have e13 : (2 ^ 51 - 1) / 2 ^ 13 = 2 ^ 38 - 1 := by decide
  have e26 : (2 ^ 51 - 1) / 2 ^ 26 = 2 ^ 25 - 1 := by decide
  have e39 : (2 ^ 51 - 1) / 2 ^ 39 = 2 ^ 12 - 1 := by decide
  have h0 := hw 0 (by decide); have h1 := hw 1 (by decide); have h2 := hw 2 (by decide)
  simp only [lv, limbNat, e13, e26, e39, Nat.and_two_pow_sub_one_eq_mod]
  rw [or_mul (by omega), or_mul (by omega), or_mul (by omega)]
  omega

/-- The limbs of `x₁`, from its words at `X1`. -/
def xl (m : Mem) (base : Addr) : Nat → Nat :=
  limbNat (fun k => (word m base (X1 + 8 * k)).toNat) (2 ^ 51 - 1)

theorem initB_env {s : State} (ha : s.gpr .rax = 0x7ffffffffffff)
    (h11 : s.gpr .r11 = 1) (h12 : s.gpr .r12 = 121665) : EnvOK s initB := by
  refine ⟨fun r k _ => lt64 _, fun g => ?_, fun d k _ => lt64 _, fun _ _ _ => Nat.zero_le _⟩
  simp only [initB]
  split
  · subst_vars; rw [ha]; decide
  · split
    · subst_vars; rw [h11]; decide
    · split
      · subst_vars; rw [h12]; decide
      · exact lt64 _

theorem stores_const {s₀ : State} {base : Addr} {m : Mem} {st : List (Nat × T)} {d : Nat} {r : Reg}
    (h : (d, T.bc (.lane0 (.gpr r))) ∈ st) (hs : ∀ x ∈ st, x.1 < 2 ^ 62) (ha : Apart st) {l : Nat} (hl : l < 4) :
    mq (stores s₀ base st m) base (d + 8 * l) = s₀.gpr r := by
  rw [stores_mq _ _ _ _ h hl hs ha]; simp only [T.eval, ite_true]

/-- `vsetup`: the constants, and `(1, 0, x₁, 1)` in the lanes. -/
theorem vsetup_wp {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vsetup) s fun s' => (∀ r, r ∉ cregs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧ Outside base 1664 544 s.mem s'.mem ∧
      Consts s'.mem base (xl s.mem base) ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i =
        if l = 2 then xl s.mem base i else if i = 0 ∧ (l = 0 ∨ l = 3) then 1 else 0) := by
  rw [vsetup, WP.block_append_iff]
  refine WP.mono (consts_wp s) fun s₁ ⟨ha, hc, hd, hb, h8, h9, h10, h11, h12, g₁, m₁, rd₁, wr₁, _, _, x₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  have hE := initB_env ha h11 h12
  have e : Sym.init.run vinit = some initS := symOf_eq _ _
  refine WP.mono (run_ok (scr_ctx hs₁) e) fun s₂ h => ?_
  have hmem : s₂.mem = stores s₁ base initS.st s₁.mem := by rw [h.mem, hs₁.rdi]
  have hX : ∀ k, (envOf s₁).m X1 k = (word s.mem base (X1 + 8 * k)).toNat := fun k => by
    rw [envOf_m hs₁.rdi, m₁]; rfl
  have hxl : (fun k => (envOf s₁).m X1 k) = fun k => (word s.mem base (X1 + 8 * k)).toNat :=
    funext hX
  have hg : ∀ r, (envOf s₁).g r = (s₁.gpr r).toNat := fun _ => rfl
  have cst : ∀ d r l, (d, r) ∈ [(KM, Reg.rax), (K19, .rcx), (KB0, .rdx), (KB1, .rbp), (K13, .r8), (K26, .r9),
      (K39, .r10)] → l < 4 → (mq s₂.mem base (d + 8 * l)).toNat = (s₁.gpr r).toNat := fun d r l hd hl => by
    have t := initT_const _ hd
    have hm := initT_mem d (by simp only [List.mem_cons] at hd ⊢; rcases hd with h | h | h | h | h | h | h | h <;>
      simp_all)
    simp only at t
    rw [t] at hm
    rw [hmem, stores_const hm initS_small initS_apart hl]
  have kx : ∀ j < 5, ∀ l < 4, slotv s₂.mem base KX1 l j =
      if l = 3 then xl s.mem base j else if j = 0 ∧ l ≠ 1 then 1 else 0 := fun j hj l hl => by
    have hm := initT_mem (KX1 + 32 * j) (by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [slotv, hmem, stores_mq _ _ _ _ hm hl initS_small initS_apart,
      (nat_ok hE _ hl (initT_ok _ (by
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide) l hl)).1,
      initT_kx1 _ j hj l hl, hxl, hg, hg, ha, h11]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> simp [xl]
  have ka : ∀ j < 5, ∀ l < 4, slotv s₂.mem base KA24 l j = if j = 0 ∧ l = 3 then 121665 else 0 :=
    fun j hj l hl => by
      have hm := initT_mem (KA24 + 32 * j) (by
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide)
      rw [slotv, hmem, stores_mq _ _ _ _ hm hl initS_small initS_apart,
        (nat_ok hE _ hl (initT_ok _ (by
          rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide) l hl)).1,
        initT_a24 _ j hj l hl, hg, h12]
      rfl
  have lan : ∀ l < 4, ∀ i < 5, lanes s₂ 0 l i =
      if l = 2 then xl s.mem base i else if i = 0 ∧ (l = 0 ∨ l = 3) then 1 else 0 := fun l hl i hi => by
    obtain ⟨o, _⟩ := initS_ok i hi l hl
    have := (h.out hE (by omega) hl o).1
    simp only [lanes, Nat.zero_add] at this ⊢
    rw [this, initS_regs _ i hi l hl, hxl, hg, hg, ha, h11]
    rfl
  refine ⟨fun r hr => by rw [vm_gpr h.eq, g₁ r hr], by rw [vm_rd h.eq, rd₁], by rw [vm_wr h.eq, wr₁],
    by rw [h.mxcsr, x₁], ?_, ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, ka, kx,
      fun i hi => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, lan⟩
  · rw [hmem, m₁]; exact stores_outside _ _ _ (by decide) _ initS_range
  · rw [cst KM .rax l (by decide) hl, ha]; rfl
  · rw [cst K19 .rcx l (by decide) hl, hc]; rfl
  · rw [cst KB0 .rdx l (by decide) hl, hd]; rfl
  · rw [cst KB1 .rbp l (by decide) hl, hb]; rfl
  · have := (initS_ok i hi 2 (by decide)).2
    have e := (h.out hE (by omega) (show 2 < 4 by decide) (initS_ok i hi 2 (by decide)).1)
    have l2 := lan 2 (by decide) i hi
    simp only [lanes, Nat.zero_add, ite_true] at l2
    rw [← l2]; omega
  · rw [cst K13 .r8 l (by decide) hl, h8]; rfl
  · rw [cst K26 .r9 l (by decide) hl, h9]; rfl
  · rw [cst K39 .r10 l (by decide) hl, h10]; rfl

end VG.Proof.X25519.X86_64.Ifma
