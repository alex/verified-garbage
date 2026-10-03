import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Stage
import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop

/-! Merged from `Proof.Ed25519.X86_64.Ifma.Block`. -/
section
/-!
# Ed25519 doublings with AVX512_IFMA: the blocks as facts about states

Each vector block of `Ifma.double4` but X25519's products and carries: the
limbs it leaves in registers and slots (`lanes`, `slotv`), as numbers, from
those it starts with, and what it keeps.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord)
open VG.Proof.X25519.X86_64.Ifma (Sym T Env Bnds EnvOK symOf symOf_eq limbNat lanes slotv mq CConsts
  envOK_of envOf envOf_m envOf_v lt64 run_ok SRel.out SRel.keep stores stores_mq stores_outside xi_xr kbv
  kb_m nat_ok vm)
open VG.Proof.X25519.X86_64 (Outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4)

/-- The constants of the doublings: the carries' and differences', and
`vstore`'s masks. -/
structure EConsts (m : Mem) (base : Addr) : Prop extends CConsts m base where
  k13 : ∀ l < 4, (mq m base (EK13 + 8 * l)).toNat = 2 ^ 13 - 1
  k26 : ∀ l < 4, (mq m base (EK26 + 8 * l)).toNat = 2 ^ 26 - 1
  k39 : ∀ l < 4, (mq m base (EK39 + 8 * l)).toNat = 2 ^ 39 - 1

/-- The constants are kept by anything that changes only `OPL` and `OPV`. -/
theorem EConsts.outside {m m' : Mem} {base : Addr} (hk : EConsts m base)
    (h : Outside base 1024 320 m m') : EConsts m' base := by
  have w : ∀ d, 1344 ≤ d → d + 8 ≤ 4096 → mq m' base d = mq m base d := fun d h1 h2 => by
    rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
    exact h.word (by omega) (by omega)
  refine ⟨⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, fun l hl => ?_,
    fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [w _ (by simp only [EK13]; omega) (by simp only [EK13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [EK26]; omega) (by simp only [EK26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [EK39]; omega) (by simp only [EK39]; omega)]; exact hk.k39 l hl

/-! ## Loading -/

theorem loadB_env {s : State} (ha : s.gpr .rax = 0x7ffffffffffff) : EnvOK s loadB := by
  refine ⟨fun r k _ => lt64 _, fun g => ?_, fun d k _ => lt64 _, fun _ _ _ => Nat.zero_le _⟩
  simp only [loadB]
  split
  · subst_vars; rw [ha]; decide
  · exact lt64 _

theorem stores_const {s₀ : State} {base : Addr} {m : Mem} {st : List (Nat × T)} {d : Nat} {r : Reg}
    (h : (d, T.bc (.lane0 (.gpr r))) ∈ st) (hs : ∀ x ∈ st, x.1 < 2 ^ 62)
    (ha : VG.Proof.X25519.X86_64.Ifma.Apart st) {l : Nat} (hl : l < 4) :
    mq (stores s₀ base st m) base (d + 8 * l) = s₀.gpr r := by
  rw [stores_mq _ _ _ _ h hl hs ha]; simp only [T.eval, ite_true]

/-- `vload`: the constants, and the limbs of slots 0–3 in the lanes. -/
theorem vload_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (ha : s.gpr .rax = 0x7ffffffffffff) (hcx : s.gpr .rcx = 19)
    (hd : s.gpr .rdx = 0x4000000000000000 - 38912) (hb : s.gpr .rbp = 0x4000000000000000 - 2048)
    (h8 : s.gpr .r8 = 0x1fff) (h9 : s.gpr .r9 = 0x3ffffff) (h10 : s.gpr .r10 = 0x7fffffffff) :
    WP isa (.block vload) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 1664 224 s.mem s'.mem ∧ EConsts s'.mem base ∧
      ∀ l < 4, ∀ i < 5, lanes s' 0 l i =
        limbNat (fun k => (mq s.mem base (64 + 32 * l + 8 * k)).toNat) (2 ^ 51 - 1) i ∧
        lanes s' 0 l i < 2 ^ 52 := by
  have hE := loadB_env ha
  have e : Sym.init.run vload = some loadS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  have hmem : s'.mem = stores s base loadS.st s.mem := by rw [h.mem, hs]
  have cst : ∀ d r l, (d, r) ∈ [(KM, Reg.rax), (K19, .rcx), (KB0, .rdx), (KB1, .rbp), (EK13, .r8),
      (EK26, .r9), (EK39, .r10)] → l < 4 → (mq s'.mem base (d + 8 * l)).toNat = (s.gpr r).toNat :=
    fun d r l hd hl => by
      have t := loadT_const _ hd
      have hm := loadT_mem d (by simp only [List.mem_cons] at hd ⊢; rcases hd with h | h | h | h | h | h | h | h <;>
        simp_all)
      simp only at t
      rw [t] at hm
      rw [hmem, stores_const hm loadS_small loadS_apart hl]
  refine ⟨h.gpr, h.rd, h.wr, ?_, ⟨⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩,
    fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, fun l hl i hi => ?_⟩
  · rw [hmem]; exact stores_outside _ _ _ (by decide) _ loadS_range
  · rw [cst KM .rax l (by decide) hl, ha]; rfl
  · rw [cst K19 .rcx l (by decide) hl, hcx]; rfl
  · rw [cst KB0 .rdx l (by decide) hl, hd]; rfl
  · rw [cst KB1 .rbp l (by decide) hl, hb]; rfl
  · rw [cst EK13 .r8 l (by decide) hl, h8]; rfl
  · rw [cst EK26 .r9 l (by decide) hl, h9]; rfl
  · rw [cst EK39 .r10 l (by decide) hl, h10]; rfl
  · obtain ⟨o, b⟩ := loadS_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega) hl o
    simp only [lanes, Nat.zero_add] at e ⊢
    refine ⟨?_, by omega⟩
    rw [e, loadS_regs _ i hi l hl]
    have hw : (fun k => (envOf s).m (64 + 32 * l) k) = fun k => (mq s.mem base (64 + 32 * l + 8 * k)).toNat :=
      funext fun k => envOf_m hs _ _
    rw [hw]
    show limbNat _ (s.gpr .rax).toNat i = _
    rw [ha]; rfl

/-! ## A doubling -/

/-- What `dblA` leaves: `(X, Y, Z, X)` in `OPL`, `(X, Y, Z, Y)` in `ymm5–ymm9`. -/
theorem dblA_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) :
    WP isa (.block dblA) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base OPL 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, slotv s'.mem base OPL l i = lanes s 0 (sel4 (ord 0 1 2 0).toNat l) i ∧
        lanes s' 5 l i = lanes s 0 (sel4 (ord 0 1 2 1).toNat l) i) ∧
      (∀ r < 16, (r < 5 ∨ 11 ≤ r) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run dblA = some dblAS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.gpr, h.rd, h.wr, ?_, fun l hl i hi => ⟨?_, ?_⟩, fun r hr h1 l hl => h.keep hr hl (dblAS_keep r hr h1)⟩
  · rw [h.mem, hs]
    exact stores_outside _ _ _ (by decide) _ (by rw [dblAS_st]; decide)
  · have hm : ∀ i < 5, ((OPL + 32 * i), T.perm (.reg i) (ord 0 1 2 0).toNat) ∈ dblAS.st := by
      rw [dblAS_st]; decide
    rw [slotv, h.mem, hs, stores_mq _ _ _ _ (hm i hi) hl (by rw [dblAS_st]; decide)
      (by rw [dblAS_st]; decide)]
    simp only [T.eval, lanes, Nat.zero_add]
  · have := h.reg (xr (5 + i)) l hl
    rw [xi_xr _ (by omega), dblAS_regs i hi] at this
    simp only [lanes, Nat.zero_add, this, T.eval]

/-! ## Products, with their limbs' bound -/

theorem mulL_bound : ∀ k < 5, ∀ l < 4, (VG.Proof.X25519.X86_64.Ifma.mulL.reg k).ok
    (VG.Proof.X25519.X86_64.Ifma.mulB OPL) l = true ∧
    (VG.Proof.X25519.X86_64.Ifma.mulL.reg k).bnd (VG.Proof.X25519.X86_64.Ifma.mulB OPL) l < prodBound := by
  decide +kernel

/-- `mul4 OPL`, its limbs below `prodBound`. -/
theorem mulLB_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base)
    (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hx : ∀ l < 4, ∀ i < 5, slotv s.mem base OPL l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.mul4 OPL)) s fun s' =>
      VG.Proof.X25519.X86_64.Ifma.MulPost base OPL s s' ∧ ∀ l < 4, ∀ i < 5, lanes s' 0 l i < prodBound := by
  have hE : EnvOK s (VG.Proof.X25519.X86_64.Ifma.mulB OPL) := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
    · simp only [VG.Proof.X25519.X86_64.Ifma.mulB]
      split
      · have := hy l hl (r - 5) (by omega)
        simp only [lanes, show 5 + (r - 5) = r by omega] at this
        omega
      · exact lt64 _
    · simp only [VG.Proof.X25519.X86_64.Ifma.mulB]
      split
      · rename_i h
        obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = OPL + 32 * i :=
          ⟨(d - OPL) / 32, by simp only [OPL] at h ⊢; omega, by simp only [OPL] at h ⊢; omega⟩
        have := hx l hl i hi
        simp only [slotv] at this
        omega
      · exact lt64 _
  have e : Sym.init.run (VG.Impl.X25519.X86_64.Ifma.mul4 OPL) = some VG.Proof.X25519.X86_64.Ifma.mulL :=
    VG.Proof.X25519.X86_64.Ifma.mulS_eq OPL _
  refine WP.mono (run_ok hc e) fun s' h => ⟨⟨h.eq, by rw [h.mem, VG.Proof.X25519.X86_64.Ifma.mulL_st]; rfl,
    fun l hl i hi => ?_, fun r hr h1 h2 l hl =>
      h.keep hr hl (VG.Proof.X25519.X86_64.Ifma.mulL_keep r hr h1 h2)⟩, fun l hl i hi => ?_⟩
  · obtain ⟨o, b⟩ := VG.Proof.X25519.X86_64.Ifma.mulL_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega) hl o
    simp only [lanes, Nat.zero_add] at e ⊢
    refine ⟨?_, by omega⟩
    have hf : (fun i => (envOf s).m (OPL + 32 * i) l) = slotv s.mem base OPL l :=
      funext fun j => by rw [envOf_m hs, slotv]
    have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
    rw [e, VG.Proof.X25519.X86_64.Ifma.mulL_nat _ _ i hi, hf, hg]
  · obtain ⟨o, b⟩ := mulL_bound i hi l hl
    obtain ⟨_, be⟩ := h.out hE (by omega) hl o
    simp only [lanes, Nat.zero_add] at be ⊢
    omega

/-- `F`, limb `i`, from `(A, B, C', P)` (`x l i`). -/
def fv (x : Nat → Nat → Nat) (i : Nat) : Nat := x 2 i + x 2 i + (kbv i + x 0 i - x 1 i)

/-- `(E, G, F, E)`. -/
def op1 (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 3 i + x 3 i
  | 1 => kbv i + x 1 i - x 0 i
  | 2 => fv x i
  | _ => x 3 i + x 3 i

/-- `(F, H, G, H)`. -/
def op2 (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => fv x i
  | 1 => x 0 i + x 1 i
  | 2 => kbv i + x 1 i - x 0 i
  | _ => x 0 i + x 1 i

theorem dblB_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < prodBound) :
    WP isa (.block dblB) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = op1 (lanes s 0) l i ∧ lanes s' 0 l i < 2 ^ 63 ∧
        lanes s' 5 l i = op2 (lanes s 0) l i ∧ lanes s' 5 l i < 2 ^ 63) ∧
      (∀ r < 16, 14 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : EnvOK s dblBB := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
    · simp only [dblBB]
      split
      · have := hx l hl r (by omega); simp only [lanes, Nat.zero_add] at this; omega
      · exact lt64 _
    · simp only [dblBB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact lt64 _
    · simp only [dblBB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact Nat.zero_le _
  have e : Sym.init.run dblB = some dblBS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, dblBS_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (dblBS_keep r hr h1)⟩
  obtain ⟨o1, b1, o2, b2⟩ := dblBS_ok i hi l hl
  obtain ⟨e1, be1⟩ := h.out hE (by omega) hl o1
  obtain ⟨e2, be2⟩ := h.out hE (by omega) hl o2
  obtain ⟨n1, n2⟩ := dblBS_nat (envOf s) i hi l hl
  simp only [lanes, Nat.zero_add] at e1 e2 ⊢
  refine ⟨?_, by omega, ?_, by omega⟩
  · rw [e1, n1]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [dblOp1, op1, fv, fNat, lanes, Nat.zero_add, envOf_v, envOf_m hs,
        kb_m hk (show 0 < 4 by decide), kb_m hk (show 1 < 4 by decide)]
  · rw [e2, n2]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [dblOp2, op2, fv, fNat, lanes, Nat.zero_add, envOf_v, envOf_m hs,
        kb_m hk (show 0 < 4 by decide), kb_m hk (show 1 < 4 by decide)]

/-- What `dblC` leaves: the first operand in `OPV`. -/
theorem dblC_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s) :
    WP isa (.block dblC) s fun s' => vm s s' = s' ∧ Outside base OPV 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, slotv s'.mem base OPV l i = lanes s 0 l i) ∧
      (∀ r < 16, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run dblC = some dblCS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, ?_, fun l hl i hi => ?_, fun r hr l hl => h.keep hr hl (dblCS_keep r hr)⟩
  · rw [h.mem, hs]
    exact stores_outside _ _ _ (by decide) _ (by rw [dblCS_st]; decide)
  · have hm : ∀ i < 5, ((OPV + 32 * i), T.reg i) ∈ dblCS.st := by
      rw [dblCS_st]; decide
    rw [slotv, h.mem, hs, stores_mq _ _ _ _ (hm i hi) hl (by rw [dblCS_st]; decide) (by rw [dblCS_st]; decide)]
    simp only [T.eval, lanes, Nat.zero_add]

end VG.Proof.Ed25519.X86_64.Ifma
end

/-! Merged from `Proof.Ed25519.X86_64.Ifma.Double`. -/
section
/-!
# Ed25519 doublings with AVX512_IFMA: a doubling in the lanes

`vdbl` leaves in the lanes of `ymm0–ymm4` the point `dblPoint` of the one
there, as field elements (`fe5`).
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord mul4 carry)
open VG.Proof.X25519.X86_64.Ifma (lanes slotv CConsts carryNat fe5 fe5_congr fe5_add fe5_sub fe5_carry
  fe5_mul carryI_wp carryF_wp mul4_wp mulL mulV mulS_eq mulL_nat mulL_ok mulL_keep mulL_st mulV_nat mulV_ok
  mulV_keep mulV_st kbv vm vm_gpr vm_rd vm_wr)
open VG.Proof.X25519.X86_64 (Outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4 sel4_lt)

/-- The point in the lanes of `ymm0–ymm4`. -/
def lanePt (s : State) : Spec.Ed25519.Point :=
  ⟨fe5 (lanes s 0 0), fe5 (lanes s 0 1), fe5 (lanes s 0 2), fe5 (lanes s 0 3)⟩

/-- Limbs below `2⁶¹`, in every lane. -/
def Small (s : State) : Prop := ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61

theorem kbv_ge (i : Nat) : 2 ^ 61 ≤ kbv i := by
  simp only [kbv]; split <;> omega

theorem prodBound_le (i : Nat) : prodBound ≤ kbv i := by
  have := kbv_ge i; simp only [prodBound]; omega

theorem fe_add_sub (a b c : Spec.X25519.Fe) : a + (b - c) = a - (c - b) :=
  toZ_inj.1 (by rw [toZ_add, toZ_sub, toZ_sub, toZ_sub]; ring)

/-- `(E, G, F, E)` and `(F, H, G, H)` as field elements, from `(A, B, C', P)`. -/
theorem ops_fe (x : Nat → Nat → Nat) (hx : ∀ l < 4, ∀ i < 5, x l i < prodBound) :
    fe5 (op1 x 0) = fe5 (x 3) + fe5 (x 3) ∧ fe5 (op1 x 1) = fe5 (x 1) - fe5 (x 0) ∧
    fe5 (op1 x 2) = fe5 (x 2) + fe5 (x 2) - (fe5 (x 1) - fe5 (x 0)) ∧
    fe5 (op1 x 3) = fe5 (x 3) + fe5 (x 3) ∧
    fe5 (op2 x 0) = fe5 (x 2) + fe5 (x 2) - (fe5 (x 1) - fe5 (x 0)) ∧
    fe5 (op2 x 1) = fe5 (x 0) + fe5 (x 1) ∧ fe5 (op2 x 2) = fe5 (x 1) - fe5 (x 0) ∧
    fe5 (op2 x 3) = fe5 (x 0) + fe5 (x 1) := by
  have g : fe5 (fun i => kbv i + x 1 i - x 0 i) = fe5 (x 1) - fe5 (x 0) :=
    fe5_sub (fun i hi => by have := hx 0 (by decide) i hi; have := prodBound_le i; omega)
      (fun i hi => by have := hx 0 (by decide) i hi; have := prodBound_le i; omega)
  have f : fe5 (fv x) = fe5 (x 2) + fe5 (x 2) - (fe5 (x 1) - fe5 (x 0)) := by
    rw [fe5_add (z := fv x) (x := fun i => x 2 i + x 2 i) (y := fun i => kbv i + x 0 i - x 1 i)
      (fun i _ => rfl),
      fe5_add (z := fun i => x 2 i + x 2 i) (x := x 2) (y := x 2) (fun i _ => rfl),
      fe5_sub (z := fun i => kbv i + x 0 i - x 1 i) (x := x 0) (y := x 1) (fun i hi => by have := hx 1 (by decide) i hi; have := prodBound_le i; omega)
        (fun i hi => by have := hx 1 (by decide) i hi; have := prodBound_le i; omega), fe_add_sub]
  have e : fe5 (fun i => x 3 i + x 3 i) = fe5 (x 3) + fe5 (x 3) := fe5_add fun _ _ => rfl
  have h : fe5 (fun i => x 0 i + x 1 i) = fe5 (x 0) + fe5 (x 1) := fe5_add fun _ _ => rfl
  exact ⟨e, g, f, e, f, h, g, h⟩

theorem lanes_keep {s t : State} {r : Nat} (hr : r + 5 ≤ 16)
    (h : ∀ q < 16, r ≤ q → q < r + 5 → ∀ l < 4, qw t (xr q) l = qw s (xr q) l) :
    ∀ l < 4, ∀ i < 5, lanes t r l i = lanes s r l i := fun l hl i hi => by
  simp only [lanes]; rw [h (r + i) (by omega) (by omega) (by omega) l hl]

/-- `vdbl`: the lanes doubled, with `T`. -/
theorem vdbl_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : EConsts s.mem base) (hx : Small s) :
    WP isa (.block vdbl) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 1024 320 s.mem s'.mem ∧ Small s' ∧ lanePt s' = dblPoint (lanePt s) := by
  have hcc : CConsts s.mem base := hk.toCConsts
  simp only [vdbl, List.append_assoc]
  -- the point carried
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs hc hcc fun l hl i hi => by have := hx l hl i hi; omega)
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ : s₁.gpr .rdi = base := by rw [vm_gpr v₁]; exact hs
  have hc₁ : VG.Proof.X25519.X86_64.Ifma.Ctx s₁ := by
    intro d hd; rw [vm_gpr v₁, vm_wr v₁]; exact hc d hd
  have p₁ : ∀ l < 4, fe5 (lanes s₁ 0 l) = fe5 (lanes s 0 l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₁ l hl i hi).1), fe5_carry _ (by have := hx l hl 4 (by decide); omega)]
  -- the first operands
  rw [WP.block_append_iff]
  refine WP.mono (dblA_wp hs₁ hc₁) fun s₂ ⟨g₂, rd₂, wr₂, o₂, u₂, k₂⟩ => ?_
  have hs₂ : s₂.gpr .rdi = base := by rw [g₂]; exact hs₁
  have hc₂ : VG.Proof.X25519.X86_64.Ifma.Ctx s₂ := by intro d hd; rw [g₂, wr₂]; exact hc₁ d hd
  -- the first product: `(A, B, C', P)`
  rw [WP.block_append_iff]
  refine WP.mono (mulLB_wp hs₂ hc₂
    (fun l hl i hi => by rw [(u₂ l hl i hi).1]; exact (u₁ _ (sel4_lt _ _) i hi).2)
    (fun l hl i hi => by rw [(u₂ l hl i hi).2]; exact (u₁ _ (sel4_lt _ _) i hi).2))
    fun s₄ ⟨⟨v₄, m₄, u₃, _⟩, b₄⟩ => ?_
  have p₄ : ∀ l < 4, fe5 (lanes s₄ 0 l) =
      fe5 (lanes s 0 (sel4 (ord 0 1 2 0).toNat l)) * fe5 (lanes s 0 (sel4 (ord 0 1 2 1).toNat l)) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₃ l hl i hi).1),
        fe5_mul (fun i hi => by rw [(u₂ l hl i hi).1]; exact (u₁ _ (sel4_lt _ _) i hi).2)
          (fun i hi => by rw [(u₂ l hl i hi).2]; exact (u₁ _ (sel4_lt _ _) i hi).2),
        ← p₁ _ (sel4_lt _ _), ← p₁ _ (sel4_lt _ _)]
      exact congrArg₂ (· * ·) (fe5_congr fun i hi => (u₂ l hl i hi).1)
        (fe5_congr fun i hi => (u₂ l hl i hi).2)
  have hs₄ : s₄.gpr .rdi = base := by rw [vm_gpr v₄]; exact hs₂
  have hc₄ : VG.Proof.X25519.X86_64.Ifma.Ctx s₄ := by intro d hd; rw [vm_gpr v₄, vm_wr v₄]; exact hc₂ d hd
  have mo₃ : Outside base 1024 320 s.mem s₄.mem := by
    rw [m₄, ← m₁]; exact o₂.mono (by decide) (by decide)
  have hk₄ : EConsts s₄.mem base := hk.outside mo₃
  -- the second operands
  rw [WP.block_append_iff]
  refine WP.mono (dblB_wp hs₄ hc₄ hk₄.toCConsts b₄)
    fun s₅ ⟨v₅, m₅, u₅, k₅⟩ => ?_
  have hs₅ : s₅.gpr .rdi = base := by rw [vm_gpr v₅]; exact hs₄
  have hc₅ : VG.Proof.X25519.X86_64.Ifma.Ctx s₅ := by intro d hd; rw [vm_gpr v₅, vm_wr v₅]; exact hc₄ d hd
  have hk₅ : EConsts s₅.mem base := by rw [m₅]; exact hk₄
  rw [WP.block_append_iff]
  refine WP.mono (carryF_wp hs₅ hc₅ hk₅.toCConsts fun l hl i hi => (u₅ l hl i hi).2.2.2)
    fun s₆ ⟨v₆, m₆, u₆, k₆⟩ => ?_
  have hs₆ : s₆.gpr .rdi = base := by rw [vm_gpr v₆]; exact hs₅
  have hc₆ : VG.Proof.X25519.X86_64.Ifma.Ctx s₆ := by intro d hd; rw [vm_gpr v₆, vm_wr v₆]; exact hc₅ d hd
  have hk₆ : EConsts s₆.mem base := by rw [m₆]; exact hk₅
  have l₆ := lanes_keep (r := 0) (s := s₅) (t := s₆) (by decide) fun q hq h1 h2 l hl =>
    k₆ q hq (by omega) (by omega) l hl
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₆ hc₆ hk₆.toCConsts fun l hl i hi => by
      rw [l₆ l hl i hi]; exact (u₅ l hl i hi).2.1) fun s₇ ⟨v₇, m₇, u₇, k₇⟩ => ?_
  have hs₇ : s₇.gpr .rdi = base := by rw [vm_gpr v₇]; exact hs₆
  have hc₇ : VG.Proof.X25519.X86_64.Ifma.Ctx s₇ := by intro d hd; rw [vm_gpr v₇, vm_wr v₇]; exact hc₆ d hd
  have l₇ := lanes_keep (r := 5) (s := s₆) (t := s₇) (by decide) fun q hq h1 h2 l hl =>
    k₇ q hq (by omega) (by omega) l hl
  -- the first operand to `OPV`
  rw [WP.block_append_iff]
  refine WP.mono (dblC_wp hs₇ hc₇) fun s₈ ⟨v₈, o₈, u₈, k₈⟩ => ?_
  have hs₈ : s₈.gpr .rdi = base := by rw [vm_gpr v₈]; exact hs₇
  have hc₈ : VG.Proof.X25519.X86_64.Ifma.Ctx s₈ := by intro d hd; rw [vm_gpr v₈, vm_wr v₈]; exact hc₇ d hd
  have l₈ := lanes_keep (r := 5) (s := s₇) (t := s₈) (by decide) fun q hq _ _ l hl => k₈ q hq l hl
  -- the second product
  refine WP.mono (mul4_wp (by decide) (mulS_eq OPV _) (mulV_nat) mulV_ok mulV_keep mulV_st hs₈ hc₈
    (fun l hl i hi => by rw [u₈ l hl i hi]; exact (u₇ l hl i hi).2)
    (fun l hl i hi => by rw [l₈ l hl i hi, l₇ l hl i hi]; exact (u₆ l hl i hi).2))
    fun s₉ ⟨v₉, m₉, u₉, _⟩ => ?_
  refine ⟨by rw [vm_gpr v₉, vm_gpr v₈, vm_gpr v₇, vm_gpr v₆, vm_gpr v₅, vm_gpr v₄, g₂, vm_gpr v₁],
    by rw [vm_rd v₉, vm_rd v₈, vm_rd v₇, vm_rd v₆, vm_rd v₅, vm_rd v₄, rd₂, vm_rd v₁],
    by rw [vm_wr v₉, vm_wr v₈, vm_wr v₇, vm_wr v₆, vm_wr v₅, vm_wr v₄, wr₂, vm_wr v₁], ?_,
    fun l hl i hi => (u₉ l hl i hi).2, ?_⟩
  · rw [m₇, m₆, m₅] at o₈
    rw [m₉]; exact mo₃.trans (o₈.mono (by decide) (by decide))
  have p₉ : ∀ l < 4, fe5 (lanes s₉ 0 l) = fe5 (op1 (lanes s₄ 0) l) * fe5 (op2 (lanes s₄ 0) l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₉ l hl i hi).1),
      fe5_mul (fun i hi => by rw [u₈ l hl i hi]; exact (u₇ l hl i hi).2)
        (fun i hi => by rw [l₈ l hl i hi, l₇ l hl i hi]; exact (u₆ l hl i hi).2),
      fe5_congr (fun i hi => u₈ l hl i hi), fe5_congr (fun i hi => (u₇ l hl i hi).1),
      fe5_carry _ (by rw [l₆ l hl 4 (by decide)]; have := (u₅ l hl 4 (by decide)).2.1; omega),
      fe5_congr (fun i hi => (l₆ l hl i hi).trans (u₅ l hl i hi).1),
      fe5_congr (fun i hi => (l₈ l hl i hi).trans (l₇ l hl i hi)),
      fe5_congr (fun i hi => (u₆ l hl i hi).1),
      fe5_carry _ (by have := (u₅ l hl 4 (by decide)).2.2.2; omega),
      fe5_congr (fun i hi => (u₅ l hl i hi).2.2.1)]
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := ops_fe (lanes s₄ 0) b₄
  have hA : fe5 (lanes s₄ 0 0) = fe5 (lanes s 0 0) * fe5 (lanes s 0 0) := by
    rw [p₄ 0 (by decide)]; rfl
  have hB : fe5 (lanes s₄ 0 1) = fe5 (lanes s 0 1) * fe5 (lanes s 0 1) := by
    rw [p₄ 1 (by decide)]; rfl
  have hC : fe5 (lanes s₄ 0 2) = fe5 (lanes s 0 2) * fe5 (lanes s 0 2) := by
    rw [p₄ 2 (by decide)]; rfl
  have hP : fe5 (lanes s₄ 0 3) = fe5 (lanes s 0 0) * fe5 (lanes s 0 1) := by
    rw [p₄ 3 (by decide)]; rfl
  simp only [lanePt, dblPoint]
  rw [p₉ 0 (by decide), p₉ 1 (by decide), p₉ 2 (by decide), p₉ 3 (by decide), a0, a1, a2, a3, b0, b1, b2, b3,
    hA, hB, hC, hP]

end VG.Proof.Ed25519.X86_64.Ifma
end

/-!
# Ed25519 doublings with AVX512_IFMA: four of them

`Ifma.double4` loads slots 0–3 into the lanes, doubles them four times
(`vdbl_wp`) and stores them back: the point in slots 0–3 then represents `16a`
if it represented `a`.
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519 VG.Proof.Ed25519.X86_64 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord mul4 carry)
open VG.Proof.X25519.X86_64.Ifma (Sym T Env Bnds EnvOK symOf symOf_eq lanes slotv CConsts carryNat fe5 fe5_congr
  fe5_carry carryI_wp vm vm_gpr vm_rd vm_wr envOK_of envOf envOf_m lt64 run_ok stores_mq stores_outside nat_ok
  mq mq_eq_word packW packW_val carryNat_le limbNat limbNat_lv consts_wp cregs)
open VG.Proof.X25519.X86_64 (Outside word val4 fe F clob Keeps off)
open VG.Impl.X25519.X86_64 (sc)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## Storing -/

theorem packB_env {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hk : EConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i ≤ 2 ^ 51 + 18) : EnvOK s packB := by
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

/-- `vstore`: each lane as four words, in slots 0–3. -/
theorem vstore_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : EConsts s.mem base) (hy : Small s) :
    WP isa (.block vstore) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 64 128 s.mem s'.mem ∧ ∀ m < 4, F s'.mem base (64 + 32 * m) = fe5 (lanes s 0 m) := by
  rw [vstore_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (carryI_wp hs hc hk.toCConsts fun l hl i hi => by have := hy l hl i hi; omega)
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ : s₁.gpr .rdi = base := by rw [vm_gpr v₁]; exact hs
  have hc₁ : VG.Proof.X25519.X86_64.Ifma.Ctx s₁ := by intro d hd; rw [vm_gpr v₁, vm_wr v₁]; exact hc d hd
  have hk₁ : EConsts s₁.mem base := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁ hc₁ hk₁.toCConsts fun l hl i hi => by have := (u₁ l hl i hi).2; omega)
    fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  have hs₂ : s₂.gpr .rdi = base := by rw [vm_gpr v₂]; exact hs₁
  have hc₂ : VG.Proof.X25519.X86_64.Ifma.Ctx s₂ := by intro d hd; rw [vm_gpr v₂, vm_wr v₂]; exact hc₁ d hd
  have hk₂ : EConsts s₂.mem base := by rw [m₂]; exact hk₁
  have b₂ : ∀ l < 4, ∀ i < 5, lanes s₂ 0 l i ≤ 2 ^ 51 + 18 := fun l hl i hi => by
    rw [(u₂ l hl i hi).1]; exact carryNat_le _ (fun j hj => (u₁ l hl j hj).2) i hi
  have hE := packB_env hs₂ hk₂ b₂
  have e : Sym.init.run vpackE = some packS := symOf_eq _ _
  refine WP.mono (run_ok hc₂ e) fun s₃ h => ?_
  have v₃ : vm s₂ s₃ = s₃ := h.eq
  refine ⟨(vm_gpr v₃).trans ((vm_gpr v₂).trans (vm_gpr v₁)), (vm_rd v₃).trans ((vm_rd v₂).trans (vm_rd v₁)),
    (vm_wr v₃).trans ((vm_wr v₂).trans (vm_wr v₁)), ?_, fun m hm => ?_⟩
  · rw [h.mem, hs₂, m₂, m₁]
    exact stores_outside _ _ _ (by decide) _ (by decide +kernel)
  · have w : ∀ j < 4, (word s₃.mem base (64 + 32 * m + 8 * j)).toNat =
        packW (fun i => lanes s₂ 0 m i) (2 ^ 51 - 1) (2 ^ 13 - 1) (2 ^ 26 - 1) (2 ^ 39 - 1) j := fun j hj => by
      rw [← mq_eq_word, h.mem, hs₂, stores_mq _ _ _ _ (packT_mem m hm) hj packS_small packS_apart,
        (nat_ok hE _ hj (packT_ok m hm j hj)).1, packT_nat _ m hm j hj, envOf_m hs₂, envOf_m hs₂,
        envOf_m hs₂, envOf_m hs₂, hk₂.km m hm, hk₂.k13 m hm, hk₂.k26 m hm, hk₂.k39 m hm]
      rfl
    have fe' : fe s₃.mem base (64 + 32 * m) = VG.Proof.X25519.X86_64.Ifma.lv (lanes s₂ 0 m) := by
      simp only [fe, val4]
      have w0 := w 0 (by decide); have w1 := w 1 (by decide); have w2 := w 2 (by decide)
      have w3 := w 3 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at w0 w1 w2 w3
      rw [w0, show 64 + 32 * m + 16 = 64 + 32 * m + 8 * 2 by rfl, w2, w1, w3]
      exact packW_val _ (b₂ m hm)
    show VG.Proof.X25519.toFe _ = _
    rw [fe']
    rw [show VG.Proof.X25519.toFe (VG.Proof.X25519.X86_64.Ifma.lv (lanes s₂ 0 m)) = fe5 (lanes s₂ 0 m) from rfl,
      fe5_congr (fun i hi => (u₂ m hm i hi).1), fe5_carry _ (by have := (u₁ m hm 4 (by decide)).2; omega),
      fe5_congr (fun i hi => (u₁ m hm i hi).1), fe5_carry _ (by have := hy m hm 4 (by decide); omega)]

/-! ## Before the loop -/

theorem fe5_load (m : Mem) (base : Addr) (l : Nat) :
    fe5 (limbNat (fun k => (mq m base (64 + 32 * l + 8 * k)).toNat) (2 ^ 51 - 1)) = F m base (64 + 32 * l) := by
  show VG.Proof.X25519.toFe _ = VG.Proof.X25519.toFe _
  rw [limbNat_lv _ (fun k _ => BitVec.isLt _)]
  rfl

theorem ctx_of {s : State} {base : Addr} (hs : Scratch s base) : VG.Proof.X25519.X86_64.Ifma.Ctx s :=
  fun d hd => by
    rw [hs.rdi]
    exact ⟨_, hs.wr, Offset.contains_base base (show d + 32 ≤ 8192 by omega) (by omega)⟩

theorem mov32_wp (s : State) (r : Reg) (n : BitVec 32) :
    WP isa (.block [.mov32 r (.imm n)]) s fun t => t.gpr r = n.setWidth 64 ∧
      (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ∀ x l, qw t x l = qw s x l := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q hq => by simp only [hq, ite_false], rfl, rfl, rfl, fun _ _ => rfl⟩

theorem dec_wp (s : State) (n : Nat) (hn : n < 16) (hc : s.gpr .rsi = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rsi (.imm 1)]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧ Keeps [.rsi] s t ∧
      ∀ x l, qw t x l = qw s x l := by
  have e : BitVec.ofNat 64 (n + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    hc, point_counter_zero n hn, e, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem lanes_qw {s t : State} (h : ∀ x l, qw t x l = qw s x l) (r : Nat) : lanes t r = lanes s r := by
  funext l i; simp only [lanes, h]

theorem lanePt_qw {s t : State} (h : ∀ x l, qw t x l = qw s x l) : lanePt t = lanePt s := by
  simp only [lanePt, lanes_qw h]

theorem cregs_clob : ∀ r ∈ cregs, r ∈ clob := by decide

theorem prep_wp {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload ++ ([.mov32 .rsi (.imm 4)] : List Instr))) s fun t =>
      t.gpr .rdi = base ∧ t.gpr .rsi = BitVec.ofNat 64 4 ∧ (∀ r, r ∉ clob → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base 1664 224 s.mem t.mem ∧ EConsts t.mem base ∧ Small t ∧
      lanePt t = point (env s.mem base) 0 1 2 3 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (consts_wp s) fun s₁ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₁, m₁, rd₁, wr₁, _, _, _⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (vload_wp hs₁.rdi (ctx_of hs₁) ha hc hd hb h8 h9 h10) fun s₂ ⟨g₂, rd₂, wr₂, o₂, k₂, u₂⟩ => ?_
  refine WP.mono (mov32_wp s₂ .rsi 4) fun t ⟨tr, tg, tm, trd, twr, tq⟩ => ?_
  have hl := lanes_qw tq 0
  refine ⟨by rw [tg _ (by decide), g₂]; exact hs₁.rdi, tr, fun r hr hr' => ?_, by rw [trd, rd₂, rd₁],
    by rw [twr, wr₂, wr₁], by rw [tm, ← m₁]; exact o₂, by rw [tm]; exact k₂,
    fun l hl' i hi => by rw [hl]; have := (u₂ l hl' i hi).2; omega, ?_⟩
  · rw [tg _ hr', g₂, g₁ r (fun h => hr (cregs_clob r h))]
  · have e : ∀ l (hl' : l < 4), fe5 (lanes t 0 l) = env s.mem base ⟨l, by omega⟩ := fun l hl' => by
      rw [hl, fe5_congr (fun i hi => (u₂ l hl' i hi).1), fe5_load, m₁]; rfl
    simp only [lanePt, point]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    rfl

/-! ## MXCSR -/

/-- What the MXCSR blocks keep. -/
structure MxKeep (base : Addr) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base EMX 8 s.mem t.mem
  xmm : t.xmm = s.xmm
  ymm : t.ymmHi = s.ymmHi

theorem MxKeep.qw_eq {base : Addr} {s t : State} (h : MxKeep base s t) : ∀ x l, qw t x l = qw s x l :=
  fun _ _ => by simp only [qw, State.lane, h.xmm, h.ymm]

theorem mx_in {s : State} {base : Addr} (hs : Scratch s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (off base d) n := ⟨_, hs.wr, Offset.contains_base base hd (by omega)⟩

theorem mx_in' {s : State} {base : Addr} (hs : Scratch s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base base hd (by omega)⟩

theorem outside_emx (m : Mem) (base : Addr) {d : Nat} (hd : EMX ≤ d ∧ d + 4 ≤ EMX + 8) (v : BitVec 32) :
    Outside base EMX 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by simp only [EMX] at hd ⊢; omega)]
  simp only [VG.Proof.X25519.X86_64.ofs] at hx
  simp only [EMX] at hd hx ⊢
  omega

/-- The save: MXCSR (its reserved bits cleared) into `r11`. -/
theorem save_wp {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block [.stmxcsr (sc EMX), .mov32 .r11 (.mem (sc EMX)), .alu32 .and .r11 (.imm 0xFFFF)]) s
      fun t => (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧
        (t.gpr .r11).setWidth 32 = s.mxcsr &&& 0xFFFF ∧ MxKeep base s t := by
  apply WP.of_runBlock
  have h1 := mx_in hs (show EMX + 4 ≤ 8192 by decide)
  have h2 := mx_in' hs (show EMX + 4 ≤ 8192 by decide)
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, readSrc32,
    VG.Proof.X25519.X86_64.ea_sc, hs.rdi, h1, h2, ite_true, Option.bind_some, Option.map_some,
    Mem.readW_writeW_self32, execAlu32, State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, ?_, ⟨rfl, rfl, outside_emx _ _ (by simp only [EMX]; omega) _, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · simp only [RegUpd.gpr_setReg_self, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide),
      BitVec.setWidth_eq]

/-- `0x1FBF` into MXCSR, through `[EMX + 4]` and `rax`. -/
theorem load_wp {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (EMX + 4)) .rax, .ldmxcsr (sc (EMX + 4)),
      .lfence]) s fun t => (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ MxKeep base s t := by
  apply WP.of_runBlock
  have h1 := mx_in hs (show EMX + 4 + 4 ≤ 8192 by decide)
  have h2 := mx_in' hs (show EMX + 4 + 4 ≤ 8192 by decide)
  have e : (BitVec.setWidth 32 (BitVec.setWidth 64 (0x1FBF : BitVec 32))).extractLsb' 16 16 = 0 := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, readSrc32,
    VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.rd_setReg, hs.rdi, h1, h2,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Mem.readW_writeW_self32,
    State.setReg32, e, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, ⟨rfl, rfl, outside_emx _ _ (by simp only [EMX]; omega) _, rfl, rfl⟩⟩
  simp only [hr, ite_false]

/-- MXCSR back from `r11`, through `[EMX]`. -/
theorem restore_wp {s : State} {base : Addr} (hs : Scratch s base)
    (h11 : ((s.gpr .r11).setWidth 32).extractLsb' 16 16 = 0) :
    WP isa (.block [.store32 (sc EMX) .r11, .ldmxcsr (sc EMX)]) s
      fun t => t.gpr = s.gpr ∧ MxKeep base s t := by
  apply WP.of_runBlock
  have h1 := mx_in hs (show EMX + 4 ≤ 8192 by decide)
  have h2 := mx_in' hs (show EMX + 4 ≤ 8192 by decide)
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32,
    VG.Proof.X25519.X86_64.ea_sc, hs.rdi, h1, h2, ite_true, Option.bind_some, Mem.readW_writeW_self32,
    h11, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨rfl, rfl, outside_emx _ _ (by simp only [EMX]; omega) _, rfl, rfl⟩⟩

theorem and_ffff (v : BitVec 32) : (v &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp

theorem lfence_wp (s : State) : WP isa (.block [.lfence]) s fun t => t = s := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']

/-- The constants are kept by the MXCSR blocks. -/
theorem EConsts.outsideMx {m m' : Mem} {base : Addr} (hk : EConsts m base)
    (h : Outside base EMX 8 m m') : EConsts m' base := by
  have w : ∀ d, 1664 ≤ d → d + 8 ≤ 4096 → mq m' base d = mq m base d := fun d h1 h2 => by
    rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
    exact h.word (by simp only [EMX]; omega) (by omega)
  refine ⟨⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, fun l hl => ?_,
    fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [w _ (by simp only [EK13]; omega) (by simp only [EK13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [EK26]; omega) (by simp only [EK26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [EK39]; omega) (by simp only [EK39]; omega)]; exact hk.k39 l hl

/-! ## Four doublings -/

/-- The loop's invariant, with `n` doublings left. -/
structure LoopInv (s : State) (base : Addr) (a : EPoint dZ) (n : Nat) (t : State) : Prop where
  pos : 0 < n
  le : n ≤ 4
  rdi : t.gpr .rdi = base
  rsi : t.gpr .rsi = BitVec.ofNat 64 n
  gpr : ∀ r, r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 1024 864 s.mem t.mem
  consts : EConsts t.mem base
  small : Small t
  rep : Rep (lanePt t) ((2 ^ (4 - n) : Nat) • a)

theorem LoopInv.ctx {s : State} {base : Addr} {a : EPoint dZ} {n : Nat} {t : State} (hs : Scratch s base)
    (h : LoopInv s base a n t) : VG.Proof.X25519.X86_64.Ifma.Ctx t :=
  ctx_of ⟨h.rdi, by rw [h.wr]; exact hs.wr, hs.nowrap⟩

theorem double4_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scratch s base)
    (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa VG.Impl.Ed25519.X86_64.Ifma.double4 s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : VG.Impl.Ed25519.X86_64.Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧
      (∀ r, r ∉ clob → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 64 1824 s.mem t.mem := by
  rw [VG.Impl.Ed25519.X86_64.Ifma.double4, withMx]
  refine WP.seq (WP.mono (prep_wp hs) fun s₁ ⟨r₁, c₁, g₁, rd₁, wr₁, o₁, k₁, sm₁, p₁⟩ => ?_)
  have hs₁ : Scratch s₁ base := ⟨r₁, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (save_wp hs₁) fun s₂ ⟨g₂, r11₂, k₂⟩ => ?_)
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂ _ (by decide)]; exact r₁, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  refine WP.seq (WP.seq (WP.mono (load_wp hs₂) fun s₃ ⟨g₃, k₃⟩ => ?_))
  have hs₃ : Scratch s₃ base := ⟨by rw [g₃ _ (by decide)]; exact hs₂.rdi, by rw [k₃.wr]; exact hs₂.wr, hs.nowrap⟩
  have q₃ : ∀ x l, qw s₃ x l = qw s₁ x l := fun x l => by rw [k₃.qw_eq, k₂.qw_eq]
  have o₃ : Outside base 1024 864 s.mem s₃.mem :=
    ((o₁.mono (by decide) (by decide)).trans (k₂.mem.mono (by decide) (by decide))).trans
      (k₃.mem.mono (by decide) (by decide))
  refine WP.seq (WP.seq ?_)
  refine WP.loop (LoopInv s₃ base a) (fun n t h => ?_) 4 s₃
    ⟨by decide, by decide, hs₃.rdi, by rw [g₃ _ (by decide), g₂ _ (by decide)]; exact c₁, fun _ _ => rfl,
      rfl, rfl, Outside.refl _ _ _ _, (k₁.outsideMx k₂.mem).outsideMx k₃.mem,
      fun l hl i hi => by rw [lanes_qw q₃]; exact sm₁ l hl i hi, by rw [lanePt_qw q₃, p₁]; simpa using ha⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.pos; omega : n ≠ 0)
  rw [WP.block_append_iff]
  refine WP.mono (vdbl_wp h.rdi (h.ctx hs₃) h.consts h.small) fun u ⟨ug, urd, uwr, uo, usm, up⟩ => ?_
  refine WP.mono (dec_wp u k (by have := h.le; omega) (by rw [ug]; exact h.rsi)) fun w ⟨wc, wz, kw, wq⟩ => ?_
  have wr' : w.gpr .rdi = base := by rw [kw.1 _ (by decide), ug]; exact h.rdi
  have wg : ∀ r, r ≠ .rsi → w.gpr r = s₃.gpr r := fun r hr' => by
    rw [kw.1 _ (by simpa using hr'), ug]; exact h.gpr r hr'
  have wrd : w.rd = s₃.rd := by rw [kw.2.2.1, urd]; exact h.rd
  have wwr : w.wr = s₃.wr := by rw [kw.2.2.2, uwr]; exact h.wr
  have wm : Outside base 1024 864 s₃.mem w.mem := by
    rw [kw.2.1]; exact h.mem.trans (uo.mono (by decide) (by decide))
  have wk : EConsts w.mem base := by rw [kw.2.1]; exact h.consts.outside uo
  have wsm : Small w := by intro l hl i hi; rw [lanes_qw wq]; exact usm l hl i hi
  have wp : Rep (lanePt w) ((2 ^ (4 - k) : Nat) • a) := by
    rw [lanePt_qw wq, up, show 4 - k = (4 - (k + 1)) + 1 by have := h.le; omega, pow_succ, mul_nsmul,
      two_nsmul]
    exact dblPoint_rep h.rep.proj
  by_cases hk : k = 0
  · subst hk
    refine Or.inl ⟨by simp only [eval, wz, decide_true, Option.map_some, Bool.not_true], ?_⟩
    have hsw : Scratch w base := ⟨wr', by rw [wwr]; exact hs₃.wr, hs.nowrap⟩
    refine WP.mono (vstore_wp wr' (ctx_of hsw) wk wsm) fun t₀ ⟨tg, trd, twr, tou, tf⟩ => ?_
    refine WP.mono (lfence_wp t₀) fun t₁ e₁ => ?_
    subst e₁
    have hs₀ : Scratch t₁ base := ⟨by rw [tg]; exact wr', by rw [twr]; exact hsw.wr, hs.nowrap⟩
    have r11 : t₁.gpr .r11 = s₂.gpr .r11 := by rw [tg, wg _ (by decide), g₃ _ (by decide)]
    refine WP.mono (restore_wp hs₀ (by rw [r11, r11₂]; exact and_ffff _)) fun t ⟨g₈, k₈⟩ => ?_
    have pt : point (env t.mem base) 0 1 2 3 = lanePt w := by
      simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
      rw [← tf 0 (by decide), ← tf 1 (by decide), ← tf 2 (by decide), ← tf 3 (by decide),
        Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide)),
        Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide))]
      rfl
    have big : Outside base 1024 864 s.mem w.mem := o₃.trans wm
    refine ⟨by rw [pt]; exact wp, fun i hi => ?_, fun r hr hr' => ?_, by rw [k₈.rd, trd, wrd, k₃.rd, k₂.rd, rd₁],
      by rw [k₈.wr, twr, wwr, k₃.wr, k₂.wr, wr₁],
      ((big.mono (by decide) (by decide)).trans (tou.mono (by decide) (by decide))).trans
        (k₈.mem.mono (by decide) (by decide))⟩
    · have := i.isLt
      simp only [env, VG.Impl.Ed25519.X86_64.offset]
      rw [Outside_F k₈.mem (by omega) (Or.inl (by simp only [EMX]; omega)), Outside_F tou (by omega) (Or.inr (by omega)),
        Outside_F big (by omega) (Or.inl (by omega))]
    · have hra : r ≠ .rax := fun e => hr (e ▸ by decide)
      have hr11 : r ≠ .r11 := fun e => hr (e ▸ by decide)
      rw [g₈, tg, wg r hr', g₃ r hra, g₂ r hr11, g₁ r hr hr']
  · refine Or.inr ⟨by simp only [eval, wz, decide_eq_false hk, Option.map_some, Bool.not_false],
      k, by omega, by omega, by have := h.le; omega, wr', wc, wg, wrd, wwr, wm, wk, wsm, wp⟩

end VG.Proof.Ed25519.X86_64.Ifma
