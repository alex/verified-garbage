import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Stage

/-!
# Ed25519 doublings with AVX512_IFMA: the blocks as facts about states

Untrusted: everything here is checked by Lean. Each vector block of
`Ifma.double4` but X25519's products and carries: the limbs it leaves in
registers and slots (`lanes`, `slotv`), as numbers, from those it starts
with, and what it keeps.
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
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 52) :
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
