import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Stage
import VerifiedGarbage.Proof.X25519.X86_64.Small

/-!
# X25519 on x86-64 with AVX512_IFMA: the blocks of an iteration

Each block of `vstep` as a fact about states: the limbs it leaves in registers
and slots (`lanes`, `slotv`), as numbers, from those it starts with, and what
it keeps.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw sel4)

theorem xi_xr : ∀ r < 16, xi (xr r) = r := by decide

/-- Limb `i` of lane `l` of the registers from `r` up. -/
def lanes (s : State) (r l i : Nat) : Nat := (qw s (xr (r + i)) l).toNat

/-- Limb `i` of lane `l` of the slot at `d`. -/
def slotv (m : Mem) (base : Addr) (d l i : Nat) : Nat := (mq m base (d + 32 * i + 8 * l)).toNat

/-- The constants of the working space, with `x₁`'s limbs. -/
structure Consts (m : Mem) (base : Addr) (x1 : Nat → Nat) : Prop where
  km : ∀ l < 4, (mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048
  a24 : ∀ i < 5, ∀ l < 4, slotv m base KA24 l i = if i = 0 ∧ l = 3 then 121665 else 0
  kx1 : ∀ i < 5, ∀ l < 4, slotv m base KX1 l i = if l = 3 then x1 i else if i = 0 ∧ l ≠ 1 then 1 else 0
  x1 : ∀ i < 5, x1 i < 2 ^ 52
  k13 : ∀ l < 4, (mq m base (K13 + 8 * l)).toNat = 2 ^ 13 - 1
  k26 : ∀ l < 4, (mq m base (K26 + 8 * l)).toNat = 2 ^ 26 - 1
  k39 : ∀ l < 4, (mq m base (K39 + 8 * l)).toNat = 2 ^ 39 - 1

/-- The constants the carries and the differences read. -/
structure CConsts (m : Mem) (base : Addr) : Prop where
  km : ∀ l < 4, (mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048

theorem Consts.c {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1) : CConsts m base :=
  ⟨hk.km, hk.k19, hk.kb0, hk.kb1⟩

theorem envOf_m {s : State} {base : Addr} (hs : s.gpr .rdi = base) (d l : Nat) :
    (envOf s).m d l = (mq s.mem base (d + 8 * l)).toNat := by
  simp only [envOf, mq, hs]

theorem envOf_v (s : State) (r l : Nat) : (envOf s).v r l = (qw s (xr r) l).toNat := rfl

/-- The environment's bounds, from the registers and memory. -/
theorem envOK_of {s : State} {base : Addr} (hs : s.gpr .rdi = base) {B : Bnds}
    (hv : ∀ r l, l < 4 → (qw s (xr r) l).toNat ≤ B.v r) (hg : ∀ g, B.g g = 2 ^ 64 - 1)
    (hm : ∀ d l, l < 4 → (mq s.mem base (d + 8 * l)).toNat ≤ B.m d)
    (hml : ∀ d l, l < 4 → B.ml d ≤ (mq s.mem base (d + 8 * l)).toNat) : EnvOK s B :=
  ⟨hv, fun g => by rw [hg]; exact Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun d k hk => by have := hm d k hk; simpa only [mq, hs] using this,
    fun d k hk => by have := hml d k hk; simpa only [mq, hs] using this⟩

theorem lt64 (x : BitVec 64) : x.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt x.isLt

/-- What a block run symbolically leaves in a register. -/
theorem SRel.out {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r l : Nat}
    (hr : r < 16) (hl : l < 4) (ho : (σ.reg r).ok B l = true) :
    (qw s (xr r) l).toNat = (σ.reg r).nat (envOf s₀) l ∧ (qw s (xr r) l).toNat ≤ (σ.reg r).bnd B l := by
  have := h.nat hE (r := xr r) hl (by rw [xi_xr r hr]; exact ho)
  rwa [xi_xr r hr] at this

theorem SRel.keep {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {r l : Nat} (hr : r < 16) (hl : l < 4)
    (hk : σ.reg r = .reg r) : qw s (xr r) l = qw s₀ (xr r) l := by
  rw [h.reg _ l hl, xi_xr r hr, hk]; rfl

/-! ## Carries -/

theorem kx1_le {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1) {i l : Nat} (hi : i < 5)
    (hl : l < 4) : slotv m base KX1 l i < 2 ^ 52 := by
  rw [hk.kx1 i hi l hl]; have := hk.x1 i hi; split <;> [omega; split <;> omega]

/-- What `carry r` leaves: limbs `r0` to `r0 + 4` carried. -/
def CarryPost (r0 : Nat) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' r0 l i = carryNat (2 ^ 51 - 1) 19 (lanes s r0 l) i ∧
      lanes s' r0 l i < 2 ^ 52) ∧
    (∀ r < 16, ¬ (r0 ≤ r ∧ r < r0 + 5) → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem carry_env {r : Nat → Nat} {r0 : Nat} (hr : ∀ i, r i = r0 + i) {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s r0 l i < 2 ^ 63) : EnvOK s (carryB r) := by
  refine envOK_of hs (fun r' l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
  · simp only [carryB, hr]
    split
    · rename_i h
      have : ∃ i < 5, r' = r0 + i := by rcases h with h | h | h | h | h <;> exact ⟨_, by omega, h⟩
      obtain ⟨i, hi, rfl⟩ := this
      exact Nat.le_sub_one_of_lt (hx l hl i hi)
    · exact lt64 _
  · simp only [carryB]
    split
    · subst_vars; rw [hk.km l hl]
    · split
      · subst_vars; rw [hk.k19 l hl]
      · exact lt64 _

theorem carryI_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 63) :
    WP isa (.block (carry id)) s (CarryPost 0 s) := by
  have hE := carry_env (r := id) (fun i => (Nat.zero_add i).symm) hs hk hx
  have e : Sym.init.run (carry id) = some carryI := carryS_eq id _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryI_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := carryI_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega) hl o
    have hs' : (fun j => lanes s 0 l j) = fun j => (envOf s).v j l := by
      funext j; simp only [lanes, Nat.zero_add, envOf_v]
    refine ⟨?_, by simp only [lanes, Nat.zero_add]; omega⟩
    simp only [lanes, Nat.zero_add] at e ⊢
    rw [e, carryI_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (carryI_keep r hr (by omega))

theorem carryF_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 63) :
    WP isa (.block (carry (5 + ·))) s (CarryPost 5 s) := by
  have hE := carry_env (r := (5 + ·)) (fun i => rfl) hs hk hx
  have e : Sym.init.run (carry (5 + ·)) = some carryF := carryS_eq (5 + ·) _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryF_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := carryF_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega) hl o
    have hs' : (fun j => lanes s 5 l j) = fun j => (envOf s).v (5 + j) l := by
      funext j; simp only [lanes, envOf_v]
    refine ⟨?_, by simp only [lanes]; omega⟩
    simp only [lanes] at e ⊢
    rw [e, carryF_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (carryF_keep r hr (by omega))

/-! ## Memory -/

open VG.Proof.X25519.X86_64 (Outside ofs word off) in
/-- Stores to slots in `[o, o + n)` change nothing outside it. -/
theorem stores_outside (s₀ : State) (base : Addr) (m : Mem) {o n : Nat} (hn : o + n < 2 ^ 63) :
    ∀ st : List (Nat × T), (∀ e ∈ st, o ≤ e.1 ∧ e.1 + 32 ≤ o + n) →
      Outside base o n m (stores s₀ base st m)
  | [], _ => fun _ _ => rfl
  | (e, t) :: st, h => by
    intro x hx
    have h₀ := h _ (List.mem_cons_self ..)
    simp only at h₀
    simp only [stores]
    rw [writeW_byte_off _ _ _ _ ?_]
    · exact stores_outside s₀ base m hn st (fun x hx => h x (List.mem_cons_of_mem _ hx)) x hx
    · show 256 / 8 ≤ (x - (base + BitVec.ofNat 64 e)).toNat
      rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]
      simp only [ofs] at hx
      have := (x - base).isLt
      rw [Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega)]
      omega

theorem mq_eq_word (m : Mem) (base : Addr) (d : Nat) : mq m base d = word m base d := rfl

open VG.Proof.X25519.X86_64 (Outside) in
theorem Consts.outside {m m' : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1)
    (h : Outside base 1024 480 m m') : Consts m' base x1 := by
  have w : ∀ d, 1504 ≤ d → d + 8 ≤ 4096 → mq m' base d = mq m base d := fun d h1 h2 => by
    rw [mq_eq_word, mq_eq_word]; exact h.word (by omega) (by omega)
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun i hi l hl => ?_,
    fun i hi l hl => ?_, hk.x1, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [slotv, w _ (by simp only [KA24]; omega) (by simp only [KA24]; omega)]; exact hk.a24 i hi l hl
  · rw [slotv, w _ (by simp only [KX1]; omega) (by simp only [KX1]; omega)]; exact hk.kx1 i hi l hl
  · rw [w _ (by simp only [K13]; omega) (by simp only [K13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [K26]; omega) (by simp only [K26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [K39]; omega) (by simp only [K39]; omega)]; exact hk.k39 l hl

/-! ## Products -/

/-- What `mul4 a` leaves: the product of the slot `a` and `ymm5–ymm9`, lane by
lane, in `ymm0–ymm4`. -/
def MulPost (base : Addr) (a : Nat) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' 0 l i = mulNat (slotv s.mem base a l) (lanes s 5 l) i ∧
      lanes s' 0 l i < 2 ^ 61) ∧
    (∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem mul4_wp {a : Nat} (ha : a % 32 = 0) {σ : Sym}
    (he : Sym.init.run (mul4 a) = some σ)
    (hnat : ∀ E l, ∀ k < 5, (σ.reg k).nat E l = mulNat (fun i => E.m (a + 32 * i) l) (fun j => E.v (5 + j) l) k)
    (hok : ∀ k < 5, ∀ l < 4, (σ.reg k).ok (mulB a) l = true ∧ (σ.reg k).bnd (mulB a) l < 2 ^ 61)
    (hkeep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → σ.reg r = .reg r) (hst : σ.st = [])
    {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hx : ∀ l < 4, ∀ i < 5, slotv s.mem base a l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mul4 a)) s (MulPost base a s) := by
  have hE : EnvOK s (mulB a) := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
    · simp only [mulB]
      split
      · rename_i h
        have := hy l hl (r - 5) (by omega)
        simp only [lanes, show 5 + (r - 5) = r by omega] at this
        omega
      · exact lt64 _
    · simp only [mulB]
      split
      · rename_i h
        obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = a + 32 * i := ⟨(d - a) / 32, by omega, by omega⟩
        have := hx l hl i hi
        simp only [slotv] at this
        omega
      · exact lt64 _
  refine WP.mono (run_ok hc he) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, hst]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => h.keep hr hl (hkeep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := hok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega⟩
  have hf : (fun i => (envOf s).m (a + 32 * i) l) = slotv s.mem base a l :=
    funext fun j => by rw [envOf_m hs, slotv]
  have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
  rw [e, hnat _ _ i hi, hf, hg]

/-! ## The stages -/

/-- The bias's limb `j`. -/
def kbv (j : Nat) : Nat := if j = 0 then 2 ^ 62 - 38912 else 2 ^ 62 - 2048

theorem kb_m {m : Mem} {base : Addr} (hk : CConsts m base) {j l : Nat} (hl : l < 4) :
    (mq m base (kb j + 8 * l)).toNat = kbv j := by
  simp only [kb, kbv]; split
  · exact hk.kb0 l hl
  · exact hk.kb1 l hl

/-- Stage 1's sums and differences, limb `i` of lane `l`, from the lanes `x`
(`x l i`). -/
def sumDiff (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 0 i + x 1 i
  | 1 => x 0 i + (kbv i - x 1 i)
  | 2 => x 2 i + x 3 i
  | _ => x 2 i + (kbv i - x 3 i)

theorem s1a_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage1a) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = sumDiff (lanes s 0) l i ∧ lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : EnvOK s s1aB := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
    · simp only [s1aB]
      split
      · have := hx l hl r (by omega); simp only [lanes, Nat.zero_add] at this; omega
      · exact lt64 _
    · simp only [s1aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact lt64 _
    · simp only [s1aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact Nat.zero_le _
  have e : Sym.init.run stage1a = some s1a := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s1a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 h2 l hl => h.keep hr hl (s1a_keep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := s1a_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega⟩
  rw [e, s1a_nat _ i hi l hl]
  have kbe : (envOf s).m (kb i) = fun l => (mq s.mem base (kb i + 8 * l)).toNat := by
    funext l; rw [envOf_m hs]
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [s1aNat, sumDiff, lanes, Nat.zero_add, envOf_v, kbe, kb_m hk.c (show 1 < 4 by decide),
      kb_m hk.c (show 3 < 4 by decide)]

/-- What `stage1b` leaves: `(A, B, D, C)` in `OPL`, `(A, B, A, B)` in `ymm5–ymm9`. -/
theorem s1b_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s) :
    WP isa (.block stage1b) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X25519.X86_64.Outside base OPL 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, slotv s'.mem base OPL l i = lanes s 0 (sel4 (ord 0 1 3 2).toNat l) i ∧
        lanes s' 5 l i = lanes s 0 (sel4 (ord 0 1 0 1).toNat l) i) ∧
      (∀ r < 16, (r < 5 ∨ 11 ≤ r) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage1b = some s1b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.gpr, h.rd, h.wr, ?_, fun l hl i hi => ⟨?_, ?_⟩, fun r hr h1 l hl => h.keep hr hl (s1b_keep r hr h1)⟩
  · rw [h.mem, hs]
    exact stores_outside _ _ _ (by decide) _ (by rw [s1b_st]; decide)
  · have hm : ∀ i < 5, ((OPL + 32 * i), T.perm (.reg i) (ord 0 1 3 2).toNat) ∈ s1b.st := by
      rw [s1b_st]; decide
    rw [slotv, h.mem, hs, stores_mq _ _ _ _ (hm i hi) hl (by rw [s1b_st]; decide) (by rw [s1b_st]; decide)]
    simp only [T.eval, lanes, Nat.zero_add]
  · have := h.reg (xr (5 + i)) l hl
    rw [xi_xr _ (by omega), s1b_regs i hi] at this
    simp only [lanes, Nat.zero_add, this, T.eval]

/-- Stage 2's first operand from `(AA, BB, DA, CB)` (`x l i`):
`(DA + CB, DA + bias - CB, AA, AA + bias - BB)`. -/
def opV (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 2 i + x 3 i
  | 1 => x 2 i + (kbv i - x 3 i)
  | 2 => x 0 i + 0
  | _ => x 0 i + (kbv i - x 1 i)

/-- Stage 2's second operand: `(DA + CB, DA + bias - CB, BB, a24)`. -/
def opW (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 2 i + x 3 i
  | 1 => x 2 i + (kbv i - x 3 i)
  | 2 => x 1 i
  | _ => if i = 0 then 121665 else 0

theorem s2a_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage2a) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 5 l i = opV (lanes s 0) l i ∧ lanes s' 5 l i < 2 ^ 63 ∧
        lanes s' 0 l i = opW (lanes s 0) l i ∧ lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 14 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : EnvOK s s2aB := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
    · simp only [s2aB]
      split
      · have := hx l hl r (by omega); simp only [lanes, Nat.zero_add] at this; omega
      · exact lt64 _
    · simp only [s2aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · split
          · rename_i h
            obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = KA24 + 32 * i :=
              ⟨(d - KA24) / 32, by simp only [KA24] at h ⊢; omega, by simp only [KA24] at h ⊢; omega⟩
            have := hk.a24 i hi l hl
            simp only [slotv] at this
            rw [this]; split <;> decide
          · exact lt64 _
    · simp only [s2aB]
      split
      · subst_vars; rw [hk.kb0 l hl]
      · split
        · subst_vars; rw [hk.kb1 l hl]
        · exact Nat.zero_le _
  have e : Sym.init.run stage2a = some s2a := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s2a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (s2a_keep r hr h1)⟩
  obtain ⟨o1, b1, o2, b2⟩ := s2a_ok i hi l hl
  obtain ⟨e1, be1⟩ := h.out hE (by omega) hl o1
  obtain ⟨e2, be2⟩ := h.out hE (by omega) hl o2
  obtain ⟨n1, n2⟩ := s2a_nat (envOf s) i hi l hl
  simp only [lanes, Nat.zero_add] at e1 e2 ⊢
  refine ⟨?_, by omega, ?_, by omega⟩
  · rw [e1, n1]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [s2aV, opV, lanes, Nat.zero_add, envOf_v, envOf_m hs, kb_m hk.c (show 1 < 4 by decide),
        kb_m hk.c (show 3 < 4 by decide)]
  · rw [e2, n2]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [s2aW, opW, lanes, Nat.zero_add, envOf_v, envOf_m hs, kb_m hk.c (show 1 < 4 by decide)]
    have := hk.a24 i hi 3 (by decide)
    simp only [slotv] at this
    rw [this]
    simp

/-- What `stage2b` leaves: stage 2's first operand in `OPV`, the second in
`ymm5–ymm9`. -/
theorem s2b_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s) :
    WP isa (.block stage2b) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X25519.X86_64.Outside base OPV 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, slotv s'.mem base OPV l i = lanes s 5 l i ∧ lanes s' 5 l i = lanes s 0 l i) ∧
      (∀ r < 16, (r < 5 ∨ 10 ≤ r) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage2b = some s2b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.gpr, h.rd, h.wr, ?_, fun l hl i hi => ⟨?_, ?_⟩, fun r hr h1 l hl => h.keep hr hl (s2b_keep r hr h1)⟩
  · rw [h.mem, hs]
    exact stores_outside _ _ _ (by decide) _ (by rw [s2b_st]; decide)
  · have hm : ∀ i < 5, ((OPV + 32 * i), T.reg (5 + i)) ∈ s2b.st := by
      rw [s2b_st]; decide
    rw [slotv, h.mem, hs, stores_mq _ _ _ _ (hm i hi) hl (by rw [s2b_st]; decide) (by rw [s2b_st]; decide)]
    simp only [T.eval, lanes]
  · have := h.reg (xr (5 + i)) l hl
    rw [xi_xr _ (by omega), s2b_regs i hi] at this
    simp only [lanes, Nat.zero_add, this, T.eval]

/-- Stage 3's second operand, from stage 2's product `(x₃', t, x₂', a24 E)`
(`x l i`) and first operand `(…, …, AA, E)` (`v l i`): `(1, AA + a24 E, 1, x₁)`. -/
def opH (x1 : Nat → Nat) (x v : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 1 => v 2 i + x 3 i
  | 3 => x1 i
  | _ => if i = 0 then 1 else 0

/-- Stage 3's first operand: `(x₂', E, x₃', t)`. -/
def opG (x v : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 2 i
  | 1 => v 3 i
  | 2 => x 0 i
  | _ => x 1 i

theorem s3a_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61)
    (hv : ∀ l < 4, ∀ i < 5, slotv s.mem base OPV l i < 2 ^ 52) :
    WP isa (.block stage3a) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 5 l i = opH x1 (lanes s 0) (slotv s.mem base OPV) l i ∧
        lanes s' 5 l i < 2 ^ 63 ∧
        lanes s' 0 l i = opG (lanes s 0) (slotv s.mem base OPV) l i ∧ lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 13 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE : EnvOK s s3aB := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
    · simp only [s3aB]
      split
      · have := hx l hl r (by omega); simp only [lanes, Nat.zero_add] at this; omega
      · exact lt64 _
    · simp only [s3aB]
      split
      · rename_i h
        rcases h with ⟨h | h, h'⟩
        · obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = OPV + 32 * i :=
            ⟨(d - OPV) / 32, by simp only [OPV] at h h' ⊢; omega, by simp only [OPV] at h h' ⊢; omega⟩
          have := hv l hl i hi
          simp only [slotv] at this
          omega
        · obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = KX1 + 32 * i :=
            ⟨(d - KX1) / 32, by simp only [KX1] at h h' ⊢; omega, by simp only [KX1] at h h' ⊢; omega⟩
          have := kx1_le hk hi hl
          simp only [slotv] at this
          omega
      · exact lt64 _
  have e : Sym.init.run stage3a = some s3a := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s3a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (s3a_keep r hr h1)⟩
  obtain ⟨o1, b1, o2, b2⟩ := s3a_ok i hi l hl
  obtain ⟨e1, be1⟩ := h.out hE (by omega) hl o1
  obtain ⟨e2, be2⟩ := h.out hE (by omega) hl o2
  obtain ⟨n1, n2⟩ := s3a_nat (envOf s) i hi l hl
  simp only [lanes, Nat.zero_add] at e1 e2 ⊢
  refine ⟨?_, by omega, ?_, by omega⟩
  · rw [e1, n1]
    have kx := hk.kx1 i hi l hl
    simp only [slotv] at kx
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [s3aH, opH, lanes, Nat.zero_add, envOf_v, envOf_m hs, slotv, kx] <;> simp
  · rw [e2, n2]
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
      simp only [s3aG, opG, lanes, Nat.zero_add, envOf_v, envOf_m hs, slotv]

/-- What `stage3b` leaves: stage 3's first operand in `OPG`. -/
theorem s3b_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s) :
    WP isa (.block stage3b) s fun s' => vm s s' = s' ∧
      VG.Proof.X25519.X86_64.Outside base OPG 160 s.mem s'.mem ∧
      (∀ l < 4, ∀ i < 5, slotv s'.mem base OPG l i = lanes s 0 l i) ∧
      (∀ r < 16, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage3b = some s3b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, ?_, fun l hl i hi => ?_, fun r hr l hl => h.keep hr hl (s3b_keep r hr)⟩
  · rw [h.mem, hs]
    exact stores_outside _ _ _ (by decide) _ (by rw [s3b_st]; decide)
  · have hm : ∀ i < 5, ((OPG + 32 * i), T.reg i) ∈ s3b.st := by
      rw [s3b_st]; decide
    rw [slotv, h.mem, hs, stores_mq _ _ _ _ (hm i hi) hl (by rw [s3b_st]; decide) (by rw [s3b_st]; decide)]
    simp only [T.eval, lanes, Nat.zero_add]

/-! ## The swap -/

/-- The mask into `ymm15`, then the swap. -/
def vsw : List Instr := [.vop (.vmovq (y 15) .rcx), .vop (.vpbroadcastq .l256 (y 15) (y 15))] ++ vswap

def swS : Sym := symOf vsw

theorem swS_regs : ∀ j < 5, swS.reg j = .xor (.reg j)
    (.and (.xor (.perm (.reg j) (ord 2 3 0 1).toNat) (.reg j)) (.bc (.lane0 (.gpr .rcx)))) := by
  decide +kernel
theorem swS_keep : ∀ r < 15, 5 ≤ r → r ≠ 10 → swS.reg r = .reg r := by decide +kernel
theorem swS_st : swS.st = [] := by decide +kernel

theorem xor_mask (x y : BitVec 64) (b : Bool) :
    x ^^^ ((y ^^^ x) &&& VG.Proof.X25519.X86_64.mask b) = if b then y else x := by
  cases b
  · simp [VG.Proof.X25519.X86_64.mask]
  · simp only [VG.Proof.X25519.X86_64.mask, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm y x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem sel4_swap : ∀ l < 4, sel4 (ord 2 3 0 1).toNat l = l ^^^ 2 := by decide

theorem vsw_wp {s : State} (hc : Ctx s) {b : Bool} (hm : s.gpr .rcx = VG.Proof.X25519.X86_64.mask b) :
    WP isa (.block vsw) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, qw s' (xr i) l = qw s (xr i) (if b then l ^^^ 2 else l)) ∧
      (∀ r < 15, 5 ≤ r → r ≠ 10 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run vsw = some swS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, swS_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 h2 l hl => h.keep (by omega) hl (swS_keep r hr h1 h2)⟩
  rw [h.reg _ l hl, xi_xr _ (by omega), swS_regs i hi]
  simp only [T.eval, ite_true, hm, sel4_swap l hl]
  rw [xor_mask]
  cases b <;> rfl

end VG.Proof.X25519.X86_64.Ifma
