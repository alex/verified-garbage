import VerifiedGarbage.Proof.MlKem.AArch64.SampleLoop
import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.Hash

/-!
# ML-KEM on AArch64: `SampleNTT` up to its loop

Untrusted: everything here is checked by Lean. `sampleSqueeze` saves our
caller's `x25`, `x26` and `x30` in `scratch`, computes SHAKE128 of the seed
into `scratch[0, 840)` with the verified Keccak functions from the all-zero
state (`Proof/MlKem/Hash.lean`), sets `a` to zeros, and restores the
registers: it leaves what the loop needs (`LPre`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against; the artifact's is the
shared contract of `Spec/`, which implies it. AArch64 contract for
`sampleNTT(seed = x0, a = x1, scratch = x2) -> w0`: with the 34 bytes `B`
at `seed`, writes `SampleNTT(B)` to `a` and returns 1, or returns 0. The
code may read `seed`, and write `a` and `scratch` (2048 bytes), and the
16 bytes below the stack pointer (the Keccak functions' frames). It may
leak `B`. -/
def sampleAArch64 : Contract AArch64.isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 34⟩
    let a : Region := ⟨s.gpr .x1, 1024⟩
    let scratch : Region := ⟨s.gpr .x2, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch
  post s s' :=
    ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (s.gpr .x1)) ∧
      Outcome (fun iters => sampleNTT iters (bytesAt s.mem (s.gpr .x0) 34))
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (s.gpr .x1))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp ∧
      (bytesAt s₁.mem (s₁.gpr .x0) 34).map (·.toNat) = (bytesAt s₂.mem (s₂.gpr .x0) 34).map (·.toNat)

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr shakeSuffix)

section
variable (s₀ : State)

abbrev sdP : Addr := s₀.gpr .x0
abbrev aP : Addr := s₀.gpr .x1
abbrev scP : Addr := s₀.gpr .x2
/-- Offset `k` of `scratch`. -/
abbrev So (k : Nat) : Addr := scP s₀ + BitVec.ofNat 64 k
abbrev seedR : Region := ⟨sdP s₀, 34⟩
abbrev aR : Region := polyRegion (aP s₀)
abbrev scR : Region := ⟨scP s₀, 2048⟩
abbrev kR : Region := ⟨s₀.sp - 16, 16⟩
/-- The seed. -/
abbrev Bs : List Byte := bytesAt s₀.mem (sdP s₀) 34

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [seedR s₀]
  wr : s₀.wr = [aR s₀, scR s₀]
  d_sa : (seedR s₀).Disjoint (aR s₀)
  d_ss : (seedR s₀).Disjoint (scR s₀)
  d_as : (aR s₀).Disjoint (scR s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  k_s : (kR s₀).Disjoint (seedR s₀)
  k_a : (kR s₀).Disjoint (aR s₀)
  k_c : (kR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : sampleAArch64.pre s₀) : Pre s₀ :=
  let ⟨a, b, c, d, e, f, g, i, j⟩ := h
  ⟨a, b, c, d, e, f, g, i, j⟩

theorem mem2 {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.mp h)

theorem mem3 {α : Type} {a b c x : α} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem2 h)

theorem mem4 {α : Type} {a b c d x : α} (h : x ∈ [a, b, c, d]) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem3 h)

/-! ## Regions -/

theorem below16 (sp : Addr) : below sp 16 = ⟨sp - 16, 16⟩ := rfl

theorem sub_so (s₀ : State) {off n : Nat} (h : off + n ≤ 2048) :
    Region.Sub ⟨So s₀ off, n⟩ (scR s₀) := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - scP s₀).toNat ≤ (x - So s₀ off).toNat + off := by
    rw [show x - scP s₀ = (x - So s₀ off) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem disj_so (s₀ : State) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2048)
    (hb : b + k ≤ 2048) : Region.Disjoint ⟨So s₀ a, n⟩ ⟨So s₀ b, k⟩ := fun x h₁ h₂ =>
  sep_off (scP s₀) h (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)

theorem in_sc {s₀ : State} (hp : Pre s₀) {off n : Nat} (h : off + n ≤ 2048) :
    InRegions s₀.wr (So s₀ off) n := by
  rw [hp.wr]; exact in_regions (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (contains_off h (by decide))

theorem covers_sc {s₀ : State} (hp : Pre s₀) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = So s₀ off ∧ off + r.len ≤ 2048) : Covers rs s₀.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨scR s₀, by rw [hp.wr]; simp, off, hb, hl⟩

theorem covers_rw {s₀ : State} {rs : List Region} (h : Covers rs s₀.wr) :
    Covers rs (s₀.rd ++ s₀.wr) := fun a n hi => in_rd_wr (h a n hi)

/-- The stack is disjoint from the parts of `scratch`. -/
theorem k_so {s₀ : State} (hp : Pre s₀) {off n : Nat} (h : off + n ≤ 2048) :
    (kR s₀).Disjoint ⟨So s₀ off, n⟩ := hp.k_c.sub_right (sub_so s₀ h)

/-! ## The saved registers -/

/-- Our caller's `x25`, `x26` and `x30`, saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (So s₀ 1680) 64 = s₀.gpr .x25 ∧ m.readW (So s₀ 1688) 64 = s₀.gpr .x26 ∧
    m.readW (So s₀ 1696) 64 = s₀.gpr .x30

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨So s₀ 1680, 24⟩ r) : Saved s₀ m' := by
  have e : ∀ k, k < 3 → m'.readW (So s₀ (1680 + 8 * k)) 64 = m.readW (So s₀ (1680 + 8 * k)) 64 :=
    fun k hk => by
      refine hf.readW (r := ⟨So s₀ 1680, 24⟩) ?_ hd (by decide)
      rw [show So s₀ (1680 + 8 * k) = So s₀ 1680 + BitVec.ofNat 64 (8 * k) by rw [ptr_add]]
      exact contains_off (by omega) (by decide)
  exact ⟨(e 0 (by decide)).trans h.1, (e 1 (by decide)).trans h.2.1, (e 2 (by decide)).trans h.2.2⟩

/-- Between the prologue and the loop: `x25 = a` and `x26 = scratch`, the
saved registers, the other callee-saved registers, and the memory outside
`scratch` and the stack below it. -/
structure Mid (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x25 : s.gpr .x25 = aP s₀
  x26 : s.gpr .x26 = scP s₀
  cs : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → s.gpr r = s₀.gpr r
  sv : Saved s₀ s.mem
  frame : Frame [scR s₀, below s₀.sp 16] s₀.mem s.mem

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .x30 → r ∉ linkRegs := by decide

/-- A call that writes parts of `scratch` apart from the saved registers,
and the stack below it. -/
theorem Mid.call {s₀ s s' : State} (h : Mid s₀ s) {rs : List Region} (hk : Kept rs s s')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨So s₀ 1680, 24⟩ r)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [scR s₀, below s₀.sp 16], Region.Sub r r') : Mid s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.cs _ (by decide) (by decide), h.x25], by rw [hk.cs _ (by decide) (by decide), h.x26],
    fun r hr h25 h26 h30 => by rw [hk.cs r hr h30, h.cs r hr h25 h26 h30], h.sv.frame hk.frame hd,
    h.frame.trans (hk.frame.sub hs)⟩

/-- A block that writes no callee-saved register nor memory. -/
theorem Mid.keep {s₀ s s' : State} (h : Mid s₀ s) {regs : List Reg}
    (hk : Keep regs s s') (hm : s'.mem = s.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide) :
    Mid s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.get .x25 (fun h' => hr _ h' (by decide)), h.x25],
    by rw [hk.get .x26 (fun h' => hr _ h' (by decide)), h.x26],
    fun r hp' h25 h26 h30 => by rw [hk.get r (fun h' => hr _ h' hp'), h.cs r hp' h25 h26 h30],
    by rw [hm]; exact h.sv, by rw [hm]; exact h.frame⟩

/-! ## The prologue -/

/-- The zeros of the Keccak state. -/
def zst (n : Nat) : List Instr := (List.range n).map fun k => .str .x .x9 .x2 (840 + 8 * k)

theorem zst_ok {s₀ : State} (hp : Pre s₀) :
    ∀ n ≤ 25, ∀ {s : State}, s.gpr .x9 = 0 → s.gpr .x2 = scP s₀ → s.wr = s₀.wr →
      WP isa (.block (zst n)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp ∧ (∀ k < n, s'.mem.readW (So s₀ (840 + 8 * k)) 64 = 0) ∧
        Frame [⟨So s₀ 840, 200⟩] s.mem s'.mem
  | 0, _, s, _, _, _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | n + 1, hn, s, h9, h2, hw => by
    rw [zst, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zst_ok hp n (by omega) h9 h2 hw) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := So s₀ (840 + 8 * n)) (by constructor <;> omega) (by rw [g₁, h2])
      (by rw [w₁, hw]; exact in_sc hp (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁, h9]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      refine f₁.writeW (List.mem_singleton_self _) _ ?_
      rw [show So s₀ (840 + 8 * n) = So s₀ 840 + BitVec.ofNat 64 (8 * n) by rw [ptr_add]]
      exact contains_off (by omega) (by decide)

theorem stateAt_zero {m : Mem} {p : Addr}
    (h : ∀ k < 25, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = 0) : stateAt m p = Spec.Sha3.zero := by
  refine Vector.ext fun i hi => ?_
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

/-- What the prologue leaves: `absorb`'s arguments, and the Keccak state zero. -/
structure AfterPro (s₀ s : State) : Prop where
  mid : Mid s₀ s
  zero : stateAt s.mem (So s₀ 840) = Spec.Sha3.zero
  x0 : s.gpr .x0 = So s₀ 840
  x1 : (s.gpr .x1).toNat = 168
  x2 : (s.gpr .x2).toNat = 0
  x3 : s.gpr .x3 = sdP s₀
  x4 : (s.gpr .x4).toNat = 34
  x5 : s.gpr .x5 = So s₀ 1040

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block samplePrologue) s₀ (AfterPro s₀) := by
  rw [samplePrologue, WP.block_append_iff, WP.block_append_iff]
  refine wp_strx (a := So s₀ 1680) (by decide) rfl (in_sc hp (by decide)) fun s₁ h₁ => ?_
  refine wp_strx (a := So s₀ 1688) (by decide) (by rw [h₁.gpr]) (by rw [h₁.wr]; exact in_sc hp (by decide))
    fun s₂ h₂ => ?_
  refine wp_strx (a := So s₀ 1696) (by decide) (by rw [h₂.gpr, h₁.gpr])
    (by rw [h₂.wr, h₁.wr]; exact in_sc hp (by decide)) fun s₃ h₃ => ?_
  refine wp_mov fun s₄ h₄ e₄ => wp_mov fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  have k₆ := (h₄.keep.trans h₅.keep).trans h₆.keep
  have m₆ : s₆.mem = ((s₀.mem.writeW (So s₀ 1680) (s₀.gpr .x25)).writeW (So s₀ 1688) (s₀.gpr .x26)).writeW
      (So s₀ 1696) (s₀.gpr .x30) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₂.gpr, h₁.gpr]
  have g₃ : ∀ r, s₃.gpr r = s₀.gpr r := fun r => by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  have sv₆ : Saved s₀ s₆.mem := by
    rw [m₆]
    refine ⟨?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
    · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
  have f₆ : Frame [scR s₀, below s₀.sp 16] s₀.mem s₆.mem := by
    rw [m₆]
    have hm : scR s₀ ∈ [scR s₀, below s₀.sp 16] := List.mem_cons_self ..
    exact (((Frame.refl _ _).writeW hm _ (contains_off (by decide) (by decide))).writeW hm _
      (contains_off (by decide) (by decide))).writeW hm _ (contains_off (by decide) (by decide))
  have mid₆ : Mid s₀ s₆ :=
    ⟨by rw [k₆.rd, h₃.rd, h₂.rd, h₁.rd], by rw [k₆.wr, h₃.wr, h₂.wr, h₁.wr],
      by rw [k₆.sp, h₃.sp, h₂.sp, h₁.sp], by rw [h₆.get .x25, h₅.get .x25, e₄, g₃],
      by rw [h₆.get .x26, e₅, h₄.get .x2, g₃],
      fun r hr h25 h26 _ => by
        rw [h₆.get r (by simpa using fun e => by subst e; revert hr; decide),
          h₅.get r (by simpa using h26), h₄.get r (by simpa using h25), g₃],
      sv₆, f₆⟩
  have z9 : s₆.gpr .x9 = 0 := by rw [e₆]; rfl
  have c2 : s₆.gpr .x2 = scP s₀ := by rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, g₃]
  refine WP.mono (zst_ok hp 25 (by decide) z9 c2 mid₆.wr) fun s₇ ⟨g₇, r₇, w₇, p₇, z₇, f₇⟩ => ?_
  have mid₇ : Mid s₀ s₇ :=
    ⟨by rw [r₇, mid₆.rd], by rw [w₇, mid₆.wr], by rw [p₇, mid₆.sp], by rw [g₇, mid₆.x25],
      by rw [g₇, mid₆.x26], fun r hr a b c => by rw [g₇, mid₆.cs r hr a b c],
      mid₆.sv.frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact disj_so s₀ (by omega) (by omega) (by omega)),
      mid₆.frame.trans (f₇.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scR s₀, List.mem_cons_self .., sub_so s₀ (by omega)⟩)⟩
  have z₇' : stateAt s₇.mem (So s₀ 840) = Spec.Sha3.zero :=
    stateAt_zero fun k hk => by rw [ptr_add]; exact z₇ k hk
  refine wp_mov fun s₈ h₈ e₈ => wp_addImm (by decide) fun s₉ h₉ e₉ => wp_movz fun s₁₀ h₁₀ e₁₀ =>
    wp_movz fun s₁₁ h₁₁ e₁₁ => wp_movz fun s₁₂ h₁₂ e₁₂ => wp_addImm (by decide) fun s₁₃ h₁₃ e₁₃ =>
    wp_nil ?_
  have k₁₃ := ((((h₈.keep.trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep).trans h₁₂.keep).trans h₁₃.keep
  have m₁₃ : s₁₃.mem = s₇.mem := by
    rw [h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem]
  refine ⟨mid₇.keep k₁₃ m₁₃, by rw [m₁₃]; exact z₇', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₁₃.get .x0, h₁₂.get .x0, h₁₁.get .x0, h₁₀.get .x0, e₉, h₈.get .x26, mid₇.x26]
  · rw [h₁₃.get .x1, h₁₂.get .x1, h₁₁.get .x1, e₁₀]; rfl
  · rw [h₁₃.get .x2, h₁₂.get .x2, e₁₁]; rfl
  · rw [h₁₃.get .x3, h₁₂.get .x3, h₁₁.get .x3, h₁₀.get .x3, h₉.get .x3, e₈, g₇, h₆.get .x0,
      h₅.get .x0, h₄.get .x0, g₃]
  · rw [h₁₃.get .x4, e₁₂]; rfl
  · rw [e₁₃, h₁₂.get .x26, h₁₁.get .x26, h₁₀.get .x26, h₉.get .x26, h₈.get .x26, mid₇.x26]

/-! ## The hash -/

/-- The SHAKE128 output of the seed in `scratch`. -/
def Buf (s₀ : State) (m : Mem) : Prop := ∀ p < 840, m (So s₀ 0 + BitVec.ofNat 64 p) = xofByte (Bs s₀) p

/-- The saved registers are apart from the parts of `scratch` the calls use. -/
theorem sv_disj (s₀ : State) {off n : Nat} (h : off + n ≤ 1680) :
    Region.Disjoint ⟨So s₀ 1680, 24⟩ ⟨So s₀ off, n⟩ := disj_so s₀ (by omega) (by omega) (by omega)

theorem sv_below {s₀ : State} (hp : Pre s₀) : Region.Disjoint ⟨So s₀ 1680, 24⟩ (below s₀.sp 16) := by
  rw [below16]; exact (k_so hp (by omega)).symm

theorem stk_eq {s₀ s : State} (h : s.sp = s₀.sp) : stk s = kR s₀ := by rw [stk, h]

theorem seed_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [scR s₀, below s₀.sp 16] s₀.mem m) :
    bytesAt m (sdP s₀) 34 = Bs s₀ :=
  bytesAt_frame hf (fun r hr => by
    rcases mem2 hr with rfl | rfl
    · exact hp.d_ss
    · rw [below16]; exact hp.k_s.symm) (by decide)

/-- `absorb`, `pad` and `squeeze`, then `R`. -/
theorem calls_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : AfterPro s₀ s) {R : Prog isa}
    {Q : State → Prop} (hR : ∀ s', Mid s₀ s' → Buf s₀ s'.mem → WP isa R s' Q) :
    WP isa (.seq (.call "vg_keccak_absorb" Impl.Sha3.AArch64.Stream.absorb) <|
      .seq (.block samplePadArgs) <|
      .seq (.call "vg_keccak_pad" Impl.Sha3.AArch64.Stream.pad) <|
      .seq (.block sampleSqueezeArgs) <|
      .seq (.call "vg_keccak_squeeze" Impl.Sha3.AArch64.Stream.squeeze) R) s Q := by
  have hsd : ∀ {u : State}, Mid s₀ u → 16 ≤ u.sp.toNat := fun hu => by rw [hu.sp]; exact hp.sp16
  have cw : ∀ {u : State}, Mid s₀ u → ∀ {rs : List Region},
      (∀ r ∈ rs, ∃ off, r.base = So s₀ off ∧ off + r.len ≤ 2048) → Covers rs u.wr :=
    fun hu _ h' => by rw [hu.wr]; exact covers_sc hp h'
  have sub : ∀ {u : State}, Mid s₀ u → ∀ {off n : Nat}, off + n ≤ 2048 →
      ∃ r' ∈ [scR s₀, below s₀.sp 16], Region.Sub ⟨So s₀ off, n⟩ r' :=
    fun _ _ _ h' => ⟨scR s₀, List.mem_cons_self .., sub_so s₀ h'⟩
  have subk : ∀ {u : State}, Mid s₀ u → ∃ r' ∈ [scR s₀, below s₀.sp 16], Region.Sub (below u.sp 16) r' :=
    fun hu => ⟨below s₀.sp 16, by simp, by rw [hu.sp]; exact fun _ h => h⟩
  -- absorb
  refine WP.seq (absorb_call (st := So s₀ 840) (sc := So s₀ 1040) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5
    rate168 (by decide) (disj_so s₀ (by omega) (by omega) (by omega))
    (hp.d_ss.sub_right (sub_so s₀ (by omega))) (hp.d_ss.sub_right (sub_so s₀ (by omega)))
    (hsd h.mid) (by rw [stk_eq h.mid.sp]; exact k_so hp (by omega)) (by rw [stk_eq h.mid.sp]; exact hp.k_s)
    (by rw [stk_eq h.mid.sp]; exact k_so hp (by omega)) ?_ (cw h.mid ?_) fun s₁ k₁ r₁ => ?_)
  · rw [h.mid.rd, h.mid.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    rcases mem3 hr with rfl | rfl | rfl
    · exact ⟨seedR s₀, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨scR s₀, by simp, 840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨scR s₀, by simp, 1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  · intro r hr
    rcases mem2 hr with rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  have mid₁ : Mid s₀ s₁ := h.mid.call k₁ (fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact sv_disj s₀ (by omega)
      · exact sv_disj s₀ (by omega)
      · rw [h.mid.sp]; exact sv_below hp)
    (fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact sub h.mid (by omega)
      · exact sub h.mid (by omega)
      · exact subk h.mid)
  have rep₁ : Repr s₁.mem (So s₀ 840) 168 (Bs s₀) := by
    have := r₁ [] (repr_nil h.zero) (by decide)
    rwa [List.nil_append, seed_frame hp h.mid.frame] at this
  -- pad
  refine WP.seq (wp_addImm (by decide) fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ =>
    wp_movz fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ => wp_nil ?_)
  have k₆ := ((((h₂.keep.trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep)
  have m₆ : s₆.mem = s₁.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem]
  have mid₆ := mid₁.keep k₆ m₆
  refine WP.seq (pad_call (st := So s₀ 840) (sc := So s₀ 1040) (rate := 168) (pos := 34)
    (by rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, mid₁.x26])
    (by rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, e₃]; rfl) (by rw [h₆.get .x2, h₅.get .x2, e₄]; rfl)
    (by rw [e₆, h₅.get .x26, h₄.get .x26, h₃.get .x26, h₂.get .x26, mid₁.x26]) rate168 (by decide)
    (disj_so s₀ (by omega) (by omega) (by omega)) (hsd mid₆)
    (by rw [stk_eq mid₆.sp]; exact k_so hp (by omega)) (by rw [stk_eq mid₆.sp]; exact k_so hp (by omega))
    (covers_rw (cw mid₆ ?_)) (cw mid₆ ?_) fun s₇ k₇ r₇ => ?_)
  · intro r hr
    rcases mem2 hr with rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  · intro r hr
    rcases mem2 hr with rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  have mid₇ : Mid s₀ s₇ := mid₆.call k₇ (fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact sv_disj s₀ (by omega)
      · exact sv_disj s₀ (by omega)
      · rw [mid₆.sp]; exact sv_below hp)
    (fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact sub mid₆ (by omega)
      · exact sub mid₆ (by omega)
      · exact subk mid₆)
  have st₇ : stateAt s₇.mem (So s₀ 840) = padded 168 shakeSuffix (Bs s₀) := by
    have hs : (s₆.gpr .x3).setWidth 8 = shakeSuffix := by
      rw [h₆.get .x3, e₅]; decide
    have := r₇ (Bs s₀) (by rw [m₆]; exact rep₁) (by rw [bytesAt_length])
    rw [hs] at this
    exact this
  -- squeeze
  refine WP.seq (wp_addImm (by decide) fun s₈ h₈ e₈ => wp_movz fun s₉ h₉ e₉ => wp_movz fun s₁₀ h₁₀ e₁₀ =>
    wp_mov fun s₁₁ h₁₁ e₁₁ => wp_movz fun s₁₂ h₁₂ e₁₂ => wp_addImm (by decide) fun s₁₃ h₁₃ e₁₃ =>
    wp_nil ?_)
  have k₁₃ := (((((h₈.keep.trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep).trans h₁₂.keep).trans h₁₃.keep)
  have m₁₃ : s₁₃.mem = s₇.mem := by rw [h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem]
  have mid₁₃ := mid₇.keep k₁₃ m₁₃
  refine WP.seq (squeeze_call (st := So s₀ 840) (out := So s₀ 0) (sc := So s₀ 1040) (rate := 168)
    (pos := 0) (len := 840)
    (by rw [h₁₃.get .x0, h₁₂.get .x0, h₁₁.get .x0, h₁₀.get .x0, h₉.get .x0, e₈, mid₇.x26])
    (by rw [h₁₃.get .x1, h₁₂.get .x1, h₁₁.get .x1, h₁₀.get .x1, e₉]; rfl)
    (by rw [h₁₃.get .x2, h₁₂.get .x2, h₁₁.get .x2, e₁₀]; rfl)
    (by rw [h₁₃.get .x3, h₁₂.get .x3, e₁₁, h₁₀.get .x26, h₉.get .x26, h₈.get .x26, mid₇.x26]; exact (ptr_zero _).symm)
    (by rw [h₁₃.get .x4, e₁₂]; rfl)
    (by rw [e₁₃, h₁₂.get .x26, h₁₁.get .x26, h₁₀.get .x26, h₉.get .x26, h₈.get .x26, mid₇.x26])
    rate168 (by decide) (disj_so s₀ (by omega) (by omega) (by omega))
    (disj_so s₀ (by omega) (by omega) (by omega)) (disj_so s₀ (by omega) (by omega) (by omega))
    (hsd mid₁₃) (by rw [stk_eq mid₁₃.sp]; exact k_so hp (by omega))
    (by rw [stk_eq mid₁₃.sp]; exact k_so hp (by omega)) (by rw [stk_eq mid₁₃.sp]; exact k_so hp (by omega))
    (covers_rw (cw mid₁₃ ?_)) (cw mid₁₃ ?_) fun s₁₄ k₁₄ r₁₄ => ?_)
  · intro r hr
    rcases mem3 hr with rfl | rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨0, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  · intro r hr
    rcases mem3 hr with rfl | rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨0, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  have mid₁₄ : Mid s₀ s₁₄ := mid₁₃.call k₁₄ (fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sv_disj s₀ (by omega)
      · exact sv_disj s₀ (by omega)
      · exact sv_disj s₀ (by omega)
      · rw [mid₁₃.sp]; exact sv_below hp)
    (fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sub mid₁₃ (by omega)
      · exact sub mid₁₃ (by omega)
      · exact sub mid₁₃ (by omega)
      · exact subk mid₁₃)
  refine hR s₁₄ mid₁₄ fun p hp' => ?_
  rw [m₁₃, st₇, ← xof_eq] at r₁₄
  rw [← bytesAt_getD s₁₄.mem (So s₀ 0) hp', r₁₄, xof_getD _ hp']

/-! ## `a` set to zeros, and the registers back -/

/-- After `k` coefficients of `a` set to zero. -/
structure ZInv (s₀ s₁ : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x3, .x4] s₁ u
  x3 : u.gpr .x3 = coeffAddr (aP s₀) k
  x4 : (u.gpr .x4).toNat = 256 - k
  coeffs : CoeffsUpTo u.mem (aP s₀) k (fun _ => 0) fun i => coeffAt s₁.mem (aP s₀) i
  frame : Frame [aR s₀] s₁.mem u.mem

theorem zero_step {s₀ : State} (hp : Pre s₀) {s₁ : State} (hw : s₁.wr = s₀.wr) (h9 : s₁.gpr .x9 = 0)
    {k : Nat} (hk : k < 256) {u : State} (h : ZInv s₀ s₁ k u) :
    WP isa (.block zeroBody) u fun u' => ZInv s₀ s₁ (k + 1) u' ∧ ((u'.gpr .x4).toNat ≠ 0 ↔ k + 1 ≠ 256) := by
  have hin : InRegions u.wr (coeffAddr (aP s₀) k) 4 := by
    rw [h.keep.wr, hw, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ (show k < n from hk))
  refine wp_strw (a := coeffAddr (aP s₀) k) (by decide) (by rw [h.x3, ptr_zero]) hin fun u₁ h₁ =>
    wp_addImm (by decide) fun u₂ h₂ e₂ => wp_subImm (by decide) fun u₃ h₃ e₃ => wp_nil ?_
  have c4 : (u₂.gpr .x4).toNat = 256 - k := by rw [h₂.get .x4, h₁.gpr, h.x4]
  have v4 : (u₃.gpr .x4).toNat = 256 - (k + 1) := by
    rw [e₃, toNat_sub_n (by rw [c4]; simp; omega), c4]
    simp
    omega
  have m₃ : u₃.mem = u.mem.writeW (coeffAddr (aP s₀) k) ((u.gpr .x9).setWidth 32) := by
    rw [h₃.mem, h₂.mem, h₁.mem]
  have z : (u.gpr .x9).setWidth 32 = 0 := by rw [h.keep.get .x9, h9]; rfl
  refine ⟨⟨(h.keep.trans ((h₁.keep.trans h₂.keep).trans h₃.keep)).mono, ?_, v4, ?_, ?_⟩,
    by rw [v4]; omega⟩
  · rw [h₃.get .x3, e₂, h₁.gpr, h.x3, coeffAddr, coeffAddr, ptr_next]
  · rw [m₃, z]; exact CoeffsUpTo.write h.coeffs hk rfl
  · rw [m₃]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show k < n from hk))

/-- The registers and permissions on exit, as on entry. -/
structure Fin (s₀ u : State) : Prop where
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  cs : ∀ r ∈ preserved, u.gpr r = s₀.gpr r

theorem sv_a {s₀ : State} (hp : Pre s₀) : ∀ r ∈ [aR s₀], Region.Disjoint ⟨So s₀ 1680, 24⟩ r :=
  fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hp.d_as.sub_right (sub_so s₀ (by omega))).symm

theorem pres_x34 : ∀ r ∈ preserved, r ∉ [Reg.x3, .x4] := by decide

/-- The registers the setup writes. -/
abbrev setupRegs : List Reg := [Reg.x2, .x3, .x4, .x5, .x9, .x10] ++ ([.x30] ++ [.x25] ++ [.x26])

theorem pres_setup : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → r ∉ setupRegs := by decide

theorem rest_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Mid s₀ s) (hb : Buf s₀ s.mem) :
    WP isa (.seq sampleZero (.block sampleSetup)) s fun u =>
      LPre (Bs s₀) (So s₀ 0) (aP s₀) u ∧ Fin s₀ u := by
  refine WP.seq (WP.seq (wp_movz fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_nil ?_))
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have mid₃ := h.keep k₃ m₃
  have z9 : s₃.gpr .x9 = 0 := by rw [h₃.get .x9, h₂.get .x9, e₁]; rfl
  have i₀ : ZInv s₀ s₃ 0 s₃ := ⟨Keep.refl _ _,
    by rw [h₃.get .x3, e₂, h₁.get .x25, h.x25, coeffAddr, Nat.mul_zero, ptr_zero],
    by rw [e₃]; rfl, CoeffsUpTo.zero _, Frame.refl _ _⟩
  refine WP.mono (count_loop (by decide) (ZInv s₀ s₃) (fun k hk u hu => zero_step hp mid₃.wr z9 hk hu) i₀)
    fun s₄ h₄ => ?_
  have rd₄ : s₄.rd = s₀.rd := by rw [h₄.keep.rd, mid₃.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [h₄.keep.wr, mid₃.wr]
  have sv := mid₃.sv.frame h₄.frame (sv_a hp)
  have in₄ : ∀ {off : Nat}, off + 8 ≤ 2048 → InRegions (s₄.rd ++ s₄.wr) (So s₀ off) 8 :=
    fun h' => by rw [wr₄]; exact in_rd_wr (in_sc hp h')
  refine wp_mov fun s₅ h₅ e₅ => wp_mov fun s₆ h₆ e₆ => wp_movz fun s₇ h₇ e₇ => wp_movz fun s₈ h₈ e₈ =>
    wp_movz fun s₉ h₉ e₉ => wp_movz fun s₁₀ h₁₀ e₁₀ => ?_
  have k₁₀ := ((((h₅.keep.trans h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep
  have m₁₀ : s₁₀.mem = s₄.mem := by rw [h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem]
  have x26 : s₄.gpr .x26 = scP s₀ := by rw [h₄.keep.get .x26, mid₃.x26]
  have x25 : s₄.gpr .x25 = aP s₀ := by rw [h₄.keep.get .x25, mid₃.x25]
  have c26 : s₁₀.gpr .x26 = scP s₀ := by rw [k₁₀.get .x26, x26]
  refine wp_ldrx (a := So s₀ 1696) (by decide) (by rw [c26]) (by rw [k₁₀.rd, k₁₀.wr]; exact in₄ (by omega))
    fun s₁₁ h₁₁ e₁₁ => ?_
  refine wp_ldrx (a := So s₀ 1680) (by decide) (by rw [h₁₁.get .x26, c26])
    (by rw [h₁₁.rd, h₁₁.wr, k₁₀.rd, k₁₀.wr]; exact in₄ (by omega)) fun s₁₂ h₁₂ e₁₂ => ?_
  refine wp_ldrx (a := So s₀ 1688) (by decide) (by rw [h₁₂.get .x26, h₁₁.get .x26, c26])
    (by rw [h₁₂.rd, h₁₂.wr, h₁₁.rd, h₁₁.wr, k₁₀.rd, k₁₀.wr]; exact in₄ (by omega))
    fun s₁₃ h₁₃ e₁₃ => wp_nil ?_
  have k₁₃ := (k₁₀.trans (h₁₁.keep.trans h₁₂.keep)).trans h₁₃.keep
  have m₁₃ : s₁₃.mem = s₄.mem := by rw [h₁₃.mem, h₁₂.mem, h₁₁.mem, m₁₀]
  have hl := h₄.coeffs
  refine ⟨⟨fun p hp' => ?_, fun p hp' => ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ⟨by rw [k₁₃.rd, rd₄], by rw [k₁₃.wr, wr₄], by rw [k₁₃.sp, h₄.keep.sp, mid₃.sp],
      fun r hr => ?_⟩⟩
  · rw [m₁₃, byte_frame h₄.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.d_as.sub_right (sub_so s₀ (by omega))).symm)
      (by decide) hp', m₃, hb p hp']
  · rw [k₁₃.rd, k₁₃.wr, rd₄, wr₄, So, ptr_add, Nat.zero_add]
    exact in_rd_wr (in_sc hp (by omega))
  · rw [k₁₃.wr, wr₄, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ (show i < n from hi))
  · exact (hp.d_as.sub_right (sub_so s₀ (by omega))).symm
  · rw [m₁₃, hl i hi, ite_eq_left hi]
  · rw [h₁₃.get .x2, h₁₂.get .x2, h₁₁.get .x2, h₁₀.get .x2, h₉.get .x2, h₈.get .x2, h₇.get .x2,
      h₆.get .x2, e₅, x26]
    exact (ptr_zero _).symm
  · rw [h₁₃.get .x3, h₁₂.get .x3, h₁₁.get .x3, h₁₀.get .x3, h₉.get .x3, h₈.get .x3, h₇.get .x3, e₆,
      h₅.get .x25, x25]
  · rw [h₁₃.get .x4, h₁₂.get .x4, h₁₁.get .x4, h₁₀.get .x4, h₉.get .x4, h₈.get .x4, e₇]; rfl
  · rw [h₁₃.get .x5, h₁₂.get .x5, h₁₁.get .x5, h₁₀.get .x5, h₉.get .x5, e₈]; rfl
  · rw [h₁₃.get .x9, h₁₂.get .x9, h₁₁.get .x9, h₁₀.get .x9, e₉]; rfl
  · rw [h₁₃.get .x10, h₁₂.get .x10, h₁₁.get .x10, e₁₀]; rfl
  · by_cases h30 : r = .x30
    · subst h30; rw [h₁₃.get .x30, h₁₂.get .x30, e₁₁, m₁₀]; exact sv.2.2
    by_cases h25 : r = .x25
    · subst h25; rw [h₁₃.get .x25, e₁₂, h₁₁.mem, m₁₀]; exact sv.1
    by_cases h26 : r = .x26
    · subst h26; rw [e₁₃, h₁₂.mem, h₁₁.mem, m₁₀]; exact sv.2.1
    rw [k₁₃.gpr r (pres_setup r hr h25 h26 h30), h₄.keep.gpr r (pres_x34 r hr),
      mid₃.cs r hr h25 h26 h30]

end VG.Proof.MlKem.AArch64.Sample
