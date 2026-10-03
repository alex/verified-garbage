import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group

/-!
# Interleaved counter mode and GHASH: the encryption loop

`EInv s₀ e s`: `e` groups of sixteen blocks are encrypted (`AInv`), the first
`e - 1` hashed into `Y` (in `xmm2`), the powers in the working space; `rdx`
points to group `e - 1`, the next to hash. `body_ok`: a body encrypts group
`e` (two batches, `batch_ok`) while it hashes group `e - 1` between their
rounds (`gq_ok`), which they do not write (`QG.data`).
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs batch gA gB body gq ordE)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep)
open VG.Spec.Gcm (Block blockAt ghashFrom mul inc32)

/-! ## `GHASH` over the groups -/

theorem ghash_append16 (h y : Block) (f : Nat → Block) (g : Nat) :
    ghashFrom h y ((List.range (16 * (g + 1))).map f) =
      ghashFrom h (ghashFrom h y ((List.range (16 * g)).map f)) ((List.range 16).map fun i => f (16 * g + i)) := by
  rw [show 16 * (g + 1) = 16 * g + 16 by omega, List.range_add, List.map_append, List.map_map]
  simp only [ghashFrom, List.foldl_append]
  rfl

theorem ghash16 (h y : Block) (X : Nat → Block) :
    ghashFrom h y ((List.range 16).map X) = mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((y ^^^ X 0)) h ^^^ X 1) h ^^^ X 2) h ^^^ X 3) h ^^^ X 4) h ^^^ X 5) h ^^^ X 6) h ^^^ X 7) h ^^^ X 8) h ^^^ X 9) h ^^^ X 10) h ^^^ X 11) h ^^^ X 12) h ^^^ X 13) h ^^^ X 14) h ^^^ X 15) h := by
  simp only [ghashFrom, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `Y` after a body: `GHASH` continued over its sixteen blocks. -/
theorem yNew_eq (H : Block) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (ord : Nat → Nat)
    (hfin : reduce (accN ord X P yl 0 8) ^^^ reduce (accN ord X P yl 1 8) = mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H) :
    yNew ord X P yl = ghashFrom H (yl 0) ((List.range 16).map X) := by
  rw [ghash16]; exact hfin

/-! ## The GHASH state, kept by the data written -/

theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 8 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 8))
    {t t' : State} (h : QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨bAddr s₀ c, 128⟩] t.mem t'.mem) : QG s₀ lo a X P yl ord base fin j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  have kp : ∀ l < 2, prod (t'.proj l) = prod (t.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) l hl, hlane .xmm9 (by decide) (by decide) l hl,
      hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega) hc (hsep i hi hi') h₁ h₂]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        by rw [hlane _ (by decide) (by decide) 1 (by decide)]; exact h2.2⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-! ## The encryption loop -/

structure EInv (s₀ : State) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2,
    x * φ (s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128) = φ (hk s₀) ^ (16 - 2 * k - l)
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : s.lane .xmm2 1 = 0

/-- The end of a body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 32`. -/
theorem nextE_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 32)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, e32,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

theorem body_ok {s₀ : State} (hp : SPre s₀) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State}
    (hI : EInv s₀ e s) :
    WP isa body s fun s' => EInv s₀ (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let P : Nat → Nat → Block := fun k l => s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := hI.pw
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  have hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k _ l _ => by rw [f₁.mem]
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hrdx₁ : (s₁.gpr .rdx).toNat + 32 * 8 = (dp s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega
  have hsepA : ∀ c, 16 * e ≤ c → ∀ i, 0 ≤ i → i < 16 → ¬ (c ≤ 16 * (e - 1) + i ∧ 16 * (e - 1) + i < c + 8) :=
    fun c hc i _ hi => by omega
  -- The first batch, with loads 1–4 of the previous group.
  refine WP.seq (WP.mono (batch_ok hp gA gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 0 false)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha (hsepA _ (Nat.le_refl _)) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 8) (by omega) hA₁ hrdx₁
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  have hrdx₂ : (s₂.gpr .rdx).toNat + 32 * 12 = (dp s₀).toNat + 16 * (16 * e + 8) := by
    rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega
  have hQ₂' : QG s₀ (fun _ => 0) a X P yl ordE 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [ite_f (by decide)]; exact h2⟩
  -- The second batch, with loads 5–7 and 0 of the previous group, and the reduction.
  refine WP.seq (WP.mono (batch_ok hp gB gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 4 true)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha (hsepA _ (by omega)) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 12) (by omega) hA₂ hrdx₂ hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (nextE_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [ite_t ⟨rfl, by decide⟩] at h2
  -- The memory of the powers is kept.
  have dP : ∀ c, c + 8 ≤ nb s₀ → ∀ r' ∈ [(⟨bAddr s₀ c, 128⟩ : Region)], (pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))
  have keepP : ∀ k < 8, ∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l :=
    fun k hk l hl => by
      rw [fm, hm₃.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide),
        hm₂.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide), f₁.mem]
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (by simp only [gRegs, List.mem_cons, not_or] at hg' ⊢; simp_all) l hl]
  have hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fm]; exact hA₃.frame,
      fun k hk => by rw [fm]; exact hA₃.blocks k hk, by rw [frd]; exact hA₃.rd, by rw [fwr]; exact hA₃.wr⟩
  have hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [keepP k hk l hl]; exact hP k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, yNew_eq (hk s₀) X P yl ordE (finE (hk s₀) X P yl hI.y1 hP),
      show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

end VG.Proof.Gcm.X86_64.Stitch
