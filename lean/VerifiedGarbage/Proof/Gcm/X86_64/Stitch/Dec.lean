import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc

/-!
# Interleaved counter mode and GHASH: decryption

`DInv s₀ e s`: `e` groups are decrypted (`AInv`) and hashed into `Y` (the
blocks as they were: the ciphertext); `rdx` points to group `e`. `dbody_ok`:
a body hashes group `e` while it decrypts it, reading blocks 0–7 during the
rounds of the first batch, before it overwrites them, and blocks 8–15 during
those of the second.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs batch dA dB dbody gq ordD storeCtr storeY dec)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

structure DInv (s₀ : State) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2,
    x * φ (s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128) = φ (hk s₀) ^ (16 - 2 * k - l)
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  y1 : s.lane .xmm2 1 = 0

/-- The end of a decryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 16`. -/
theorem nextD_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 16)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- Which blocks of the group the GHASH loads to come still read: in the first
batch, all until its loads are done, then those the second batch reads. -/
abbrev loA (j : Nat) : Nat := if j < 5 then 0 else 8
abbrev loB (j : Nat) : Nat := if j < 5 then 8 else 16

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State}
    (hI : DInv s₀ e s) :
    WP isa dbody s fun s' => DInv s₀ (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => blk s₀ (16 * e + i)
  let P : Nat → Nat → Block := fun k l => s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := hI.pw
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  have hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
        rfl
      pv := fun k _ l _ => by rw [f₁.mem]
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = dp s₀ + BitVec.ofNat 64 (256 * e + 32 * k) from addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  -- The first batch decrypts blocks 0–7 of the group, hashing them (the product with `Y` last).
  refine WP.seq (WP.mono (batch_ok hp dA gRegs gRegs_ok (QG s₀ loA a X P yl ordD 0 false)
    (gq_ok (fun j => by simp only [loA]; split <;> split <;> omega) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha
      (fun i hi _ => by have : 8 ≤ i := hi; omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega) hA₁ (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  have hQ₂' : QG s₀ loB a X P yl ordD 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [ite_f (by decide)]; exact h2⟩
  -- The second batch decrypts blocks 8–15, hashing them, then reduces.
  refine WP.seq (WP.mono (batch_ok hp dB gRegs gRegs_ok (QG s₀ loB a X P yl ordD 4 true)
    (gq_ok (fun j => by simp only [loB]; split <;> split <;> omega) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha
      (fun i hi hi' => by have : 16 ≤ i := hi; omega) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 4) (by omega) hA₂ (by rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega) hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (nextD_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [ite_t ⟨rfl, by decide⟩] at h2
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
  have hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [keepP k hk l hl]; exact hP k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (yNew_eq (hk s₀) X P yl ordD (finD (hk s₀) X P yl hI.y1 hP)).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega)]

theorem dfinal_ok {s₀ : State} (hp : SPre s₀) {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : DInv s₀ e s) :
    WP isa (.block (storeCtr ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₁ (by rw [l₁ _ (by decide) 0 (by decide)]; exact hm0)
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₁, hrcx, m₁, l₁ _ (by decide) 0 (by decide)] at m₂
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < nb s₀, blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₂, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show blockAt s₂.mem (cp s₀) = _
    rw [m₂, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide),
      Nat.add_zero, he]
  · show blockAt s₂.mem (yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4

/-- The decryption of `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPre s₀) : WP isa dec s₀ (DPost s₀) := by
  have hm := hp.nbm
  have h16 := hp.nb16
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ hR => ?_)
  have hI₁ : DInv s₀ 0 s₁ :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInv s₀ e s
  have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ DInv s₀ e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (dbody_ok hp he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI'⟩
  exact WP.seq (WP.mono (WP.loop (M := isa) I hstep (nb s₀) s₁ ⟨0, by simp, by omega, hI₁⟩)
    fun s₂ ⟨e, he, hI₂⟩ => dfinal_ok hp he hI₂)

/-- Both interleaved loops meet their contracts. -/
theorem stitch_ok : StitchOk := ⟨fun _ hp => enc_ok hp, fun _ hp => dec_ok hp⟩

end VG.Proof.Gcm.X86_64.Stitch
