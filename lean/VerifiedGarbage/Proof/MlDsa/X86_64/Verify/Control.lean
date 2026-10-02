import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top

/-!
# ML-DSA verification on x86-64: branches, sequences and the comparison

The branch on the result in `r15` (`ifOk_ok`, `ifOk_tr`), sequences of pieces
indexed by a number (`seqR_ok`, `seqR_tr`), and the comparison of `c̃′` with
`c̃` without a branch (`cmpAnd_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The branch on `r15` -/

theorem test15_ok (s : State) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => PPostB s s₁ [] ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) :=
  WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun _ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _), h15,
      by rw [hz, BitVec.and_self]⟩

theorem flag_sw (p : Prop) [Decidable p] : ((flag p).setWidth 32 == 0) = !decide p := by
  unfold flag; by_cases h : p <;> simp [h]

theorem ifOk_ok {c : Prog isa} {s : State} {Q : State → Prop} {p : Prop} [Decidable p] (h15 : s.gpr .r15 = flag p)
    (ht : ∀ s₁, PPostB s s₁ [] → s₁.gpr .r15 = s.gpr .r15 → p → WP isa c s₁ Q)
    (he : ∀ s₁, PPostB s s₁ [] → s₁.gpr .r15 = s.gpr .r15 → ¬ p → Q s₁) : WP isa (ifOk c) s Q := by
  unfold ifOk
  refine WP.seq (WP.mono (test15_ok s) fun s₁ ⟨hP, h15', hz⟩ => ?_)
  rw [h15, flag_sw] at hz
  refine WP.ite (M := isa) (decide p) (show s₁.zf.map (!·) = _ by rw [hz]; simp) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP h15' (by simpa using hb)
  · exact WP.block_nil (he s₁ hP h15' (by simpa using hb))

theorem ifOk_tr {c : Prog isa} {P Q : State → State → Prop}
    (he : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ PPostB x₀ x [] ∧ PPostB y₀ y [] ∧
      x.gpr .r15 = x₀.gpr .r15 ∧ y.gpr .r15 = y₀.gpr .r15 ∧ (x₀.gpr .r15).setWidth 32 ≠ 0) c Q)
    (hq : ∀ x y, (∃ x₀ y₀, P x₀ y₀ ∧ PPostB x₀ x [] ∧ PPostB y₀ y [] ∧
      x.gpr .r15 = x₀.gpr .r15 ∧ y.gpr .r15 = y₀.gpr .r15 ∧ (x₀.gpr .r15).setWidth 32 = 0) → Q x y) :
    RelCT isa P (ifOk c) Q := by
  unfold ifOk
  refine RelCT.seq (RelCT.postDep (block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => PPostB x x₁ [] ∧ x₁.gpr .r15 = x.gpr .r15 ∧ x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨test15_ok x, test15_ok y⟩) (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      (PPostB x₀ x₁ [] ∧ x₁.gpr .r15 = x₀.gpr .r15 ∧ x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      (PPostB y₀ y₁ [] ∧ y₁.gpr .r15 = y₀.gpr .r15 ∧ y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, he x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, e1, hx⟩, ⟨h2, e2, _⟩⟩, hc⟩ =>
      ⟨x₀, y₀, hp, h1, h2, e1, e2, ?_⟩) fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono nil_tr (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, e1, hx⟩, ⟨h2, e2, _⟩⟩, hc⟩ =>
      ⟨x₀, y₀, hp, h1, h2, e1, e2, ?_⟩) fun x y h => hq x y h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))


/-! ## The comparison -/

theorem sbb_val (x r : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 r &&&
      BitVec.setWidth 32 (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < (1 : BitVec 64).toNat))))) =
    if x = 0 then BitVec.setWidth 64 (BitVec.setWidth 32 r) else 0 := by
  by_cases h : x = 0
  · subst h
    rw [ifp rfl, show decide ((0 : BitVec 64).toNat < (1 : BitVec 64).toNat) = true by decide,
      show BitVec.setWidth 32 (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 32 by decide,
      BitVec.and_allOnes]
  · rw [ifn h, show decide (x.toNat < (1 : BitVec 64).toNat) = false by
      simp only [decide_eq_false_iff_not]; intro h'; exact h (BitVec.eq_of_toNat_eq (by simp at h' ⊢; omega))]
    apply BitVec.eq_of_toNat_eq; simp

theorem cmpEnd_ok (s : State) :
    WP isa (.block (([.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++ and15)) s fun s' =>
      (s'.gpr .r15 = (if s.gpr .rdx = 0 then BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) else 0) ∧
        s'.mem = s.mem) ∧ Keep [.rdx, .rax, .r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold and15
  xrun [List.cons_append, List.nil_append]
  exact sbb_val _ _



theorem cmpBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) :
    WP isa cmpBody s fun s' =>
      (s'.gpr .rdx = s.gpr .rdx ||| (BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^ BitVec.setWidth 64 (s.mem (s.gpr .rdi))) ∧
        s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold cmpBody
  xrun [h0, h1]

theorem or_xor_zero {d : BitVec 64} {x y : Byte} :
    (d ||| (BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) = 0) ↔ d = 0 ∧ x = y := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => h ▸ rfl⟩
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have hx := x.isLt; have hy := y.isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- `r15 ← 0` unless the `n` bytes at `a` and `b` are equal. -/
theorem cmpAnd_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a b : Ptr} {n : Nat} (hn : 0 < n)
    (ha : inB (rbs ++ wbs) a n = true) (hb : inB (rbs ++ wbs) b n = true) {P : Prop} [Decidable P]
    (h15 : s.gpr .r15 = flag P) :
    WP isa (cmpAnd a b n) s fun s' => PPostB s s' [] ∧
      s'.gpr .r15 = flag (P ∧ bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n) := by
  have hS := L.ok
  have hn' : n < 2 ^ 31 := by obtain ⟨m, hm, hl⟩ := inB_spec ha; have := (hS _ hm).1; omega
  have hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)),
      x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS ha, by decide⟩, ⟨ptr_ok hS hb, by decide⟩, ⟨hn', by decide⟩⟩
  have ra := L.inR ha
  have rb := L.inR hb
  unfold cmpAnd
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s1 h1 => ?_
  refine WP.mono (WP.keep [.rdx] (Q := fun s₂ => s₂.mem = s1.mem ∧ s₂.gpr .rdx = 0) (by xrun) (by decide))
    fun s2 ⟨⟨hm2, hd2⟩, k2⟩ => ?_
  have k12 : Keep argRegs s s2 := (h1.2.trans k2).mono (by simp)
  have hm12 : s2.mem = s.mem := hm2.trans h1.1.2
  have ea : s2.gpr .rsi = pa s a := by rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_self ..)
  have eb : s2.gpr .rdi = pa s b := by
    rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have ec : s2.gpr .rcx = BitVec.ofNat 64 n := by
    rw [k2.gpr (by decide)]
    exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine WP.seq (WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega) hn (fun k s' =>
      s'.gpr .rsi = pa s a + BitVec.ofNat 64 k ∧ s'.gpr .rdi = pa s b + BitVec.ofNat 64 k ∧ s'.mem = s.mem ∧
      (s'.gpr .rdx = 0 ↔ ∀ j < k, s.mem (pa s a + BitVec.ofNat 64 j) = s.mem (pa s b + BitVec.ofNat 64 j)) ∧
      Keep argRegs s s')
    (fun k hk s' ⟨hsi, hdi, hm, hd, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [ea]; simp, by rw [eb]; simp, hm12, by rw [hd2]; simp, k12⟩ ec)
    fun s3 ⟨_, _, hm3, hd3, k3⟩ => ?_)
  · refine WP.mono (cmpBody_ok s' (by rw [kk.2.1, kk.2.2, hsi]; exact inRegions_byte ra hk (by omega))
      (by rw [kk.2.1, kk.2.2, hdi]; exact inRegions_byte rb hk (by omega)))
      fun s'' ⟨⟨hd', hsi', hdi', hcx, hz, hm'⟩, k'⟩ => ⟨⟨?_, ?_, hm'.trans hm, ?_, (kk.trans k').mono (by simp)⟩, hcx, hz⟩
    · rw [hsi', hsi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [hdi', hdi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [hd', or_xor_zero, hd, hsi, hdi, hm]
      constructor
      · rintro ⟨h, e⟩ j hj
        rcases (by omega : j < k ∨ j = k) with hj | rfl
        · exact h j hj
        · exact e
      · intro h; exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · refine WP.mono (cmpEnd_ok s3) fun s4 ⟨⟨h15', hm4⟩, k4⟩ => ⟨?_, ?_⟩
    · exact postB_of_keep (k3.trans k4) (by decide) (by rw [hm4, hm3]; exact Frame.refl _ _)
    · have hr15 : s3.gpr .r15 = flag P := by rw [k3.gpr (by decide), h15]
      rw [h15', hr15]
      have heq : (s3.gpr .rdx = 0) ↔ bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n := by
        rw [hd3]
        constructor
        · intro h; simp only [bytesAt]; exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)
        · intro h j hj
          have := congrArg (fun l => l.getD j 0) h
          rwa [Proof.MlKem.bytesAt_getD _ _ hj, Proof.MlKem.bytesAt_getD _ _ hj] at this
      by_cases hd : s3.gpr .rdx = 0
      · rw [ifp hd]
        have he := heq.mp hd
        by_cases hP : P <;> simp [flag, hP, he]
      · rw [ifn hd]
        have he : ¬ bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n := fun e => hd (heq.mpr e)
        simp [flag, he]

end VG.Proof.MlDsa.X86_64.Verify
