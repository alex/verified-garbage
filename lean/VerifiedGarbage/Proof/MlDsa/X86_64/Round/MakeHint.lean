import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint

/-!
# ML-DSA on x86-64: `vg_mldsa_make_hint`

Untrusted: everything here is checked by Lean. The loop also counts the 1s
in `r9` (`onesFrom`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)

/-! ## The body -/

/-- `r₁` of `r + z mod q`. -/
def mhS (g : Nat) (z r : BitVec 32) : BitVec 64 :=
  hbV g (condAddV (BitVec.setWidth 64 (r + z)) (BitVec.signExtend 64 qImm) qImm)

/-- The hint bit: whether `r₁` of `r` and of `r + z` differ. -/
def mhB (g : Nat) (z r : BitVec 32) : BitVec 64 :=
  ((mhS g z r ^^^ hbV g (BitVec.setWidth 64 r)) + BitVec.signExtend 64 (63 : BitVec 32)) >>> 6

theorem mhBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h1' : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rsi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (mhBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
          (BitVec.setWidth 32 (mhB g (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)
            (s.mem.readW (cfAddr (s.gpr .rsi) (s.gpr .rcx)) 32))) ∧
        s'.gpr .r9 = s.gpr .r9 + mhB g (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)
          (s.mem.readW (cfAddr (s.gpr .rsi) (s.gpr .rcx)) 32) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .r9, .r11, .rcx] s s' := by
  refine WP.keep _ ?_ (by rcases hg with rfl | rfl <;> decide)
  unfold mhBody hb hbRaw condAdd
  xrun [h1, h1', h2, ea_cf, List.cons_append, List.nil_append, mhB, mhS, hbV, hbRawV, condAddV, dShift_ge,
    dShift_le]
  exact ⟨rfl, rfl⟩

/-! ## The value -/

theorem xor_eq_zero {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  have : x ^^^ (x ^^^ y) = y := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [h, Nat.xor_zero] at this
  exact this

theorem mhB_toNat {g : Nat} (h : g ∈ gamma2s) {z r : BitVec 32} (hz : z.toNat < q) (hr : r.toNat < q) :
    (mhB g z r).toNat = (makeHint g (Fin.ofNat q z.toNat) (Fin.ofNat q r.toNat)).toNat := by
  have hr' : (BitVec.setWidth 64 r).toNat < q := by rw [setWidth64_toNat]; exact hr
  have hq : qImm = BitVec.ofNat 32 q := rfl
  have e1 : (BitVec.setWidth 64 (r + z)).toNat = r.toNat + z.toNat := by
    rw [setWidth64_toNat, BitVec.toNat_add]; rw [q_eq] at hz hr; omega
  have e2 : (condAddV (BitVec.setWidth 64 (r + z)) (BitVec.signExtend 64 qImm) qImm).toNat =
      (r.toNat + z.toNat) % q := by
    rw [hq, condAddV_imm_toNat (by decide) (by rw [e1]; omega), e1]
  have hs : (condAddV (BitVec.setWidth 64 (r + z)) (BitVec.signExtend 64 qImm) qImm).toNat < q := by
    rw [e2]; exact Nat.mod_lt _ (by decide)
  have hM : Proof.MlDsa.Round.hbM g ≤ 44 ∧ 0 < Proof.MlDsa.Round.hbM g := by
    rcases mem_gamma2s h with rfl | rfl <;> decide
  have hu := Nat.mod_lt (hbF g ((r.toNat + z.toNat) % q)) hM.2
  have hv := Nat.mod_lt (hbF g r.toNat) hM.2
  have hx : hbF g ((r.toNat + z.toNat) % q) % Proof.MlDsa.Round.hbM g ^^^ hbF g r.toNat % Proof.MlDsa.Round.hbM g
      < 2 ^ 6 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hvz : (Fin.ofNat q z.toNat).val = z.toNat := Nat.mod_eq_of_lt hz
  have hvr : (Fin.ofNat q r.toNat).val = r.toNat := Nat.mod_eq_of_lt hr
  rw [makeHint_eq h, hvz, hvr, mhB, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_xor, mhS,
    hbV_toNat h hs, hbV_toNat h hr', e2, setWidth64_toNat, show (BitVec.signExtend 64 (63 : BitVec 32)).toNat = 63
      by decide, Nat.shiftRight_eq_div_pow]
  by_cases e : hbF g r.toNat % Proof.MlDsa.Round.hbM g = hbF g ((r.toNat + z.toNat) % q) % Proof.MlDsa.Round.hbM g
  · rw [decide_eq_false (fun h' => h' e), e, Nat.xor_self]; rfl
  · rw [decide_eq_true e]
    have : hbF g ((r.toNat + z.toNat) % q) % Proof.MlDsa.Round.hbM g ^^^ hbF g r.toNat % Proof.MlDsa.Round.hbM g ≠ 0 :=
      fun h' => e (xor_eq_zero h').symm
    show _ = 1
    omega

/-! ## The function -/

theorem mhPrologue_ok (s : State) :
    WP isa (.block (gammaCmp .rdx ++ ([.mov .r10 (.reg .rcx), .mov32 .r9 (.imm 0)] : List Instr))) s fun s' =>
      (s'.gpr .r10 = s.gpr .rcx ∧ s'.gpr .r9 = 0 ∧
        s'.zf = some (BitVec.setWidth 32 (s.gpr .rdx) - BitVec.ofNat 32 g32 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.rdx, .r10, .r9] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold gammaCmp
  xrun [List.cons_append, List.nil_append]

theorem mhEpilogue_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .r9)]) s fun s' => (s'.gpr .rax = s.gpr .r9 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

section
variable {s₀ : State} (hp : makeHintK.pre s₀)
include hp

/-- The hint of the polynomials at `z` and `r`, for `γ₂ = g`. -/
abbrev mhHint (s₀ : State) (g : Nat) : Vector Bool n :=
  Vector.zipWith (makeHint g) (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi))

theorem mh_loop {g : Nat} (hge : arg32 s₀ .rdx = g) {s₁ : State} (h10 : s₁.gpr .r10 = s₀.gpr .rcx)
    (h9 : s₁.gpr .r9 = 0) (hk : Keep [.rdx, .r10, .r9] s₀ s₁) (hm : s₁.mem = s₀.mem) :
    WP isa (mapLoop (mhBody g)) s₁ (Inv s₁ [.r10, .rdi, .rsi] [.r10]
      (fun _ k => BitVec.setWidth 32 (mhB g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)))
      (fun i s => (s.gpr .r9).toNat = onesFrom (mhHint s₀ g) (256 - i)) 256) := by
  have hg : g ∈ gamma2s := hge ▸ hp.2.2.2.2.2.2.2.1
  have hg' : g = g32 ∨ g = g88 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hdi : s₁.gpr .rdi = s₀.gpr .rdi := hk.gpr (by decide)
  have hsi : s₁.gpr .rsi = s₀.gpr .rsi := hk.gpr (by decide)
  have hL : Layout s₁ [.rdi, .rsi] [.r10] :=
    { rd := fun p h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rw [hk.2.1, hk.2.2, hp.1]; rcases h with rfl | rfl <;> simp [hdi, hsi]
      wr := fun o h => by
        simp only [List.mem_singleton] at h; subst h; rw [hk.2.2, hp.2.1, h10]; simp
      dis := fun p hp' o ho => by
        simp only [List.mem_singleton] at ho; subst ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rw [h10]; rcases hp' with rfl | rfl
        exacts [hdi ▸ hp.2.2.1, hsi ▸ hp.2.2.2.1]
      pw := List.pairwise_singleton _ _ }
  have hz : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2.2.2.1
  have hr : Reduced s₀.mem (s₀.gpr .rsi) := hp.2.2.2.2.2.2.2.2.2
  refine loop_ok (clob := [.rax, .rdx, .r8, .r9, .r11, .rcx]) hL (by decide) (by decide) (fun s _ _ hk' => ?_)
    fun i hi s hI hc => ?_
  · rw [hk'.gpr (by decide), h9, onesFrom_n]; rfl
  · have ha : ∀ p ∈ [Reg.r10, .rdi, .rsi], cfAddr (s.gpr p) (s.gpr .rcx) = coeffAddr (s₁.gpr p) (255 - i) :=
      fun p hp' => hI.addr hc hi hp'
    refine WP.mono (mhBody_ok hg' s (by rw [ha _ (by simp)]; exact hI.inR hL (by simp) (by omega))
      (by rw [ha _ (by simp)]; exact hI.inR hL (by simp) (by omega))
      (by rw [ha _ (by simp)]; exact hI.inW hL (by simp) (by omega)))
      fun s' ⟨⟨hm', h9', hc', hz'⟩, hk'⟩ => ⟨⟨?_, hc', hz', ?_⟩, hk'⟩
    · rw [hm', ha _ (by simp), ha _ (by simp), ha _ (by simp), hI.read hL (by simp) (by omega),
        hI.read hL (by simp) (by omega), hm, hdi, hsi]
      rfl
    · have hk255 : 255 - i < n := by rw [n_eq]; omega
      rw [h9', ha _ (by simp), ha _ (by simp), hI.read hL (by simp) (by omega), hI.read hL (by simp) (by omega),
        hm, hdi, hsi, BitVec.toNat_add, hI.j, mhB_toNat hg (hz _ hk255) (hr _ hk255),
        show 256 - (i + 1) = 255 - i by omega, onesFrom_step _ hk255, show 255 - i + 1 = 256 - i by omega, zipWith_get _ _ _ hk255,
        polyAt_get _ _ hk255, polyAt_get _ _ hk255]
      have : onesFrom (mhHint s₀ g) (256 - i) ≤ 256 := by
        unfold onesFrom; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have := Bool.toNat_le (makeHint g (Fin.ofNat q (coeffAt s₀.mem (s₀.gpr .rdi) (255 - i)).toNat)
        (Fin.ofNat q (coeffAt s₀.mem (s₀.gpr .rsi) (255 - i)).toNat))
      omega

theorem mh_correct : ∃ t s', Exec isa makeHint s₀ t s' ∧ abiPreserved s₀ s' ∧ makeHintK.post s₀ s' := by
  have hg : arg32 s₀ .rdx ∈ gamma2s := hp.2.2.2.2.2.2.2.1
  have hz : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2.2.2.1
  have hr : Reduced s₀.mem (s₀.gpr .rsi) := hp.2.2.2.2.2.2.2.2.2
  have go : ∀ g, arg32 s₀ .rdx = g → ∀ s₁ : State, s₁.gpr .r10 = s₀.gpr .rcx → s₁.gpr .r9 = 0 →
      Keep [.rdx, .r10, .r9] s₀ s₁ → s₁.mem = s₀.mem →
      WP isa (.seq (mapLoop (mhBody g)) (.block [.mov .rax (.reg .r9)])) s₁ fun s' =>
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k = BitVec.setWidth 32 (mhB (arg32 s₀ .rdx)
          (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k))) ∧
        (s'.gpr .rax).toNat = onesFrom (mhHint s₀ (arg32 s₀ .rdx)) 0 ∧ Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
    intro g hge s₁ h10 h9 hk hm
    subst hge
    refine WP.seq (WP.mono (mh_loop hp rfl h10 h9 hk hm) fun s₂ hI => ?_)
    refine WP.mono (mhEpilogue_ok s₂) fun s' ⟨⟨hax, hm'⟩, _⟩ => ⟨fun k hk' => ?_, ?_, ?_⟩
    · rw [hm', ← h10]; exact hI.done .r10 (by simp) k (by omega) hk'
    · rw [hax, hI.j]
    · have := hI.frame
      rw [hm, List.map_singleton, h10] at this
      rw [hm']; exact this
  have wp : WP isa makeHint s₀ fun s' =>
      (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k = BitVec.setWidth 32 (mhB (arg32 s₀ .rdx)
        (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k))) ∧
      (s'.gpr .rax).toNat = onesFrom (mhHint s₀ (arg32 s₀ .rdx)) 0 ∧ Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
    refine WP.seq (WP.mono (mhPrologue_ok s₀) fun s₁ ⟨⟨h10, h9, hzf, hm⟩, hk⟩ => ?_)
    have e : ∀ {A B C : Prog isa} {s : State} {Q : State → Prop}, WP isa (.ite .e (.seq A C) (.seq B C)) s Q →
        WP isa (.seq (.ite .e A B) C) s Q := fun h => by
      obtain ⟨t, s', he, hq⟩ := h
      cases he with
      | iteT hc h' =>
        cases h' with
        | seq h₁ h₂ => exact ⟨_, s', .seq (.iteT hc h₁) h₂, hq⟩
      | iteF hc h' =>
        cases h' with
        | seq h₁ h₂ => exact ⟨_, s', .seq (.iteF hc h₁) h₂, hq⟩
    refine e (WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hzf) (fun h => ?_) (fun h => ?_))
    · rw [sub_beq_zero32, decide_eq_true_eq] at h
      exact go _ ((gamma_cases hg).1 h) s₁ h10 h9 hk hm
    · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
      exact go _ ((gamma_cases hg).2 h) s₁ h10 h9 hk hm
  obtain ⟨t, s', he, ⟨hv, hax, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] wp (by decide)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_, ?_⟩
  · simpa using hp.2.2.2.2.2.2.1
  · refine hintIs_of_toNat fun k hk' => ?_
    apply BitVec.eq_of_toNat_eq
    rw [hv k hk', BitVec.toNat_setWidth, mhB_toNat hg (hz k hk') (hr k hk'), zipWith_get _ _ _ hk',
      polyAt_get _ _ hk', polyAt_get _ _ hk']
    simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  · have : (s'.gpr .rax).toNat ≤ 256 := by
      rw [hax]; unfold onesFrom; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    rw [BitVec.toNat_setWidth, hintOnes_single, ← hax]
    omega

end

theorem makeHint_ct : ConstantTime isa makeHintK.pre makeHintK.pub makeHint :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

theorem makeHint_verified : Verified X86_64.target makeHint (makeHintContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => mh_correct hp) makeHint_ct (by
    round_implies [makeHintContract, makeHintSig, makeHintK, hintK, X86_64.abi, X86_64.argRegs] [hintSat]
      using hintSat)

end VG.Proof.MlDsa.X86_64.Round
