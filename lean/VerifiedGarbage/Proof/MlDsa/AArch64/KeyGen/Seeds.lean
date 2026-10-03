import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inv

/-!
# ML-DSA key generation on AArch64: the prologue and the seeds

The prologue saves the caller's registers and keeps the pointers
(`pro_piece`); then `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)` to `HX`, `ρ` to the seed
of `RejNTTPoly` and `ρ′ ‖ 0` to that of `RejBoundedPoly` (`seeds_piece`,
`K1`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Keep pbytes)
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

theorem PPostB.app {S : Nat} {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : PPostB S s s₁ ws₁)
    (h₂ : PPostB S s₁ s₂ ws₂) (hc : ∀ w ∈ ws₂, w.1.1 ∈ keptRegs) : PPostB S s s₂ (ws₁ ++ ws₂) :=
  PPostB.trans h₁ h₂ hc (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)

theorem sc_bases (ws : List (Ptr × Nat)) (h : ∀ w ∈ ws, w.1.1 = .x28) : ∀ w ∈ ws, w.1.1 ∈ keptRegs :=
  fun w hw => by rw [h w hw]; decide

/-! ## The prologue -/

theorem scr_ge {p : Params} (hF : PFacts p) : 1024 * 32 ≤ scrLen p := by rw [scr_eq]; have := hF.k; omega

theorem pro_piece {p : Params} (hF : PFacts p) {S : Nat} :
    Piece p S (fun σ s => s = σ) (fun σ s => KC p σ s ∧ s.gpr .x24 = 1) (.block pro) := by
  refine ⟨fun σ s hp hs => ?_, taintRel [.x0, .x1, .x2, .x3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · subst hs
    have hp' := hp
    unfold kgPre at hp'
    sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at hp'
    obtain ⟨_, _, hwr, _, _, d03, _⟩ := hp'
    have hsc : 1024 * 32 ≤ Spec.MlDsa.scratchWords p * 8 := scr_ge hF
    have hin : ∀ k < 6, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 := fun k hk =>
      ⟨⟨s.gpr .x3, Spec.MlDsa.scratchWords p * 8⟩, by rw [hwr]; simp, Offset.contains_base _ (by simp only [SV]; omega) (by simp only [SV]; omega)⟩
    refine WP.mono (pro_ok hin) fun s' ⟨ht, h24, hf⟩ => ⟨⟨ht, ?_⟩, h24⟩
    rw [pa, ht.x25, BitVec.add_zero]
    exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact d03.sub_right (Offset.sub_base _ (by simp only [SV]; omega))) (by decide)
  · subst h₁ h₂
    obtain ⟨esp, _, e0, e1, e2, e3⟩ := kgPub_eq pub
    refine ⟨esp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-! ## The seeds -/

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte :=
  Spec.MlDsa.H (xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds. -/
structure K1 (p : Params) (σ s : State) : Prop where
  kc : KC p σ s
  hx : bytesAt s.mem (pa s (sc oHX)) 128 = hxOf p σ
  sa : bytesAt s.mem (pa s (sc oSA)) 32 = rhoOf p σ
  sb : bytesAt s.mem (pa s (sc oSB)) 64 = rho'Of p σ
  z : bytesAt s.mem (pa s (sc (oSB + 65))) 1 = [0]

/-- A piece that writes `ws` keeps `K1`. -/
def k1Chk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  kcChk p ws && keepB kgR (kgW p) ws (sc oHX) 128 && keepB kgR (kgW p) ws (sc oSA) 32 &&
    keepB kgR (kgW p) ws (sc oSB) 64 && keepB kgR (kgW p) ws (sc (oSB + 65)) 1

theorem K1.step {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ) {s s' : State}
    (h : K1 p σ s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : k1Chk p ws = true) : K1 p σ s' := by
  simp only [k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP h0, by rw [L.keepBytes hP h1]; exact h.hx, by rw [L.keepBytes hP h2]; exact h.sa,
    by rw [L.keepBytes hP h3]; exact h.sb, by rw [L.keepBytes hP h4]; exact h.z⟩

theorem rho_eq (p : Params) (σ : State) : rhoOf p σ = (hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : rho'Of p σ = ((hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : kOf p σ = ((hxOf p σ).drop 96).take 32 := rfl

theorem bytesAt_two (m : Mem) (a : Addr) (x y : Byte) :
    bytesAt ((m.writeW a x).writeW (a + BitVec.ofNat 64 1) y) a 2 = [x, y] := by
  have hne : a + BitVec.ofNat 64 0 ≠ a + BitVec.ofNat 64 1 :=
    Offset.add_ofNat_ne a (by decide) (by decide) (by decide)
  show [_, _] = _
  dsimp only
  rw [Proof.MlKem.writeW8_apply, Proof.MlKem.writeW8_apply, Proof.MlKem.writeW8_apply,
    Proof.MlDsa.KeyGen.ifn hne, Proof.MlDsa.KeyGen.ifp (Proof.MlKem.AArch64.ptr_zero a),
    Proof.MlDsa.KeyGen.ifp rfl]

theorem setTwo_ok {p : Params} {S : Nat} {s : State} (L : Lay S kgR (kgW p) s) {o a b : Nat}
    (ho : o + 1 < 4096) (h1 : inB (kgW p) (sc o) 1 = true) (h2 : inB (kgW p) (sc (o + 1)) 1 = true) :
    WP isa (.block (setB (sc o) a ++ setB (sc (o + 1)) b)) s fun s' =>
      PPostB S s s' [(sc o, 1), (sc (o + 1), 1)] ∧ Keep [.x9] s s' ∧
      bytesAt s'.mem (pa s (sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (p := sc o) (v := a) (by simp only; omega) h1 (show Reg.x28 ∈ keptRegs by decide))
    fun s₁ ⟨hP₁, k₁, m₁⟩ => WP.mono (setB_ok (L.post hP₁) (p := sc (o + 1)) (v := b) ho h2 (show Reg.x28 ∈ keptRegs by decide))
      fun s₂ ⟨hP₂, k₂, m₂⟩ => ⟨PPostB.app hP₁ hP₂ (sc_bases _ (by simp)), (k₁.trans k₂).mono (by simp), ?_⟩
  have e : pa s₁ (sc (o + 1)) = pa s (sc o) + BitVec.ofNat 64 1 := by
    rw [hP₁.pa (show Reg.x28 ∈ keptRegs by decide), pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [m₂, m₁, e]
  exact bytesAt_two _ _ _ _

theorem hx_eq (p : Params) (σ : State) :
    hxOf p σ = Spec.MlDsa.H (xiOf σ ++ [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ]) 128 := by
  rw [hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

theorem bytes64 (m : Mem) (a : Addr) : bytesAt m a 64 = bytesAt m a 32 ++ bytesAt m (a + BitVec.ofNat 64 32) 32 :=
  Proof.MlKem.bytesAt_add m a 32 32

theorem sc_pa {S : Nat} {s s' : State} {W : List Region} (hP : PostB S s s' W) (o : Nat) :
    pa s' (sc o) = pa s (sc o) := hP.pa (show Reg.x28 ∈ keptRegs by decide)

theorem seeds_ok {p : Params} (hF : PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) {σ : State}
    (hp : kgPre p S σ) {s : State} (h : KC p σ s) (h24 : s.gpr .x24 = 1) :
    WP isa ((seedsWith keccak.callee) p) s fun s' => K1 p σ s' ∧ s'.gpr .x24 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have hsc := scr_eq p
  have L := h.lay hF hp
  unfold seedsWith
  refine WP.seq (WP.mono (setTwo_ok L (o := oKL) (a := p.k) (b := p.ℓ) (by decide) (by lay) (by lay))
    fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ := h.step hF hp hP₁ (by unfold kcChk; lay)
  have L₁ := h₁.lay hF hp
  refine WP.seq (WP.mono (shake_ok h16 hSl L₁ (ins := [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩]) (out := ⟨.x28, oHX, 128⟩)
    (by simp) (by unfold hashChk pieceChk; lay)) fun s₂ ⟨hP₂, x₂, ho₂⟩ => ?_)
  have h₂ := h₁.step hF hp hP₂ (by unfold kcChk; lay)
  have L₂ := h₂.lay hF hp
  have hmsg : ([⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩].map (pbytes s₁) : List (List Byte)).flatten =
      xiOf σ ++ [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
    have e1 : pbytes s₁ ⟨.x25, 0, 32⟩ = xiOf σ := h₁.xi
    have e2 : pbytes s₁ ⟨.x28, oKL, 2⟩ = [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
      show bytesAt s₁.mem (pa s₁ (sc oKL)) 2 = _
      rw [sc_pa hP₁]; exact hb₁
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, e1, e2]
  rw [hmsg, ← hx_eq] at ho₂
  have ho₂' : bytesAt s₂.mem (pa s₂ (sc oHX)) 128 = hxOf p σ := by rw [sc_pa hP₂]; exact ho₂
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyP_ok L₂ (dst := sc oSA) (src := sc oHX) (by unfold copyPChk; lay)) fun s₃ ⟨hP₃, k₃, b₃⟩ => ?_
  have h₃ := h₂.step hF hp hP₃ (by unfold kcChk; lay)
  have L₃ := h₃.lay hF hp
  have hx3 : bytesAt s₃.mem (pa s₃ (sc oHX)) 128 = hxOf p σ := by rw [L₂.keepBytes hP₃ (by lay)]; exact ho₂'
  have sa3 : bytesAt s₃.mem (pa s₃ (sc oSA)) 32 = rhoOf p σ := by
    rw [sc_pa hP₃, b₃, rho_eq, ← ho₂', Proof.MlKem.bytesAt_take _ _ (by decide)]
  refine WP.mono (copyP_ok L₃ (dst := sc oSB) (src := sc (oHX + 32)) (by unfold copyPChk; lay))
    fun s₄ ⟨hP₄, k₄, b₄⟩ => ?_
  have h₄ := h₃.step hF hp hP₄ (by unfold kcChk; lay)
  have L₄ := h₄.lay hF hp
  refine WP.mono (copyP_ok L₄ (dst := sc (oSB + 32)) (src := sc (oHX + 64)) (by unfold copyPChk; lay))
    fun s₅ ⟨hP₅, k₅, b₅⟩ => ?_
  have h₅ := h₄.step hF hp hP₅ (by unfold kcChk; lay)
  have L₅ := h₅.lay hF hp
  refine WP.mono (setB_ok L₅ (p := sc (oSB + 65)) (v := 0) (by decide) (by lay) (show Reg.x28 ∈ keptRegs by decide))
    fun s₆ ⟨hP₆, k₆, m₆⟩ => ⟨⟨h₅.step hF hp hP₆ (by unfold kcChk; lay), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [L₅.keepBytes hP₆ (by lay), L₄.keepBytes hP₅ (by lay), L₃.keepBytes hP₄ (by lay)]; exact hx3
  · rw [L₅.keepBytes hP₆ (by lay), L₄.keepBytes hP₅ (by lay), L₃.keepBytes hP₄ (by lay)]; exact sa3
  · rw [L₅.keepBytes hP₆ (by lay)]
    have add32 : ∀ (t : State) (o : Nat), pa t (sc o) + BitVec.ofNat 64 32 = pa t (sc (o + 32)) := fun t o => by
      rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
    have A : bytesAt s₅.mem (pa s₅ (sc oSB)) 32 = bytesAt s₃.mem (pa s₃ (sc (oHX + 32))) 32 := by
      rw [L₄.keepBytes hP₅ (by lay), sc_pa hP₄, b₄]
    have B : bytesAt s₅.mem (pa s₅ (sc (oSB + 32))) 32 = bytesAt s₃.mem (pa s₃ (sc (oHX + 64))) 32 := by
      rw [sc_pa hP₅, b₅, L₃.keepBytes hP₄ (by lay)]
    have C : rho'Of p σ = bytesAt s₃.mem (pa s₃ (sc (oHX + 32))) 32 ++ bytesAt s₃.mem (pa s₃ (sc (oHX + 64))) 32 := by
      rw [rho'_eq, ← hx3, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide),
        bytes64, add32, add32]
    rw [bytes64, add32, A, B, C]
  · rw [sc_pa hP₆, m₆, bytesAt_one, writeW8_self]; rfl
  · rw [k₆.get .x24, k₅.get .x24, k₄.get .x24, k₃.get .x24, x₂, k₁.get .x24, h24]

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (taint.check (AArch64.Taint.ofRegs [.x28])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem seeds_tr {p : Params} (hF : PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) :
    RelCT isa (Two p S) ((seedsWith keccak.callee) p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have hsc := scr_eq p
  unfold seedsWith
  refine RelCT.seq (Two.step (taintRel [.x28] (fun x y h => h.x28) (setKL_taint p.k (by omega) p.ℓ (by omega)))
    fun x L => WP.mono (setTwo_ok L (o := oKL) (a := p.k) (b := p.ℓ) (by decide) (by lay) (by lay))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (Two.step (VectorTaint.relRegs [.x25, .x26, .x27, .x28] (fun x y h => h.bases) keccak.mldsaSeedsTaint.choose_spec)
    fun x L => WP.mono (shake_ok h16 hSl L (ins := [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩]) (out := ⟨.x28, oHX, 128⟩)
      (by simp) (by unfold hashChk pieceChk; lay)) fun _ h => ⟨_, h.1⟩) ?_
  exact taintRel [.x28] (fun x y h => h.x28) (by taint_decide)

theorem seeds_piece {p : Params} (hF : PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) :
    Piece p S (fun σ s => KC p σ s ∧ s.gpr .x24 = 1) (fun σ s => K1 p σ s ∧ s.gpr .x24 = 1) ((seedsWith keccak.callee) p) :=
  ⟨fun _ _ hp h => seeds_ok hF h16 hSl hp h.1 h.2,
    rel_of (seeds_tr hF h16 hSl) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_two hF p₁ p₂ pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.AArch64.KeyGen
