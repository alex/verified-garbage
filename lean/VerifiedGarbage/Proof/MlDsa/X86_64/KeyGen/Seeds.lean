import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inv

/-!
# ML-DSA key generation on x86-64: the prologue and the seeds

The prologue saves the callee-saved registers and keeps the pointers
(`pro_piece`); then `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)` to `HX`, `ρ` to the seed
of `RejNTTPoly` and `ρ′ ‖ 0` to that of `RejBoundedPoly` (`seeds_piece`,
`K1`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc setB copy hashAt topPro at_)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-! ## Two runs in the layout -/

theorem Two.lrel {p : Params} {x y : State} (h : Two p x y) : LRel kgR (kgW p) x y :=
  ⟨h.sx.lay, h.sy.lay, fun b hb => h.regs _ (by
    simp only [kgR, kgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [kgRegs]), h.rsp⟩

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem Two.step {p : Params} {c : Prog isa} (htr : RelCT isa (Two p) c fun _ _ => True)
    (hok : ∀ x, Site p x → WP isa c x fun x' => ∃ W, PostB x x' W) : RelCT isa (Two p) c (Two p) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB x x' W) (fun x y h => ⟨hok x h.sx, hok y h.sy⟩)
    fun x y x' y' h ⟨_, hx⟩ ⟨_, hy⟩ => ⟨⟨h.sx.lay.post hx (kgB_bases p), by rw [hx.rsp]; exact h.sx.h32⟩,
      ⟨h.sy.lay.post hy (kgB_bases p), by rw [hy.rsp]; exact h.sy.h32⟩,
      fun r hr => by
        have hb : r ∈ bases := by simp only [kgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
                                  rcases hr with rfl | rfl | rfl | rfl <;> decide
        rw [hx.bs r hb, hy.bs r hb]; exact h.regs r hr, by rw [hx.rsp, hy.rsp]; exact h.rsp⟩

theorem two_rbx {p : Params} {x y : State} (h : Two p x y) : ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.regs .rbx (by decide)

/-! ## Pieces with the sponge, a byte or a copy -/

section
variable {p : Params} {s : State} (L : Lay kgR (kgW p) s)
include L

theorem setB_okM {q : Ptr} {v : Nat} (hr : q.1 ≠ .rax) (hv : v < 256) (hc : inB (kgW p) q 1 = true) :
    WP isa (.block (setB q v)) s fun s' => (PPost s s' [(q, 1)] ∧ bytesAt s'.mem (pa s q) 1 = [BitVec.ofNat 8 v]) ∧
      MX s' = MX s :=
  WP.mx (noLd_spec (by rfl)) (setB_okL L hr hv hc)

theorem copy_okM {dst src : Ptr} {n : Nat} (hsr : src.1 ≠ .rdi) (hc : copyChk (kgB p) (kgW p) dst src n = true) :
    WP isa (copy dst src n) s fun s' => (PPost s s' [(dst, n)] ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n) ∧ MX s' = MX s :=
  WP.mx (noLd_spec (by rfl)) (copy_okL L hsr hc)

end

theorem absorb_noLd : noLd Impl.Sha3.X86_64.Stream.absorb = true := by decide +kernel
theorem pad_noLd : noLd Impl.Sha3.X86_64.Stream.pad = true := by decide +kernel
theorem squeeze_noLd : noLd Impl.Sha3.X86_64.Stream.squeeze = true := by decide +kernel

theorem noLd_seq {a b : Prog isa} (ha : noLd a = true) (hb : noLd b = true) : noLd (.seq a b) = true := by
  simp only [noLd, Code.allInstrs] at ha hb ⊢; rw [ha, hb]; rfl

theorem noLd_call {n : String} {b : Prog isa} (hb : noLd b = true) : noLd (.call n b) = true := by
  simp only [noLd, Code.allInstrs] at hb ⊢; exact hb

theorem absAll_noLd (rate : Nat) : ∀ (ps : List (Ptr × Nat)) (pos : Nat), noLd (VG.Impl.MlKem.X86_64.absAll rate ps pos) = true
  | [], _ => rfl
  | _ :: ps, _ => noLd_seq (noLd_seq (by rfl) (noLd_call absorb_noLd)) (absAll_noLd rate ps _)

theorem hash_noLd (ps : List (Ptr × Nat)) (rate suffix : Nat) (out : Ptr) (len : Nat) :
    noLd (hashAt ps rate suffix out len) = true :=
  noLd_seq (by rfl) (noLd_seq (absAll_noLd rate ps 0) (noLd_seq (noLd_seq (by rfl) (noLd_call pad_noLd))
    (noLd_seq (by rfl) (noLd_call squeeze_noLd))))

theorem hash_okM {p : Params} {ps : List (Ptr × Nat)} {rate suffix : Nat} {out : Ptr} {len : Nat}
    (hc : hashChk (kgB p) (kgW p) ps rate out len = true) (hsuf : suffix < 256) {s : State} (L : Lay kgR (kgW p) s) :
    WP isa (hashAt ps rate suffix out len) s fun s' => (PPost s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧
      bytesAt s'.mem (pa s out) len =
        Spec.Sha3.squeezeFrom rate (Proof.MlKem.padded rate (BitVec.ofNat 8 suffix) (pieces s ps)) 0 len) ∧
      MX s' = MX s :=
  WP.mx (noLd_spec (hash_noLd ps rate suffix out len)) (hash_ok (kgB_bases p) hc hsuf L)

/-! ## The prologue -/

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) :
    WP isa (.block pro) σ fun s => KC p σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨_, hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hS : ⟨σ.gpr .rcx, scrLen p⟩ ∈ σ.wr := by rw [hwr]; simp
  have hs : 888 ≤ scrLen p := by have := hF.k; simp only [scrLen, Spec.MlDsa.scratchWords]; omega
  have hs2 : scrLen p < 2 ^ 64 := by
    have := hF.k; have := hF.l; have := hF.kl; simp only [scrLen, Spec.MlDsa.scratchWords]; omega
  have c : ∀ o, o + 8 ≤ 888 → (⟨σ.gpr .rcx, scrLen p⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' (by omega) (by omega)
  have w : ∀ o, o + 8 ≤ 888 → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.mx (noLd_spec (by rfl)) (WP.keep [.rbx, .rbp, .r12, .r13, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide))) fun s ⟨⟨⟨hm, hbx, hbp, h12, h13, h15⟩, k⟩, hx⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h12 h13, fun j hj => ?_, ?_⟩, ?_, hx⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using d3) (by decide)

theorem pro_piece {p : Params} (hF : PFacts p) :
    Piece p (fun σ s => s = σ) (fun σ s => KC p σ s ∧ s.gpr .r15 = 1) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact pro_ok hF hp,
    taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂
      exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)⟩

/-! ## The seeds -/

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte := Spec.MlDsa.H (xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds, with `ρ` copied to the first `j` seeds of `oSA4`. -/
structure K1R (p : Params) (j : Nat) (σ s : State) : Prop where
  kc : KC p σ s
  hx : bytesAt s.mem (pa s (sc oHX)) 128 = hxOf p σ
  sa : bytesAt s.mem (pa s (sc oSA)) 32 = rhoOf p σ
  sb : bytesAt s.mem (pa s (sc oSB)) 64 = rho'Of p σ
  z : bytesAt s.mem (pa s (sc (oSB + 65))) 1 = [0]
  sa4 : ∀ k < j, bytesAt s.mem (pa s (sc (oSA4 + 34 * k))) 32 = rhoOf p σ

/-- After the seeds. -/
abbrev K1 (p : Params) (σ s : State) : Prop := K1R p 4 σ s

theorem K1.step {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {s s' : State} (h : K1 p σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hx : MX s' = MX s) (hc : k1Chk p ws = true) : K1 p σ s' := by
  simp only [k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, a0⟩, a1⟩, a2⟩, a3⟩ := hc
  have L := h.kc.lay hF hp
  refine ⟨h.kc.step hF hp hP hx h0, by rw [L.keepBytes hP h1]; exact h.hx, by rw [L.keepBytes hP h2]; exact h.sa,
    by rw [L.keepBytes hP h3]; exact h.sb, by rw [L.keepBytes hP h4]; exact h.z, fun k hk => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [L.keepBytes hP a0]; exact h.sa4 0 hk
  · rw [L.keepBytes hP a1]; exact h.sa4 1 hk
  · rw [L.keepBytes hP a2]; exact h.sa4 2 hk
  · rw [L.keepBytes hP a3]; exact h.sa4 3 hk

theorem shake31' : BitVec.ofNat 8 31 = Spec.Sha3.shakeSuffix := by decide

theorem hx_eq (p : Params) (σ : State) :
    hxOf p σ = Spec.Sha3.squeezeFrom 136 (Proof.MlKem.padded 136 (BitVec.ofNat 8 31)
      (xiOf σ ++ ([BitVec.ofNat 8 p.k] ++ [BitVec.ofNat 8 p.ℓ]))) 0 128 := by
  rw [hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, shake31',
    List.append_assoc, ← Proof.MlKem.shake256_eq]; rfl

theorem rho_eq (p : Params) (σ : State) : rhoOf p σ = (hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : rho'Of p σ = ((hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : kOf p σ = ((hxOf p σ).drop 96).take 32 := rfl

/-- Two bytes, at `scratch + o` and `scratch + o + 1`. -/
theorem setTwo_ok {p : Params} {s : State} (L : Lay kgR (kgW p) s) {o a b : Nat} (ha : a < 256) (hb : b < 256)
    (h1 : inB (kgW p) (sc o) 1 = true) (h2 : inB (kgW p) (sc (o + 1)) 1 = true)
    (hk : keepB (kgB p) [(sc (o + 1), 1)] (sc o) 1 = true) :
    WP isa (.block (setB (sc o) a ++ setB (sc (o + 1)) b)) s fun s' =>
      PPost s s' [(sc o, 1), (sc (o + 1), 1)] ∧ MX s' = MX s ∧
      bytesAt s'.mem (pa s (sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  have hr : Reg.rbx ≠ .rax := by decide
  have hc : ∀ w ∈ [(sc (o + 1), 1)], w.1.1 ∈ calleeSaved := fun w hw => by
    rw [List.mem_singleton] at hw; subst hw; exact rbx_cs
  refine WP.block_append (WP.mono (setB_okM L (q := sc o) (v := a) hr ha h1)
    fun s₁ ⟨⟨hP₁, hb₁⟩, hx₁⟩ => WP.mono (setB_okM (L.post hP₁.b (kgB_bases p)) (q := sc (o + 1)) (v := b)
      hr hb h2) fun s₂ ⟨⟨hP₂, hb₂⟩, hx₂⟩ => ⟨PPost.app hP₁ hP₂ hc, hx₂.trans hx₁, ?_⟩)
  have L₁ := L.post hP₁.b (kgB_bases p)
  have e1 : pa s₁ (sc o) = pa s (sc o) := hP₁.pa rbx_cs
  have k1 := L₁.keepBytes hP₂.b hk
  rw [hP₂.pa rbx_cs, e1] at k1
  have e : pa s (sc o) + BitVec.ofNat 64 1 = pa s₁ (sc (o + 1)) := by rw [hP₁.pa rbx_cs]; exact off_add _ _ _
  rw [show 2 = 1 + 1 from rfl, Proof.MlKem.bytesAt_add, k1, hb₁, e, hb₂]
  rfl

theorem setKL_ok {p : Params} {s : State} (L : Lay kgR (kgW p) s) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    WP isa (.block (setB (sc oKL) a ++ setB (sc (oKL + 1)) b)) s fun s' =>
      PPost s s' [(sc oKL, 1), (sc (oKL + 1), 1)] ∧ MX s' = MX s ∧
      bytesAt s'.mem (pa s (sc oKL)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] :=
  setTwo_ok L ha hb (by lay) (by lay) (by lay)

/-- `ρ` to seed `j` of `oSA4`. -/
theorem copyR_ok {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {j : Nat} (hj : j < 4) {s : State}
    (h : K1R p j σ s) :
    WP isa (copy (sc (oSA4 + 34 * j)) (sc oHX) 32) s fun s' => K1R p (j + 1) σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  have hk := hF.k; have hl := hF.l
  have L := h.kc.lay hF hp
  refine WP.mono (copy_okM L (dst := sc (oSA4 + 34 * j)) (src := sc oHX) (n := 32) (by decide) (by layk))
    fun s' ⟨⟨hP, hb⟩, hx⟩ => ⟨⟨h.kc.step hF hp hP.b hx (by layk), by rw [L.keepBytes hP.b (by layk)]; exact h.hx,
      by rw [L.keepBytes hP.b (by layk)]; exact h.sa, by rw [L.keepBytes hP.b (by layk)]; exact h.sb,
      by rw [L.keepBytes hP.b (by layk)]; exact h.z, fun k hk' => ?_⟩, hP.cs .r15 (by decide)⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · rw [L.keepBytes hP.b (by layk)]; exact h.sa4 k hk'
  · rw [hP.pa rbx_cs, hb, ← Proof.MlKem.bytesAt_take s.mem (pa s (sc oHX)) (show 32 ≤ 128 by decide), h.hx, ← rho_eq]

theorem seeds_ok {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {s : State} (h : KC p σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (seeds p) s fun s' => K1 p σ s' ∧ s'.gpr .r15 = 1 := by
  have hk := hF.k; have hl := hF.l
  have L := h.lay hF hp
  unfold seeds
  refine WP.seq (WP.mono (setKL_ok L (a := p.k) (b := p.ℓ) (by omega) (by omega)) fun s₁ ⟨hP₁, hx₁, hb₁⟩ => ?_)
  have h₁ := h.step hF hp hP₁.b hx₁ (by layk)
  have L₁ := h₁.lay hF hp
  have e₁ : ∀ o, pa s₁ (sc o) = pa s (sc o) := fun o => hP₁.pa rbx_cs
  refine WP.seq (WP.mono (hash_okM (ps := [((.rbp, 0), 32), (sc oKL, 2)]) (rate := 136) (suffix := 31)
    (out := sc oHX) (len := 128) (by layk) (by decide) L₁) fun s₂ ⟨⟨hP₂, ho₂⟩, hx₂⟩ => ?_)
  have h₂ := h₁.step hF hp hP₂.b hx₂ (by layk)
  have L₂ := h₂.lay hF hp
  have e₂ : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun o => hP₂.pa rbx_cs
  have hpc : pieces s₁ [((.rbp, 0), 32), (sc oKL, 2)] = xiOf σ ++ ([BitVec.ofNat 8 p.k] ++ [BitVec.ofNat 8 p.ℓ]) := by
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h₁.xi, e₁, hb₁]; rfl
  rw [hpc, ← hx_eq, ← e₂] at ho₂
  refine WP.seq (WP.mono (copy_okM L₂ (dst := sc oSA) (src := sc oHX) (n := 32) (by decide) (by layk))
    fun s₃ ⟨⟨hP₃, hb₃⟩, hx₃⟩ => ?_)
  have h₃ := h₂.step hF hp hP₃.b hx₃ (by layk)
  have L₃ := h₃.lay hF hp
  have e₃ : ∀ o, pa s₃ (sc o) = pa s₂ (sc o) := fun o => hP₃.pa rbx_cs
  have hx3 : bytesAt s₃.mem (pa s₃ (sc oHX)) 128 = hxOf p σ := by rw [L₂.keepBytes hP₃.b (by layk)]; exact ho₂
  rw [← Proof.MlKem.bytesAt_take s₂.mem (pa s₂ (sc oHX)) (show 32 ≤ 128 by decide), ho₂, ← rho_eq, ← e₃] at hb₃
  refine WP.seq (WP.mono (copy_okM L₃ (dst := sc oSB) (src := sc (oHX + 32)) (n := 64) (by decide) (by layk))
    fun s₄ ⟨⟨hP₄, hb₄⟩, hx₄⟩ => ?_)
  have h₄ := h₃.step hF hp hP₄.b hx₄ (by layk)
  have L₄ := h₄.lay hF hp
  have e₄ : ∀ o, pa s₄ (sc o) = pa s₃ (sc o) := fun o => hP₄.pa rbx_cs
  have hsb : bytesAt s₃.mem (pa s₃ (sc (oHX + 32))) 64 = rho'Of p σ := by
    rw [rho'_eq, ← hx3, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide), pa, pa, off_add]
  rw [hsb, ← e₄] at hb₄
  refine WP.seq (WP.mono (WP.mx (noLd_spec (by rfl)) (setB_okL L₄ (p := sc (oSB + 65)) (v := 0) (by decide)
    (by decide) (by lay))) fun s₅ ⟨⟨hP₅, hb₅⟩, hx₅⟩ => ?_)
  have h₅ : K1R p 0 σ s₅ := ⟨h₄.step hF hp hP₅.b hx₅ (by layk),
    by rw [L₄.keepBytes hP₅.b (by layk), L₃.keepBytes hP₄.b (by layk)]; exact hx3,
    by rw [L₄.keepBytes hP₅.b (by layk), L₃.keepBytes hP₄.b (by layk)]; exact hb₃,
    by rw [L₄.keepBytes hP₅.b (by layk)]; exact hb₄, by rw [hP₅.pa rbx_cs]; exact hb₅,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have f₅ : s₅.gpr .r15 = 1 := by
    rw [hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide),
      hP₁.cs .r15 (by decide), h15]
  refine WP.seq (WP.mono (copyR_ok hF hp (j := 0) (by decide) h₅) fun s₆ ⟨h₆, f₆⟩ => ?_)
  refine WP.seq (WP.mono (copyR_ok hF hp (j := 1) (by decide) h₆) fun s₇ ⟨h₇, f₇⟩ => ?_)
  refine WP.seq (WP.mono (copyR_ok hF hp (j := 2) (by decide) h₇) fun s₈ ⟨h₈, f₈⟩ => ?_)
  exact WP.mono (copyR_ok hF hp (j := 3) (by decide) h₈) fun s₉ ⟨h₉, f₉⟩ =>
    ⟨h₉, by rw [f₉, f₈, f₇, f₆, f₅]⟩

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem seeds_tr {p : Params} (hF : PFacts p) : RelCT isa (Two p) (seeds p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  unfold seeds
  refine RelCT.seq (Two.step (taintRel [.rbx] (fun x y h => two_rbx h) (setKL_taint p.k (by omega) p.ℓ (by omega)))
    fun x S => WP.mono (setKL_ok S.lay (a := p.k) (b := p.ℓ) (by omega) (by omega)) fun _ h => ⟨_, h.1.b⟩) ?_
  refine RelCT.seq (Two.step (RelCT.mono (hash_tr (kgB_bases p) (ps := [((.rbp, 0), 32), (sc oKL, 2)]) (rate := 136)
      (suffix := 31) (out := sc oHX) (len := 128) (by layk) (by decide)) (fun _ _ h => h.lrel) fun _ _ h => h)
    fun x S => WP.mono (hash_okM (ps := [((.rbp, 0), 32), (sc oKL, 2)]) (rate := 136) (suffix := 31)
      (out := sc oHX) (len := 128) (by layk) (by decide) S.lay) fun _ h => ⟨_, h.1.1.b⟩) ?_
  refine RelCT.seq (Two.step (taintRel [.rbx] (fun x y h => two_rbx h) (by taint_decide))
    fun x S => WP.mono (copy_okM S.lay (dst := sc oSA) (src := sc oHX) (n := 32) (by decide) (by layk))
      fun _ h => ⟨_, h.1.1.b⟩) ?_
  refine RelCT.seq (Two.step (taintRel [.rbx] (fun x y h => two_rbx h) (by taint_decide))
    fun x S => WP.mono (copy_okM S.lay (dst := sc oSB) (src := sc (oHX + 32)) (n := 64) (by decide) (by layk))
      fun _ h => ⟨_, h.1.1.b⟩) ?_
  exact taintRel [.rbx] (fun x y h => two_rbx h) (by taint_decide)

theorem seeds_piece {p : Params} (hF : PFacts p) :
    Piece p (fun σ s => KC p σ s ∧ s.gpr .r15 = 1) (fun σ s => K1 p σ s ∧ s.gpr .r15 = 1) (seeds p) :=
  ⟨fun _ _ hp h => seeds_ok hF hp h.1 h.2,
    rel_of (seeds_tr hF) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_two hF p₁ p₂ pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.X86_64.KeyGen
