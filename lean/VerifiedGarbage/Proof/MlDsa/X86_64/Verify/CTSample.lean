import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages

/-!
# ML-DSA verification on x86-64: constant time, the samplers

The seed of each entry of `Â` is `ρ ‖ s ‖ r`, and `c̃` a piece of the
signature, public in both runs; each sampler's output is masked with its
result without a branch (`sampledTail_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt aSeed)

/-- A well-formed hint `h`, and `z` small. -/
def HN (p : Params) (σ : State) (h : List (Vector Bool n)) : Prop :=
  vHint p (vSig p σ) = some h ∧ ∀ i < p.ℓ, normRq [toRq (vZ p (vSig p σ) i)] < p.γ₁ - p.β

/-- Before the samplers, after them and while sampling `Â`. -/
def Is (p : Params) (σ s : State) : Prop := ∃ h, HN p σ h ∧ S2 p h p.ℓ σ s ∧ s.gpr .r15 = flag True
def I4 (p : Params) (σ s : State) : Prop := ∃ h, HN p σ h ∧ S4 p h σ s
def IA (p : Params) (r c : Nat) (σ s : State) : Prop := ∃ h, HN p σ h ∧ S3 p h r c σ s

theorem IA.t {p : Params} {r c : Nat} {σ s : State} (h : IA p r c σ s) : T p σ s := let ⟨_, _, hs⟩ := h; hs.t

theorem seed_of {p : Params} {h : List (Vector Bool n)} {r c : Nat} {σ s₀ s : State} (hs : S3 p h r c σ s₀)
    (hP : PPostB s₀ s wsB) (hm : s.mem = (s₀.mem.writeW (pa s₀ (sc oSB) + BitVec.ofNat 64 32) (BitVec.ofNat 8 c)).writeW
      (pa s₀ (sc oSB) + BitVec.ofNat 64 33) (BitVec.ofNat 8 r)) :
    bytesAt s.mem (pa s (sc oSB)) 34 = aSeed (vPk p σ) r c := by
  rw [hP.pa (by decide), hm, seed_bytes, hs.rho, aSeed, integerToBytes_one, integerToBytes_one]

theorem aOne_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {r c : Nat} (hr : r < p.k)
    (hc : c < p.ℓ) : RelCT isa (RV p (IA p r c)) (aOne P (8 * r + c)) (RV p (IA p r (c + 1))) := by
  have hck := aChk_all p hp r hr c hc
  have hkl := kl_le p hp
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h32, h33⟩, hrej⟩, hin⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hck
  have hT : ∀ σ s, IA p r c σ s → T p σ s := fun _ _ h => h.t
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (aOne_ok C hp hv hr hc hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  have em : (8 * r + c) % 8 = c := by omega
  have ed : (8 * r + c) / 8 = r := by omega
  unfold aOne
  rw [em, ed]
  refine RelCT.seq (relInv (I' := fun σ s => ∃ s₀, IA p r c σ s₀ ∧ (PPostB s₀ s wsB ∧ s.gpr .r15 = s₀.gpr .r15 ∧
      s.mem = (s₀.mem.writeW (pa s₀ (sc oSB) + BitVec.ofNat 64 32) (BitVec.ofNat 8 c)).writeW
        (pa s₀ (sc oSB) + BitVec.ofNat 64 33) (BitVec.ofNat 8 r)))
    (fun σ s hv hs => WP.mono (setB2_ok ((hT σ s hs).lay hp hv) h32 h33 c r (by omega) (by omega))
      fun _ h' => ⟨s, hs, h'⟩)
    (setB2_tr fun x y h => (RV.lrel hp hT h).2.2.1 .rbx (by decide))) ?_
  unfold sampled
  refine RelCT.seq (RelCT.sameB (rejNttAt_tr C.rejNtt (layOk p hp) hrej fun x y h => ?_) (fun x y h => ?_)
    (fun x y h => (RV.lrelStep hp hT (fun _ _ f => ⟨_, f.1⟩) h).2.2))
    (sampledTail_tr (ptr_ok (layOk p hp) hin) (show Reg.rbx ∈ bases by decide))
  · have L := RV.lrelStep hp hT (fun _ _ f => ⟨_, f.1⟩) h
    obtain ⟨σ₁, σ₂, _, _, pub, ⟨x₀, ⟨_, _, hx⟩, fx⟩, ⟨y₀, ⟨_, _, hy⟩, fy⟩⟩ := h
    exact ⟨L.1, L.2.1, L.2.2, by rw [seed_of hx fx.1 fx.2.2, seed_of hy fy.1 fy.2.2, pub.2.2.2.2.2.1]⟩
  · have L := RV.lrelStep hp hT (fun _ _ f => ⟨_, f.1⟩) h
    exact ⟨WP.mono (rejNttAt_ok C.rejNtt L.1 hrej) fun _ h' => ⟨_, h'.1⟩,
      WP.mono (rejNttAt_ok C.rejNtt L.2.1 hrej) fun _ h' => ⟨_, h'.1⟩⟩

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl, Proof.MlKem.bytesAt_add,
    show 68 = 34 + 34 from rfl, Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds of `SB4`, for the entries `(r, c₀), …, (r, c₀ + 3)`. -/
theorem GS.seeds {p : Params} {h : List (Vector Bool n)} {r c c₀ : Nat} {σ s : State} (g : GS p h r c c₀ 4 σ s) :
    bytesAt s.mem (pa s (sc oSB4)) 136 = aSeed (vPk p σ) r (c₀ + 0) ++ aSeed (vPk p σ) r (c₀ + 1) ++
      aSeed (vPk p σ) r (c₀ + 2) ++ aSeed (vPk p σ) r (c₀ + 3) := by
  have e : ∀ k, pa s (sc (oSB4 + 34 * k)) = pa s (sc oSB4) + BitVec.ofNat 64 (34 * k) := fun k => by
    simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have b0 : bytesAt s.mem (pa s (sc oSB4)) 34 = aSeed (vPk p σ) r (c₀ + 0) := g.done 0 (by decide)
  have b1 : bytesAt s.mem (pa s (sc oSB4) + BitVec.ofNat 64 34) 34 = aSeed (vPk p σ) r (c₀ + 1) := by
    have := g.done 1 (by decide); rw [e] at this; exact this
  have b2 : bytesAt s.mem (pa s (sc oSB4) + BitVec.ofNat 64 68) 34 = aSeed (vPk p σ) r (c₀ + 2) := by
    have := g.done 2 (by decide); rw [e] at this; exact this
  have b3 : bytesAt s.mem (pa s (sc oSB4) + BitVec.ofNat 64 102) 34 = aSeed (vPk p σ) r (c₀ + 3) := by
    have := g.done 3 (by decide); rw [e] at this; exact this
  rw [bytes136, b0, b1, b2, b3]

theorem slotBlock_tr {r c₀ j : Nat} {P : State → State → Prop} (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rbx = s₂.gpr .rbx) :
    RelCT isa P (.block (setSR r c₀ j)) fun _ _ => True :=
  taintRel [.rbx] (fun s₁ s₂ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hP s₁ s₂ h)
    (hc := .block []) (by with_unfolding_all rfl)

/-- The bytes of seed `j` of `SB4`, from `GS j` to `GS (j + 1)`. -/
theorem slot_tr {p : Params} (hp : p ∈ params) {r c c₀ j : Nat} (hr : r < 256) (hj : j < 4) (hx : c₀ + j < 256)
    (hck : slotChk p r c j = true) :
    RelCT isa (RV p fun σ s => ∃ h, HN p σ h ∧ GS p h r c c₀ j σ s) (.block (setSR r c₀ j))
      (RV p fun σ s => ∃ h, HN p σ h ∧ GS p h r c c₀ (j + 1) σ s) :=
  relInv (fun σ s hv ⟨h, hh, g⟩ => WP.mono (slot_ok hp hv hr hj hx hck g) fun _ g' => ⟨h, hh, g'⟩)
    (slotBlock_tr fun x y h => (RV.lrel hp (fun _ _ h => let ⟨_, _, g⟩ := h; g.s3.t) h).2.2.1 .rbx (by decide))

theorem aGrp_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {r c₀ c : Nat} (hr : r < p.k)
    (hck : gChk p r c₀ c = true) : RelCT isa (RV p (IA p r c)) (aGrp P p r c₀) (RV p (IA p r (c₀ + 4))) := by
  have hkl := kl_le p hp
  have hck' := hck
  simp only [gChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hck'
  obtain ⟨⟨⟨⟨⟨⟨⟨hsl, hrej⟩, hin⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hck'
  have hT : ∀ σ s, IA p r c σ s → T p σ s := fun _ _ h => h.t
  have hTG : ∀ σ s, (∃ h, HN p σ h ∧ GS p h r c c₀ 4 σ s) → T p σ s := fun _ _ ⟨_, _, g⟩ => g.s3.t
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (aGrp_ok C hp hv hr hck hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold aGrp
  refine RelCT.seq (RelCT.mono (slot_tr hp (by omega) (by decide) (by omega) (hsl 0 (by decide)))
    (fun x y ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, s₁⟩, ⟨h₂, hh₂, s₂⟩⟩ => ⟨σ₁, σ₂, v₁, v₂, pub,
      ⟨h₁, hh₁, s₁, fun _ h => absurd h (by omega)⟩, ⟨h₂, hh₂, s₂, fun _ h => absurd h (by omega)⟩⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (slot_tr hp (by omega) (by decide) (by omega) (hsl 1 (by decide))) ?_
  refine RelCT.seq (slot_tr hp (by omega) (by decide) (by omega) (hsl 2 (by decide))) ?_
  refine RelCT.seq (slot_tr hp (by omega) (by decide) (by omega) (hsl 3 (by decide))) ?_
  unfold sampled4
  refine RelCT.seq (RelCT.sameB (rej4At_tr C.rej4 (layOk p hp) hrej fun x y h => ?_) (fun x y h => ?_)
    (fun x y h => (RV.lrel hp hTG h).2.2))
    (sampledTail4_tr (ptr_ok (layOk p hp) hin) (show Reg.rbx ∈ bases by decide))
  · have L := RV.lrel hp hTG h
    obtain ⟨σ₁, σ₂, _, _, pub, ⟨_, _, gx⟩, ⟨_, _, gy⟩⟩ := h
    exact ⟨L.1, L.2.1, L.2.2, by rw [gx.seeds, gy.seeds, pub.2.2.2.2.2.1]⟩
  · have L := RV.lrel hp hTG h
    exact ⟨WP.mono (rej4At_ok C.rej4 L.1 hrej) fun _ h' => ⟨_, h'.1⟩,
      WP.mono (rej4At_ok C.rej4 L.2.1 hrej) fun _ h' => ⟨_, h'.1⟩⟩

theorem IA.next {p : Params} {r : Nat} {x y : State} (h : RV p (IA p r p.ℓ) x y) : RV p (IA p (r + 1) 0) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, s₁⟩, ⟨h₂, hh₂, s₂⟩⟩ := h
  exact ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, s₁.next⟩, ⟨h₂, hh₂, s₂.next⟩⟩

theorem aRow_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {r : Nat} (hr : r < p.k) :
    RelCT isa (RV p (IA p r 0)) (aRow P p r) (RV p (IA p (r + 1) 0)) := by
  have hkl := kl_le p hp
  have hg := gChk_all p hp r hr
  have hl : p.ℓ = 4 ∨ p.ℓ = 5 ∨ p.ℓ = 7 := by
    have : ∀ p ∈ params, p.ℓ = 4 ∨ p.ℓ = 5 ∨ p.ℓ = 7 := by decide
    exact this p hp
  unfold aRow
  refine RelCT.seq (aGrp_tr C hp hr hg.1) ?_
  by_cases h7 : p.ℓ = 7
  · rw [ite_eq_left h7]
    refine RelCT.mono (aGrp_tr C hp hr (hg.2 h7)) (fun x y h => by rwa [Nat.zero_add] at h) fun x y h => ?_
    rw [show 3 + 4 = p.ℓ by omega] at h
    exact IA.next h
  · rw [ite_eq_right h7]
    refine RelCT.mono (seqR_tr (R := fun e => RV p (IA p r (e - 8 * r))) (p.ℓ - 4) (8 * r + 4) fun e he he' => ?_)
      (fun x y h => by rw [show 8 * r + 4 - 8 * r = 4 by omega]; rwa [Nat.zero_add] at h) fun x y h => ?_
    · have := aOne_tr C hp hr (c := e - 8 * r) (by omega)
      rw [show 8 * r + (e - 8 * r) = e by omega, show e - 8 * r + 1 = e + 1 - 8 * r by omega] at this
      exact this
    · rw [show 8 * r + 4 + (p.ℓ - 4) - 8 * r = p.ℓ by omega] at h
      exact IA.next h

theorem ballStage_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p (IA p p.k 0)) (sampled (ballAt P (.r13, 0) p.ctildeLen p.τ pC) pC) (RV p (I4 p)) := by
  have hc := sChk_all p hp
  simp only [sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, c5⟩, c6⟩, c7⟩, _⟩, c9⟩, _⟩, _⟩ := hc
  have hT : ∀ σ s, IA p p.k 0 σ s → T p σ s := fun _ _ h => h.t
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (ballStage_ok C hp hv hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold sampled
  refine RelCT.seq (RelCT.sameB (ballAt_tr C.ball (layOk p hp) c6 c5 fun x y h => ?_) (fun x y h => ?_)
    (fun x y h => (RV.lrel hp hT h).2.2)) (sampledTail_tr (ptr_ok (layOk p hp) c9) (show Reg.rbx ∈ bases by decide))
  · have L := RV.lrel hp hT h
    obtain ⟨σ₁, σ₂, _, _, pub, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩ := h
    exact ⟨L.1, L.2.1, L.2.2, by rw [hx.t.sigSlice (by omega : 0 + p.ctildeLen ≤ p.sigLen),
      hy.t.sigSlice (by omega : 0 + p.ctildeLen ≤ p.sigLen), pub.2.2.2.2.2.2.2]⟩
  · have L := RV.lrel hp hT h
    exact ⟨WP.mono (ballAt_ok C.ball L.1 c6 c5) fun _ h' => ⟨_, h'.1⟩,
      WP.mono (ballAt_ok C.ball L.2.1 c6 c5) fun _ h' => ⟨_, h'.1⟩⟩

/-- While copying `ρ`. -/
def IRho (p : Params) (j : Nat) (σ s : State) : Prop := ∃ h, HN p σ h ∧ RhoS p h j σ s

theorem copyK_tr {p : Params} (hp : p ∈ params) {j : Nat} (hj : j < 4) :
    RelCT isa (RV p (IRho p j)) (copy (sc (oSB4 + 34 * j)) (.rbp, 0) 32) (RV p (IRho p (j + 1))) := by
  have hc := rChk_all p hp j hj
  simp only [rChk, Bool.and_eq_true] at hc
  have hS := layOk p hp
  have hsd' := sepB_spec hc.1.1.1.1
  have hok : ∀ a ∈ copyArgs (sc (oSB4 + 34 * j)) (.rbp, 0) 32, a.2.Ok ∧ a.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS hsd'.2.1, by decide⟩, ⟨ptr_ok hS hsd'.1, by decide⟩, ⟨show 32 < 2 ^ 31 by decide, by decide⟩⟩
  exact relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (copyK_ok hp hv hj hs) fun _ h' => ⟨h, hh, h'⟩)
    (copy_tr hok (show Reg.rbx ∈ bases by decide) (by decide) fun x y h =>
      (RV.lrel hp (fun _ _ h => let ⟨_, _, hs⟩ := h; hs.t) h).2.2)

theorem samples_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p (Is p)) (samples P p) (RV p (I4 p)) := by
  have hc := sChk_all p hp
  simp only [sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  have hS := layOk p hp
  have hsd' := sepB_spec c1
  have hok : ∀ a ∈ copyArgs (sc oSB) (.rbp, 0) 32, a.2.Ok ∧ a.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS hsd'.2.1, by decide⟩, ⟨ptr_ok hS hsd'.1, by decide⟩, ⟨show 32 < 2 ^ 31 by decide, by decide⟩⟩
  unfold samples rhos
  refine RelCT.seq (RelCT.seq (relInv (I' := IRho p 0)
    (fun σ s hv ⟨h, hh, hs, h15⟩ => WP.mono (copyRho_ok hp hv hs h15) fun _ h' => ⟨h, hh, h'⟩)
    (copy_tr hok (by decide) (by decide) fun x y h =>
      (RV.lrel hp (fun _ _ h => let ⟨_, _, hs, _⟩ := h; hs.t) h).2.2))
    (RelCT.seq (copyK_tr hp (j := 0) (by decide)) (RelCT.seq (copyK_tr hp (j := 1) (by decide))
      (RelCT.seq (copyK_tr hp (j := 2) (by decide)) (RelCT.mono (copyK_tr hp (j := 3) (by decide)) (fun _ _ h => h)
        (Q' := RV p (IA p 0 0)) fun x y h => ?_))))) (RelCT.seq ?_ (ballStage_tr C hp))
  · obtain ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, r₁⟩, ⟨h₂, hh₂, r₂⟩⟩ := h
    exact ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, r₁.s3⟩, ⟨h₂, hh₂, r₂.s3⟩⟩
  have := seqR_tr (R := fun r => RV p (IA p r 0)) p.k 0 fun r _ hr => aRow_tr C hp (by omega)
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.X86_64.Verify
