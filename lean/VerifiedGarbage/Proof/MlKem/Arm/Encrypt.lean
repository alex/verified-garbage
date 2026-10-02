import VerifiedGarbage.Proof.MlKem.Arm.CallsCT

/-!
# ML-KEM on 32-bit ARM: K-PKE.Encrypt, correctness

`K.encrypt` runs within encapsulation and decapsulation, on buffers the callers
choose (`EB`): the encapsulation key (in `r4`), the message (in `r5`) and the
ciphertext (in `r8`), each at an offset of one of the callers' buffers; `r` is
at 920 in `scratch`. It writes the ciphertext, and changes nothing but the
regions of `encW` (`encrypt_ok`). Its phases: `ρ` copied to the seed of
`SampleNTT`, `t̂` decoded (`decT_loop`), the `PRF`s into `ŷ`, `e₁` and `e₂`,
`μ`, the rows of `u` compressed into the ciphertext (`encRow_step`), and `v`.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Regions inside regions -/

theorem sepB_mono {sz : List Nat} {a a' b b' : Nat × Nat × Nat} (h : sepB sz a b = true) (ha : inB a' a = true)
    (hb : inB b' b = true) : sepB sz a' b' = true := by
  obtain ⟨i, o, l⟩ := a
  obtain ⟨i', o', l'⟩ := a'
  obtain ⟨j, p, n⟩ := b
  obtain ⟨j', p', n'⟩ := b'
  simp only [inB, sepB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h ha hb ⊢
  obtain ⟨⟨e1, a1⟩, a2⟩ := ha
  obtain ⟨⟨e2, b1⟩, b2⟩ := hb
  subst e1; subst e2
  omega

theorem sepAll_mono {sz : List Nat} {a a' : Nat × Nat × Nat} {W W' : List (Nat × Nat × Nat)}
    (h : sepAll sz a W' = true) (ha : inB a' a = true) (hW : W.all (fun w => W'.any (inB w)) = true) :
    sepAll sz a' W = true :=
  List.all_eq_true.mpr fun w hw => by
    obtain ⟨w', hw', hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp hW w hw)
    exact sepB_mono (List.all_eq_true.mp h w' hw') ha hi

theorem inB_off {i o l k n : Nat} (h : k + n ≤ l) : inB (i, o + k, n) (i, o, l) = true := by
  simp only [inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem inB_refl (w : Nat × Nat × Nat) : inB w w = true := by
  simp only [inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- The bounds of a region apart from another. -/
theorem sepAll_bounds {sz : List Nat} {i o l : Nat} {w : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll sz (i, o, l) (w :: W) = true) : i < sz.length ∧ o + l ≤ sz.getD i 0 :=
  sepB_bounds (List.all_eq_true.mp h w (List.mem_cons_self ..))

/-- A part of a buffer inside a bigger one. -/
theorem KeptX.subOff {L : Lay} {xs : List Reg} {s s' : State} (hL : L.Ok) {i o l k n : Nat}
    (hb : i < L.sizes.length ∧ o + l ≤ L.size i) (hk : k + n ≤ l) (h : KeptX xs (L.RL [(i, o + k, n)]) s s') :
    KeptX xs (L.RL [(i, o, l)]) s s' :=
  h.sub fun r hr => by
    simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact ⟨L.R i o l, List.mem_singleton_self _, Lay.R_sub_R hL hb.1 (by omega) (by omega) hb.2⟩

/-! ## Copying from an offset -/

theorem copyLo {L : Lay} {s : State} (hL : L.Ok) {sb db : Reg} {bo so dO len i j : Nat}
    (hsb : sb ∈ preserved ∧ sb ≠ .lr) (hdb : db ∈ preserved ∧ db ≠ .lr)
    (gs : s.gpr sb = L.ptr i + BitVec.ofNat 32 bo) (gd : s.gpr db = L.ptr j)
    (hse : encodable (BitVec.ofNat 32 so) = true)
    (hde : encodable (BitVec.ofNat 32 dO) = true) (hle : encodable (BitVec.ofNat 32 len) = true)
    (hlen : len < 2 ^ 32) (hl0 : 0 < len) (hs : sepB L.sizes (i, bo + so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i (bo + so)) len := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) hl0
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) hl0
  refine WP.seq (WP.mono (copy_setup hsb hdb hse hde hle) fun s₁ ⟨o₁, g0, g1, g2⟩ => ?_)
  rw [gs, ptr_add_add32] at g0; rw [gd] at g1
  refine WP.mono (copy_loop fa fb hlen hl0 (by rw [ea, eb]; exact Lay.disj hL hs)
    (by rw [ea, o₁.rd, o₁.wr]; exact Lay.covers ri (sepB_bounds hs).2)
    (by rw [eb, o₁.wr]; exact Lay.covers wj (sepB_bounds (sepB_symm hs)).2) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_⟩
  · refine (o₁.kept _).trans ⟨fun r hr _ => cs r hr, sp, rd, wr, ?_⟩
    rw [eb] at fr; exact fr
  · rw [eb, ea, o₁.mem] at hb; exact hb

/-! ## Decoding `t̂` -/

theorem decTArgs_ok {s : State} {P B : BitVec 32} {i : Nat} (h7 : s.gpr .r7 = P) (h4 : s.gpr .r4 = B)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 i) :
    WP isa (.block (at384 .r0 .r4 .r9 ++ slotAt .r1 .r9 (oPoly 0))) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = B + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 7 ∧
      s'.gpr .r1 = P + BitVec.ofNat 32 i <<< 10 + BitVec.ofNat 32 (oPoly 0) := by
  have e1 : encodable (BitVec.ofNat 32 (oPoly 0)) = true := by decide
  run_block [at384, slotAt, ptrTo, e1, h7, h4, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, -, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, ite_false]

/-- The polynomials `0` to `k - 1` decoded from the `384 k` bytes at offset `o` of buffer `i` (in `r4`). -/
structure DecInv (K : KemLay) (L : Lay) (i o : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r9] (L.RL [(0, 2048, 1024 * K.k)]) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  t : ∀ k < j, PolyIs s.mem (L.A 0 (oPoly k)) (decode12 (bytesAt s₀.mem (L.A i (o + 384 * k)) 384))

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem decT_slots : ∀ k < K.k, [((0 : Nat), oPoly k, (1024 : Nat))].all (fun w => [(0, 2048, 1024 * K.k)].any (subB0 w)) = true ∧
    (∀ k' < K.k, k' ≠ k → [((0 : Nat), oPoly k, (1024 : Nat))].all (sep0 (oPoly k') 1024) = true) := by
  intro k hk
  exact ⟨by kdecide, fun k' _ _ => by kdecide⟩

theorem decT_step {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h4 : s₀.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr)
    {j : Nat} (hj : j < K.k) {s : State} (h : DecInv K L i o s₀ j s) :
    WP isa K.decTBody s fun s' => DecInv K L i o s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = K.k) := by
  have hL := hc.ok
  have k4 := hK.k4
  have hc' := h.kx.ctx (by decide) hc
  obtain ⟨c_sub, c_sep⟩ := decT_slots hK j hj
  have g4 : s.gpr .r4 = L.ptr i + BitVec.ofNat 32 o := by rw [h.kx.cs .r4 (by decide) (by decide) (by decide), h4]
  refine WP.seq (WP.mono (decTArgs_ok hc'.r7 g4 h.r9) fun s₁ ⟨o₁, a0, a1⟩ => ?_)
  rw [at384_eq _ (by omega), ptr_add_add32] at a0
  rw [slot_eq _ (by offs), show 2048 + 1024 * 0 + 1024 * j = 2048 + 1024 * j by omega] at a1
  have hc₁ := hc'.only o₁
  have hsj : sepAll L.sizes (i, o + 384 * j, 384) [(0, 2048, 1024 * K.k)] = true :=
    sepAll_mono hs (inB_off (by omega)) (by kdecide)
  have hsep : sepB L.sizes (i, o + 384 * j, 384) (0, oPoly j, 1024) = true :=
    sepB_mono (List.all_eq_true.mp hsj _ (List.mem_singleton_self _)) (inB_refl _) (by
      simp only [inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)
  refine WP.seq (decode12L hL a0 a1 hsep (by rw [o₁.rd, o₁.wr, h.kx.rd, h.kx.wr]; exact hr) hc₁.buf0
    fun s₂ k₂ p₂ => ?_)
  have g9 : s₂.gpr .r9 = BitVec.ofNat 32 j := by
    rw [k₂.cs .r9 (by decide) (by decide), o₁.cs .r9 (by decide) (by decide), h.r9]
  refine WP.mono (count_ok (by omega) (by omega) (by kenc) g9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_⟩, z'⟩
  all_goals have K : KeptX [.r9] (L.RL [(0, oPoly j, 1024)]) s s' :=
    (o₁.x _ _).trans ((k₂.x _).trans (k'.mono (fun _ h => absurd h List.not_mem_nil)))
  · exact h.kx.trans (K.subL hc c_sub)
  · intro k hk
    have hb : bytesAt s.mem (L.A i (o + 384 * j)) 384 = bytesAt s₀.mem (L.A i (o + 384 * j)) 384 :=
      Lay.bytes_keep hL h.kx.frame hsj (by decide)
    by_cases e : k = j
    · subst e
      rw [o₁.mem, hb] at p₂
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₂
    · exact Lay.polyIs_keep hL K.frame (hc.sepAll0 (by offs) (c_sep k (by omega) e)) (h.t k (by omega))

omit hK in
theorem decT_init {L : Lay} {i o : Nat} {s₀ : State} :
    WP isa (.block [.mov .r9 (.imm 0)]) s₀ (DecInv K L i o s₀ 0) :=
  WP.mono (movc_ok .r9 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem decT_loop {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h4 : s₀.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr) {s : State}
    (h : DecInv K L i o s₀ 0 s) : WP isa (.loop K.decTBody .ne) s (DecInv K L i o s₀ K.k) :=
  wp_loop_ne (DecInv K L i o s₀) (N := K.k) hK.k1 (fun _ hj _ h => decT_step hK hc h4 hs hr hj h) (fun _ h => h) h

end

namespace Enc

/-! ## The buffers of K-PKE.Encrypt -/

/-- Where `encrypt` finds `ek` and `m`, and writes `c`: offsets in buffers. -/
structure EB where
  iE : Nat
  oE : Nat
  iM : Nat
  oM : Nat
  iC : Nat
  oC : Nat

/-- What `encrypt` changes in `scratch` and the stack: the polynomials and the
working spaces of the callees. -/
abbrev encW0 (K : KemLay) : List (Nat × Nat × Nat) :=
  [(0, 0, 840), (0, 952, 1), (0, 1024, 128), (0, 1216, 34), (0, 2048, 1024 * (3 * K.k + 5)), (0, K.oSample, 3072),
    (1, 0, 8)]

/-- What `encrypt` changes. -/
abbrev encW (K : KemLay) (b : EB) : List (Nat × Nat × Nat) := encW0 K ++ [(b.iC, b.oC, K.ctLen)]

/-- A state `encrypt` runs from. -/
structure EncPre (K : KemLay) (L : Lay) (b : EB) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  ctx : Ctx L s
  r4 : s.gpr .r4 = L.ptr b.iE + BitVec.ofNat 32 b.oE
  r5 : s.gpr .r5 = L.ptr b.iM + BitVec.ofNat 32 b.oM
  r8 : s.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC
  sE : sepAll L.sizes (b.iE, b.oE, K.ekLen) (encW0 K) = true
  sM : sepAll L.sizes (b.iM, b.oM, 32) (encW0 K) = true
  sC : sepAll L.sizes (b.iC, b.oC, K.ctLen) (encW0 K) = true
  wE : L.buf b.iE ∈ s.rd ++ s.wr
  wM : L.buf b.iM ∈ s.rd ++ s.wr
  wC : L.buf b.iC ∈ s.wr

/-- The entries of `Â` the products use, from `ρ` and `r`: `Â[i, j]`, or
`ŷ[i]` if its `SampleNTT` does not finish. -/
def aEnc (ρ r : List Byte) (i j : Nat) : Poly := effA true ρ j i (VG.Proof.MlKem.encY r i)

/-- Whether the `SampleNTT`s of the first `i` rows of `Â^⊺` (of `k` entries) finished. -/
def okEnc (k : Nat) (ρ : List Byte) (i : Nat) : Bool := (List.range i).all fun i' => okRow true ρ i' k

section
variable (K : KemLay) (L : Lay) (b : EB) (s₀ : State)

/-- `ek`. -/
abbrev ekB : List Byte := bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen
/-- `m`. -/
abbrev mB : List Byte := bytesAt s₀.mem (L.A b.iM b.oM) 32
/-- `r`. -/
abbrev rB : List Byte := bytesAt s₀.mem (L.A 0 oSigma) 32

/-- `ρ`. -/
abbrev ρE : List Byte := ekRho K.p (ekB K L b s₀)
/-- The entries of `Â` the products use. -/
abbrev aE : Nat → Nat → Poly := aEnc (ρE K L b s₀) (rB L s₀)
/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
abbrev okE (i : Nat) : Bool := okEnc K.k (ρE K L b s₀) i

end

theorem okE_succ (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) :
    okE K L b s₀ (i + 1) = (okE K L b s₀ i && okRow true (ρE K L b s₀) i K.k) := by
  simp only [okE, okEnc, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- Before the rows: what changes is within `encW0`. -/
abbrev EA (K : KemLay) (L : Lay) (s₀ s : State) : Prop := KeptX [.r9, .r10, .r11] (L.RL (encW0 K)) s₀ s

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

theorem EA.ctx {s : State} (h : EA K L s₀ s) : Ctx L s := KeptX.ctx h (by decide) hp.ctx

/-- The bytes of a part of a buffer apart from `encW0`. -/
theorem EA.bytes {s : State} (h : EA K L s₀ s) {i o l : Nat} (hs : sepAll L.sizes (i, o, l) (encW0 K) = true) :
    bytesAt s.mem (L.A i o) l = bytesAt s₀.mem (L.A i o) l := by
  have := sepAll_bounds hs
  have := hp.ctx.ok.fit i this.1
  exact Lay.bytes_keep hp.ctx.ok h.frame hs (by simp only [Lay.size] at this; omega)

theorem EA.ek {s : State} (h : EA K L s₀ s) {k n : Nat} (hk : k + n ≤ K.ekLen) :
    bytesAt s.mem (L.A b.iE (b.oE + k)) n = bytesAt s₀.mem (L.A b.iE (b.oE + k)) n :=
  EA.bytes hp h (sepAll_mono hp.sE (inB_off hk) (List.all_eq_true.mpr fun _ h => List.any_eq_true.mpr ⟨_, h, inB_refl _⟩))

omit hp in
theorem EA.reg {s : State} (h : EA K L s₀ s) {r : Reg} (hr : r ∈ [Reg.r4, .r5, .r7, .r8]) : s.gpr r = s₀.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact h.cs _ (by decide) (by decide) (by decide)

/-! ## `ρ` -/

theorem enc1_ok : WP isa (copy .r4 (384 * K.k) .r7 oSeed 32) s₀ fun s =>
    EA K L s₀ s ∧ Frame (L.RL [(0, oSeed, 32)]) s₀.mem s.mem ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have k4 := hK.k4
  have hs : sepB L.sizes (b.iE, b.oE + 384 * K.k, 32) (0, oSeed, 32) = true :=
    sepB_mono (List.all_eq_true.mp hp.sE (0, 1216, 34) (by simp)) (inB_off (by offs)) (by decide)
  refine WP.mono (copyLo hL (bo := b.oE) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ hp.r4 hp.ctx.r7 hK.encT
    (by decide) (by decide) (by decide) (by decide) hs hp.wE hp.ctx.buf0) fun s ⟨k, e⟩ =>
    ⟨(k.x _).subL hp.ctx (by kdecide), k.frame, e.trans ?_⟩
  show _ = ((bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen).drop (384 * K.k)).take 32
  rw [bytesAt_slice _ _ (by offs), add_ofNat_add]

/-! ## `t̂` -/

theorem enc2_ok {s₁ : State} (h₁ : EA K L s₀ s₁) (hρ : bytesAt s₁.mem (L.A 0 oSeed) 32 = ρE K L b s₀) {s : State}
    (h : DecInv K L b.iE b.oE s₁ K.k s) :
    EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ ∧
      ∀ k < K.k, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k) := by
  have hK := hp.wf
  refine ⟨h₁.trans ((h.kx.weaken (by simp)).subL hp.ctx (by kdecide)),
    (Lay.bytes_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by decide) (by kdecide)) (by decide)).trans hρ,
    fun k hk => ?_⟩
  have := h.t k hk
  rw [EA.ek hp h₁ (by offs)] at this
  show PolyIs _ _ (decode12 (((bytesAt s₀.mem (L.A b.iE b.oE) K.ekLen).drop (384 * k)).take 384))
  rw [bytesAt_slice _ _ (by offs), add_ofNat_add]; exact this

/-! ## The `PRF`s -/

omit hp in
theorem prf_ek (hK : K.WF) : (prfLW K 0 K.k).all (fun w => (encW0 K).any (subB0 w)) = true ∧
    (prfLW K K.k (2 * K.k + 1)).all (fun w => (encW0 K).any (subB0 w)) = true ∧
    (prfLW K 0 K.k).all (sep0 oSeed 32) = true ∧ (prfLW K K.k (2 * K.k + 1)).all (sep0 oSeed 32) = true ∧
    (∀ k < K.k, (prfLW K 0 K.k).all (sep0 (oPoly k) 1024) = true) ∧
    (∀ k < 2 * K.k, (prfLW K K.k (2 * K.k + 1)).all (sep0 (oPoly k) 1024) = true) ∧
    (encW0 K).all (sep0 oSigma 32) = true := by
  refine ⟨by kdecide, by kdecide, by kdecide, by kdecide, fun k hk => by kdecide, fun k hk => by kdecide, by kdecide⟩

theorem enc3_ok {s₂ : State} (h₂ : EA K L s₀ s₂) (hρ : bytesAt s₂.mem (L.A 0 oSeed) 32 = ρE K L b s₀)
    (ht : ∀ k < K.k, PolyIs s₂.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k)) :
    WP isa (K.prfLoop true 0 K.k) s₂ fun s => EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ ∧
      (∀ k < K.k, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k)) ∧
      ∀ j < K.k, PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀) j) := by
  have hK := hp.wf
  have hc := EA.ctx hp h₂
  obtain ⟨c1, -, c3, -, c5, -, c7⟩ := prf_ek hK
  refine WP.mono (prfLoop_ok hK hc true (N₀ := 0) (N₁ := K.k) hK.k1 (by omega)
    (EA.bytes hp h₂ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, fun j hj => ?_⟩
  · exact h₂.trans ((k.weaken (by simp)).subL hp.ctx c1)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c3) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs) (c5 k' hk')) (ht k' hk')
  · exact p j (Nat.zero_le _) hj

theorem enc4_ok {s₃ : State} (h₃ : EA K L s₀ s₃) (hρ : bytesAt s₃.mem (L.A 0 oSeed) 32 = ρE K L b s₀)
    (hv : ∀ k < 2 * K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - K.k))) :
    WP isa (K.prfLoop false K.k (2 * K.k + 1)) s₃ fun s => EA K L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀ ∧
      (∀ k < 2 * K.k, PolyIs s.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
        else VG.Proof.MlKem.encY (rB L s₀) (k - K.k))) ∧
      ∀ N, K.k ≤ N → N < 2 * K.k + 1 → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀) N) := by
  have hK := hp.wf
  have hc := EA.ctx hp h₃
  obtain ⟨-, c2, -, c4, -, c6, c7⟩ := prf_ek hK
  refine WP.mono (prfLoop_ok hK hc false (N₀ := K.k) (N₁ := 2 * K.k + 1) (by omega) (by omega)
    (EA.bytes hp h₃ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, p⟩
  · exact h₃.trans ((k.weaken (by simp)).subL hp.ctx c2)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c4) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs) (c6 k' hk')) (hv k' hk')

/-! ## `μ` -/

omit hp in
theorem muArgs_ok (hK : K.WF) {s : State} {P M : BitVec 32} (h7 : s.gpr .r7 = P) (h5 : s.gpr .r5 = M) :
    WP isa (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly (3 * K.k + 1))]) s
      fun s' => Only s s' ∧ s'.gpr .r0 = M ∧ s'.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧
        s'.gpr .r2 = BitVec.ofNat 32 1 ∧ s'.gpr .r3 = P + BitVec.ofNat 32 (oPoly (3 * K.k + 1)) := by
  have e1 : encodable (32 : BitVec 32) = true := by decide
  have e2 : encodable (1 : BitVec 32) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 (oPoly (3 * K.k + 1))) = true := hK.enc (by omega)
  run_block [ptrTo, e1, e2, e3, h7, h5]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem enc5a_ok {s₄ : State} (h₄ : EA K L s₀ s₄) :
    WP isa (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly (3 * K.k + 1))]) s₄
      fun s => (EA K L s₀ s ∧ s.mem = s₄.mem) ∧ s.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM ∧
        s.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧ s.gpr .r2 = BitVec.ofNat 32 1 ∧
        s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1)) := by
  have hc := EA.ctx hp h₄
  have g5 : s₄.gpr .r5 = L.ptr b.iM + BitVec.ofNat 32 b.oM := by rw [EA.reg h₄ (by simp), hp.r5]
  exact WP.mono (muArgs_ok hp.wf hc.r7 g5) fun s₁ ⟨o₁, a0, a1, a2, a3⟩ =>
    ⟨⟨h₄.trans (o₁.x _ _), o₁.mem⟩, a0, a1, a2, a3⟩

theorem enc5b_ok {s₄ s : State} (h₄ : EA K L s₀ s₄) (h : EA K L s₀ s ∧ s.mem = s₄.mem)
    (a0 : s.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM) (a1 : s.gpr .r1 = BitVec.ofNat 32 (32 * 1))
    (a2 : s.gpr .r2 = BitVec.ofNat 32 1) (a3 : s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly (3 * K.k + 1))) :
    WP isa callDecompress s fun s' => EA K L s₀ s' ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) s₄.mem s'.mem ∧
      PolyIs s'.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀)) := by
  have hK := hp.wf
  have hc := EA.ctx hp h.1
  have hs : sepB L.sizes (b.iM, b.oM, 32 * 1) (0, oPoly (3 * K.k + 1), 1024) = true :=
    sepB_mono (List.all_eq_true.mp hp.sM (0, 2048, 1024 * (3 * K.k + 5)) (by simp)) (inB_refl _) (by kdecide)
  refine decompressL hp.ctx.ok a0 a1 a2 a3 (by decide) hs (by rw [h.1.rd, h.1.wr]; exact hp.wM)
    hc.buf0 fun s' k p => ⟨?_, ?_, ?_⟩
  · exact h.1.trans ((k.x _).subL hp.ctx (by kdecide))
  · rw [← h.2]; exact k.frame
  · rw [h.2, show 32 * 1 = 32 from rfl, EA.bytes hp h₄ hp.sM] at p; exact p

end

/-! ## What the rows and `v` use -/

theorem sepAll_left {sz : List Nat} {a a' : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)} (h : sepAll sz a W = true)
    (ha : inB a' a = true) : sepAll sz a' W = true :=
  sepAll_mono h ha (List.all_eq_true.mpr fun w hw => List.any_eq_true.mpr ⟨w, hw, inB_refl w⟩)

theorem sepB_same {sz : List Nat} {i o l o' l' : Nat} (hb : i < sz.length) (h1 : o + l ≤ sz.getD i 0)
    (h2 : o' + l' ≤ sz.getD i 0) (hd : o + l ≤ o' ∨ o' + l' ≤ o) : sepB sz (i, o, l) (i, o', l') = true := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false,
    false_or]
  omega

/-- The polynomials the rows and `v` use: `ρ`, `t̂`, `ŷ`, `e₁`, `e₂` and `μ`. -/
structure EData (K : KemLay) (L : Lay) (b : EB) (s₀ s : State) : Prop where
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = ρE K L b s₀
  v : ∀ k < 2 * K.k, PolyIs s.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
    else VG.Proof.MlKem.encY (rB L s₀) (k - K.k))
  e : ∀ N, K.k ≤ N → N < 2 * K.k + 1 → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀) N)
  mu : PolyIs s.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀))

theorem EData.keep {K : KemLay} {L : Lay} {b : EB} {s₀ s s' : State} (hL : L.Ok) (h : EData K L b s₀ s)
    {W : List (Nat × Nat × Nat)} (hf : Frame (L.RL W) s.mem s'.mem) (h1 : sepAll L.sizes (0, 1216, 32) W = true)
    (h2 : sepAll L.sizes (0, 2048, 1024 * (3 * K.k + 2)) W = true) : EData K L b s₀ s' := by
  have hp : ∀ k < 3 * K.k + 2, sepAll L.sizes (0, oPoly k, 1024) W = true := fun k hk =>
    sepAll_left h2 (by simp only [inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)
  exact ⟨(Lay.bytes_keep hL hf h1 (by decide)).trans h.rho, fun k hk => Lay.polyIs_keep hL hf (hp k (by omega)) (h.v k hk),
    fun N h3 h7 => Lay.polyIs_keep hL hf (hp (K.k + N) (by omega)) (h.e N h3 h7),
    Lay.polyIs_keep hL hf (hp (3 * K.k + 1) (by omega)) h.mu⟩

/-- After the rows `i' < i`. -/
structure ERow (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) : Prop where
  kx : KeptX [.r9, .r10, .r11] (L.RL (encW K b)) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if okE K L b s₀ i then 1 else 0
  d : EData K L b s₀ s
  c : ∀ i' < i, bytesAt s.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i')

/-- In row `i` (from `s`), with the sum `f`. -/
structure RB (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) (f : Poly) (s' : State) : Prop where
  kx : KeptX [.r9, .r10, .r11] (L.RL (rowW K)) s s'
  r9 : s'.gpr .r9 = BitVec.ofNat 32 i
  r11 : s'.gpr .r11 = if okE K L b s₀ (i + 1) then 1 else 0
  acc : PolyIs s'.mem (L.A 0 K.oAcc) f

/-- In row `i`, after its encoding. -/
structure RC (K : KemLay) (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) (s' : State) : Prop where
  kx : KeptX [.r9, .r10, .r11] (L.RL (rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)])) s s'
  r9 : s'.gpr .r9 = BitVec.ofNat 32 i
  r11 : s'.gpr .r11 = if okE K L b s₀ (i + 1) then 1 else 0
  cb : bytesAt s'.mem (L.A b.iC (b.oC + K.uLen * i)) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i)

theorem row_facts {K : KemLay} (hK : K.WF) : (rowW K).all (fun w => (encW0 K).any (subB0 w)) = true ∧
    (rowW K).all (fun w => (encW0 K).any (inB w)) = true ∧
    (rowW K).all (sep0 1216 32) = true ∧ (rowW K).all (sep0 2048 (1024 * (3 * K.k + 2))) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (fun w => (rowW K).any (subB0 w)) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat))].all (fun w => (rowW K).any (subB0 w)) = true ∧
    (∀ i < K.k, (rowW K).all (sep0 (oPoly (K.k + (K.k + i))) 1024) = true) := by
  refine ⟨by kdecide, by kdecide, by kdecide, by kdecide, by kdecide, by kdecide, fun i hi => by kdecide⟩

/-- A `u[i]` within `c`. -/
theorem uSlot {K : KemLay} {i : Nat} (hi : i < K.k) : K.uLen * i + K.uLen ≤ K.ctLen := by
  have : K.uLen * i + K.uLen ≤ K.uLen * K.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  simp only [KemLay.ctLen]; omega

/-- Two `u[i]` within `c` are apart. -/
theorem uApart {K : KemLay} {i i' : Nat} (h : i' ≠ i) :
    K.uLen * i' + K.uLen ≤ K.uLen * i ∨ K.uLen * i + K.uLen ≤ K.uLen * i' := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)
  · exact .inr (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

/-- The part `[k, k + n)` of `c` apart from regions inside `encW0`. -/
theorem cSep {k n : Nat} (hk : k + n ≤ K.ctLen) {W : List (Nat × Nat × Nat)}
    (hW : W.all (fun w => (encW0 K).any (inB w)) = true) : sepAll L.sizes (b.iC, b.oC + k, n) W = true :=
  sepAll_mono hp.sC (inB_off hk) hW

theorem cData {k n : Nat} (hk : k + n ≤ K.ctLen) :
    sepAll L.sizes (0, 1216, 32) [(b.iC, b.oC + k, n)] = true ∧
      sepAll L.sizes (0, 2048, 1024 * (3 * K.k + 2)) [(b.iC, b.oC + k, n)] = true := by
  have hK := hp.wf
  have c1 := cSep hp hk (W := [(0, 1216, 32)]) (by kdecide)
  have c2 := cSep hp hk (W := [(0, 2048, 1024 * (3 * K.k + 2))]) (by kdecide)
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at c1 c2 ⊢
  exact ⟨sepB_symm c1, sepB_symm c2⟩

theorem cBound : b.iC < L.sizes.length ∧ b.oC + K.ctLen ≤ L.size b.iC := sepAll_bounds hp.sC

theorem ERow.rowPre {i : Nat} (hi : i < K.k) {s : State} (h : ERow K L b s₀ i s) :
    RowPre K L (ρE K L b s₀) (VG.Proof.MlKem.encY (rB L s₀)) i (okE K L b s₀ i) s :=
  ⟨hp.wf, h.kx.ctx (by decide) hp.ctx, hi, h.r9, h.r11, h.d.rho, fun j hj => by
    have := h.d.v (K.k + j) (by omega)
    have e : ¬ (K.k + j < K.k) := by omega
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega] at this
    exact this⟩

section
variable {i : Nat} (hi : i < K.k) {s : State} (h : ERow K L b s₀ i s)
include hi h

omit hi in
theorem RB.ctx {f : Poly} {s' : State} (r : RB K L b s₀ i s f s') : Ctx L s' :=
  r.kx.ctx (by decide) (h.kx.ctx (by decide) hp.ctx)

omit hi in
theorem er2_ok {s₁ : State}
    (r : RowInv K L true (ρE K L b s₀) (VG.Proof.MlKem.encY (rB L s₀)) i (okE K L b s₀ i) s K.k s₁) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 K.oNtt]) s₁ fun s₂ =>
      RB K L b s₀ i s (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀ j i) (VG.Proof.MlKem.encY (rB L s₀)) K.k) s₂ ∧
      s₂.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ s₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt := by
  have hK := hp.wf
  have hc₁ := r.kx.ctx (by decide) (h.kx.ctx (by decide) hp.ctx)
  refine WP.mono (accArgs_ok hc₁.r7 (by kenc) (by kenc)) fun s₂ ⟨o₂, a0, a1⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, a0, a1⟩
  · exact (r.kx.weaken (by simp)).trans (o₂.x _ _)
  · rw [o₂.cs .r9 (by decide) (by decide), r.kx.cs .r9 (by decide) (by decide) (by decide), h.r9]
  · rw [o₂.cs .r11 (by decide) (by decide), r.r11, okE_succ]
  · rw [o₂.mem, ← rowAcc_eq]; exact r.acc

omit hi in
theorem er3_ok {f : Poly} {s₂ : State} (r : RB K L b s₀ i s f s₂) (g0 : s₂.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc)
    (g1 : s₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) : WP isa callNttInv s₂ (RB K L b s₀ i s (nttInv f)) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, c5, -, -⟩ := row_facts hK
  exact nttInvL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 hc.buf0 r.acc
    fun s₃ k₃ p₃ => ⟨r.kx.trans ((k₃.x _).subL hp.ctx c5), by rw [k₃.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₃.cs .r11 (by decide) (by decide), r.r11], p₃⟩

theorem er4_ok {f : Poly} {s₃ : State} (r : RB K L b s₀ i s f s₃) :
    WP isa (.block (ptrTo .r0 .r7 K.oAcc :: slotAt .r1 .r9 (oPoly (2 * K.k)))) s₃ fun s₄ => RB K L b s₀ i s f s₄ ∧
      s₄.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
      s₄.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i))) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  refine WP.mono (ptrSlot_ok (i := i) hc.r7 r.r9 (by kenc) (by kenc)) fun s₄ ⟨o₄, a0, a1⟩ => ?_
  rw [slot_eq _ (by offs), show oPoly (2 * K.k) + 1024 * i = oPoly (K.k + (K.k + i)) by offs] at a1
  exact ⟨⟨r.kx.trans (o₄.x _ _), by rw [o₄.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₄.cs .r11 (by decide) (by decide), r.r11], by rw [o₄.mem]; exact r.acc⟩, a0, a1⟩

theorem er5_ok {f : Poly} {s₄ : State} (r : RB K L b s₀ i s f s₄) (g0 : s₄.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc)
    (g1 : s₄.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (K.k + (K.k + i)))) :
    WP isa callAdd s₄ (RB K L b s₀ i s (add f (VG.Proof.MlKem.cbd (rB L s₀) (K.k + i)))) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, -, c6, c7⟩ := row_facts hK
  have he : PolyIs s₄.mem (L.A 0 (oPoly (K.k + (K.k + i)))) (VG.Proof.MlKem.cbd (rB L s₀) (K.k + i)) :=
    Lay.polyIs_keep hp.ctx.ok r.kx.frame (hc.sepAll0 (by offs) (c7 i hi)) (h.d.e (K.k + i) (by omega) (by omega))
  exact addL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 (mem_rd_wr hc.buf0) r.acc he
    fun s₅ k₅ p₅ => ⟨r.kx.trans ((k₅.x _).subL hp.ctx c6), by rw [k₅.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₅.cs .r11 (by decide) (by decide), r.r11], p₅⟩

omit hp hi h in
theorem cArgs_ok (hK : K.WF) {s : State} {P C : BitVec 32} {i : Nat} (h7 : s.gpr .r7 = P) (h8 : s.gpr .r8 = C)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 i) :
    WP isa (.block (([ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.du))] : List Instr) ++
      K.atU .r2 .r8 .r9 ++ ([.mov .r3 (.imm (BitVec.ofNat 32 K.uLen))] : List Instr))) s
      fun s' => Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 K.oAcc ∧ s'.gpr .r1 = BitVec.ofNat 32 K.du ∧
        s'.gpr .r2 = C + BitVec.ofNat 32 i * BitVec.ofNat 32 K.uLen ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * K.du) := by
  have e1 : encodable (BitVec.ofNat 32 K.oAcc) = true := hK.enc (by omega)
  have e2 := hK.encDu
  have e3 := hK.encU
  rw [WP.block_append_iff, WP.block_append_iff]
  have hb : WP isa (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.du))]) s fun s₁ =>
      s₁.gpr .r0 = P + BitVec.ofNat 32 K.oAcc ∧ s₁.gpr .r1 = BitVec.ofNat 32 K.du ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.sp = s.sp := by
    run_block [ptrTo, e1, e2, h7]
    exact ⟨trivial, trivial, fun r h0 h1 => by rw [ite_eq_right h1, ite_eq_right h0], trivial⟩
  refine WP.mono hb fun s₁ ⟨a0, a1, o₁, m₁, rd₁, wr₁, sp₁⟩ => WP.mono (atU_ok hK (d := .r2) (by decide) s₁)
    fun s₂ ⟨a2, o₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  run_block [e3]
  refine ⟨⟨fun r hr hl => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁]⟩,
    by rw [o₂ .r0 (by decide), a0], by rw [o₂ .r1 (by decide), a1], ?_, trivial⟩
  · obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
    show (if r = .r3 then _ else s₂.gpr r) = s.gpr r
    rw [ite_eq_right m3, o₂ r m2, o₁ r m0 m1]
  · rw [a2, o₁ .r8 (by decide) (by decide), h8, o₁ .r9 (by decide) (by decide), h9]

omit hi in
theorem er6_ok {f : Poly} {s₅ : State} (r : RB K L b s₀ i s f s₅) :
    WP isa (.block (([ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.du))] : List Instr) ++
      K.atU .r2 .r8 .r9 ++ ([.mov .r3 (.imm (BitVec.ofNat 32 K.uLen))] : List Instr))) s₅
      fun s₆ => RB K L b s₀ i s f s₆ ∧ s₆.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        s₆.gpr .r1 = BitVec.ofNat 32 K.du ∧ s₆.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * i) ∧
        s₆.gpr .r3 = BitVec.ofNat 32 (32 * K.du) := by
  have hc := r.ctx hp h
  have g8 : s₅.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC := by
    rw [r.kx.cs .r8 (by decide) (by decide) (by decide), h.kx.cs .r8 (by decide) (by decide) (by decide), hp.r8]
  refine WP.mono (cArgs_ok hp.wf hc.r7 g8 r.r9) fun s₆ ⟨o₆, a0, a1, a2, a3⟩ => ?_
  rw [atU_eq, ptr_add_add32] at a2
  exact ⟨⟨r.kx.trans (o₆.x _ _), by rw [o₆.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₆.cs .r11 (by decide) (by decide), r.r11], by rw [o₆.mem]; exact r.acc⟩, a0, a1, a2, a3⟩

theorem er7_ok {s₆ : State} (r : RB K L b s₀ i s (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i) s₆)
    (g0 : s₆.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s₆.gpr .r1 = BitVec.ofNat 32 K.du)
    (g2 : s₆.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * i)) (g3 : s₆.gpr .r3 = BitVec.ofNat 32 (32 * K.du)) :
    WP isa K.callCU s₆ (RC K L b s₀ i s) := by
  have hK := hp.wf
  have hc := r.ctx hp h
  have hs : sepB L.sizes (0, K.oAcc, 1024) (b.iC, b.oC + K.uLen * i, 32 * K.du) = true := by
    have := cSep hp (k := K.uLen * i) (n := K.uLen) (uSlot hi) (W := [(0, K.oAcc, 1024)]) (by kdecide)
    simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact sepB_symm this
  exact hp.calls.cu hp.ctx.ok g0 g1 g2 g3 (.inl rfl) hs (mem_rd_wr hc.buf0)
    (by rw [r.kx.wr, h.kx.wr]; exact hp.wC) r.acc fun s₇ k₇ p₇ =>
    ⟨(r.kx.monoL (by simp)).trans ((k₇.x _).monoL (by simp)), by rw [k₇.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₇.cs .r11 (by decide) (by decide), r.r11], p₇⟩

theorem er8_ok {s₇ : State} (r : RC K L b s₀ i s s₇) :
    WP isa (.block (count .r9 K.k)) s₇ fun s' => ERow K L b s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨r1, r2, r3, r4, -, -, -⟩ := row_facts hK
  obtain ⟨cb1, cb2⟩ := cBound hp
  refine WP.mono (count_ok (by omega) (by omega) (by kenc) r.r9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.r9, .r10, .r11] (L.RL (rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)])) s s' :=
    r.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · refine h.kx.trans ?_
    have e : ∀ w ∈ L.RL (rowW K ++ [(b.iC, b.oC + K.uLen * i, K.uLen)]), ∃ w' ∈ L.RL (encW K b), Region.Sub w w' := by
      intro w hw
      simp only [Lay.RL, List.map_append, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨w', hw', hs⟩ := hp.ctx.subL r1 w hw
        exact ⟨w', by simp only [Lay.RL, List.map_append, List.mem_append]; exact .inl hw', hs⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hw; subst hw
        have := uSlot (K := K) hi
        exact ⟨L.R b.iC b.oC K.ctLen, by simp, Lay.R_sub_R hL cb1 (by omega) (by omega) cb2⟩
    exact K'.sub e
  · rw [k'.cs .r11 (by decide) (by decide) (by decide), r.r11]
  · obtain ⟨d1, d2⟩ := cData hp (k := K.uLen * i) (n := K.uLen) (uSlot hi)
    exact h.d.keep hL K'.frame (sepAll_append (hp.ctx.sepAll0 (by decide) r3) d1)
      (sepAll_append (hp.ctx.sepAll0 (by offs) r4) d2)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by offs)).trans r.cb
    · have u1 := uSlot (K := K) (i := i') (by omega)
      have u2 := uSlot (K := K) hi
      have s1 : sepAll L.sizes (b.iC, b.oC + K.uLen * i', K.uLen) (rowW K) = true := cSep hp (by omega) r2
      have s2 : sepAll L.sizes (b.iC, b.oC + K.uLen * i', K.uLen) [(b.iC, b.oC + K.uLen * i, K.uLen)] = true := by
        simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true]
        exact sepB_same cb1 (by simp only [Lay.size] at cb2; omega) (by simp only [Lay.size] at cb2; omega)
          (by have := uApart (K := K) e; omega)
      rw [← h.c i' (by omega)]
      exact Lay.bytes_keep hL K'.frame (sepAll_append s1 s2) (by offs)

end

theorem encRow_step {i : Nat} (hi : i < K.k) {s : State} (h : ERow K L b s₀ i s) :
    WP isa K.encRowBody s fun s' => ERow K L b s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = K.k) :=
  WP.seq (WP.mono (rowSum_ok (transpose := true) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (er2_ok hp h r₁) fun _ ⟨r₂, a0, a1⟩ =>
    WP.seq (WP.mono (er3_ok hp h r₂ a0 a1) fun _ r₃ =>
    WP.seq (WP.mono (er4_ok hp hi h r₃) fun _ ⟨r₄, b0, b1⟩ =>
    WP.seq (WP.mono (er5_ok hp hi h r₄ b0 b1) fun _ r₅ =>
    WP.seq (WP.mono (er6_ok hp h r₅) fun _ ⟨r₆, c0, c1, c2, c3⟩ =>
    WP.seq (WP.mono (er7_ok hp hi h r₆ c0 c1 c2 c3) fun _ r₇ => er8_ok hp hi h r₇)))))))

end

/-! ## `v` -/

/-- What the steps of `v` keep: what the rows left. -/
structure VEnv (K : KemLay) (L : Lay) (b : EB) (s₀ s : State) : Prop where
  kx : KeptX [.r9, .r10, .r11] (L.RL (encW K b)) s₀ s
  r11 : s.gpr .r11 = if okE K L b s₀ K.k then 1 else 0
  d : EData K L b s₀ s
  c : ∀ i' < K.k, bytesAt s.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
    compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i')

/-- A region of `scratch` the steps of `v` may change. -/
def vOK (K : KemLay) (w : Nat × Nat × Nat) : Bool :=
  (encW0 K).any (subB0 w) && (encW0 K).any (inB w) && sep0 1216 32 w && sep0 2048 (1024 * (3 * K.k + 2)) w

theorem vOK_facts {K : KemLay} (hK : K.WF) : (dotW K).all (vOK K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (vOK K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat))].all (vOK K) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [List.all_cons, List.all_nil, vOK, Bool.and_true]; kdecide)

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

theorem VEnv.keep {s s' : State} (h : VEnv K L b s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (k : KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.r9, .r10]) (hW : W.all (vOK K) = true) : VEnv K L b s₀ s' := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  have w1 : W.all (fun w => (encW0 K).any (subB0 w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.1.1
  have w2 : W.all (fun w => (encW0 K).any (inB w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.1.2
  have w3 : W.all (sep0 1216 32) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.2
  have w4 : W.all (sep0 2048 (1024 * (3 * K.k + 2))) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.2
  refine ⟨h.kx.trans ?_, ?_, h.d.keep hL k.frame (hc.sepAll0 (by decide) w3) (hc.sepAll0 (by offs) w4),
    fun i' hi' => (Lay.bytes_keep hL k.frame (cSep hp (uSlot hi') w2) (by simp only [KemLay.uLen]; have := hK.du; omega)).trans
      (h.c i' hi')⟩
  · refine ((k.weaken fun x hx' => ?_).subL hp.ctx w1).monoL fun w hw => List.mem_append_left _ hw
    have := hx x hx'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl <;> simp
  · rw [k.cs .r11 (by decide) (by decide) (fun hm => by have := hx _ hm; simp at this), h.r11]

omit hp in
theorem ERow.venv {s : State} (h : ERow K L b s₀ K.k s) : VEnv K L b s₀ s := ⟨h.kx, h.r11, h.d, h.c⟩

theorem ev1_ok {s : State} (h : VEnv K L b s₀ s) :
    WP isa K.dot s fun s' => VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc)
      (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀)) (VG.Proof.MlKem.encY (rB L s₀)) K.k) := by
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  refine WP.mono (dot_ok hK hc (fun j hj => ?_) (fun j hj => ?_)) fun s' ⟨k, p⟩ =>
    ⟨h.keep hp k (by simp) (vOK_facts hK).1, p⟩
  · have := h.d.v j (by omega); simp only [hj, ↓reduceIte] at this; exact this
  · have := h.d.v (K.k + j) (by omega)
    have e : ¬ (K.k + j < K.k) := by omega
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega] at this
    exact this

theorem evArgs_ok {s : State} {f : Poly} (h : VEnv K L b s₀ s) (hf : PolyIs s.mem (L.A 0 K.oAcc) f) {o : Nat}
    (he : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, ptrTo .r1 .r7 o]) s fun s' => (VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) f) ∧
      s'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧ s'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 o := by
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) hp.ctx
  exact WP.mono (accArgs_ok hc.r7 (by kenc) he) fun s' ⟨o', a0, a1⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl, by rw [o'.mem]; exact hf⟩, a0, a1⟩

theorem ev3_ok {s : State} {f : Poly} (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f)
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 K.oNtt) :
    WP isa callNttInv s fun s' => VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) (nttInv f) := by
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  exact nttInvL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 hc.buf0 h.2
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (vOK_facts hK).2.1, p⟩

theorem evAdd_ok {s : State} {f g : Poly} {k : Nat} (hk : k = 3 * K.k ∨ k = 3 * K.k + 1)
    (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f) (hg : PolyIs s.mem (L.A 0 (oPoly k)) g)
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly k)) :
    WP isa callAdd s fun s' => VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) (add f g) := by
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  exact addL hp.ctx.ok g0 g1 (hc.sep00 (by offs) (by rcases hk with rfl | rfl <;> offs)
    (by rcases hk with rfl | rfl <;> offs)) hc.buf0 (mem_rd_wr hc.buf0) h.2 hg
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (vOK_facts hK).2.2, p⟩

omit hp in
theorem vArgs_ok (hK : K.WF) {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h8 : s.gpr .r8 = C) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r2 .r8 (K.uLen * K.k),
      .mov .r3 (.imm (BitVec.ofNat 32 K.vLen))]) s
      fun s' => Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 K.oAcc ∧ s'.gpr .r1 = BitVec.ofNat 32 K.dv ∧
        s'.gpr .r2 = C + BitVec.ofNat 32 (K.uLen * K.k) ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * K.dv) := by
  have e1 : encodable (BitVec.ofNat 32 K.oAcc) = true := hK.enc (by omega)
  have e2 := hK.encDv
  have e3 := hK.encVo
  have e4 := hK.encV
  run_block [ptrTo, e1, e2, e3, e4, h7, h8]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem ev8_ok {s : State} {f : Poly} (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) f) :
    WP isa (.block [ptrTo .r0 .r7 K.oAcc, .mov .r1 (.imm (BitVec.ofNat 32 K.dv)), ptrTo .r2 .r8 (K.uLen * K.k),
      .mov .r3 (.imm (BitVec.ofNat 32 K.vLen))]) s
      fun s' => (VEnv K L b s₀ s' ∧ PolyIs s'.mem (L.A 0 K.oAcc) f) ∧ s'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc ∧
        s'.gpr .r1 = BitVec.ofNat 32 K.dv ∧ s'.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * K.k) ∧
        s'.gpr .r3 = BitVec.ofNat 32 (32 * K.dv) := by
  have hc := h.1.kx.ctx (by decide) hp.ctx
  have g8 : s.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC := by
    rw [h.1.kx.cs .r8 (by decide) (by decide) (by decide), hp.r8]
  exact WP.mono (vArgs_ok hp.wf hc.r7 g8) fun s' ⟨o', a0, a1, a2, a3⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl, by rw [o'.mem]; exact h.2⟩, a0, a1,
      by rw [a2, ptr_add_add32], a3⟩

omit hp in
/-- `c * k` bytes as `k` pieces of `c`. -/
theorem bytes_catK (m : Mem) (p : Addr) (c : Nat) :
    ∀ k, bytesAt m p (c * k) = VG.Proof.MlKem.KPke.catK (fun i => bytesAt m (p + BitVec.ofNat 64 (c * i)) c) k
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, bytesAt_add, bytes_catK m p c k]
    exact (VG.Proof.MlKem.KPke.foldK_succ List.nil_append _ k).symm

omit hp in
theorem catK_congr {f g : Nat → List Byte} : ∀ {k}, (∀ i < k, f i = g i) →
    VG.Proof.MlKem.KPke.catK f k = VG.Proof.MlKem.KPke.catK g k
  | 0, _ => rfl
  | k + 1, h => by
    show VG.Proof.MlKem.KPke.foldK (· ++ ·) [] f (k + 1) = VG.Proof.MlKem.KPke.foldK (· ++ ·) [] g (k + 1)
    rw [VG.Proof.MlKem.KPke.foldK_succ List.nil_append, VG.Proof.MlKem.KPke.foldK_succ List.nil_append]
    exact congrArg₂ (· ++ ·) (catK_congr fun i hi => h i (by omega)) (h k (by omega))

theorem ev9_ok {s : State} (h : VEnv K L b s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc)
      (VG.Proof.MlKem.KPke.encV K.p (ekB K L b s₀) (mB L b s₀) (rB L s₀)))
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 K.oAcc) (g1 : s.gpr .r1 = BitVec.ofNat 32 K.dv)
    (g2 : s.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + K.uLen * K.k)) (g3 : s.gpr .r3 = BitVec.ofNat 32 (32 * K.dv)) :
    WP isa K.callCU s fun s' => KeptX [.r9, .r10, .r11] (L.RL (encW K b)) s₀ s' ∧
      s'.gpr .r11 = (if okE K L b s₀ K.k then 1 else 0) ∧
      bytesAt s'.mem (L.A b.iC b.oC) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (aE K L b s₀) (ekB K L b s₀) (mB L b s₀) (rB L s₀) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  have hc := h.1.kx.ctx (by decide) hp.ctx
  obtain ⟨cb1, cb2⟩ := cBound hp
  have hs : sepB L.sizes (0, K.oAcc, 1024) (b.iC, b.oC + K.uLen * K.k, 32 * K.dv) = true := by
    have := cSep hp (k := K.uLen * K.k) (n := K.vLen) (by simp only [KemLay.ctLen]; omega) (W := [(0, K.oAcc, 1024)])
      (by kdecide)
    simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact sepB_symm this
  have ect : K.ctLen = K.uLen * K.k + 32 * K.dv := rfl
  have eu : K.uLen = 32 * K.du := rfl
  have du := hK.du
  simp only [Lay.size] at cb2
  refine hp.calls.cu hL g0 g1 g2 g3 (.inr rfl) hs (mem_rd_wr hc.buf0)
    (by rw [h.1.kx.wr]; exact hp.wC) h.2 fun s' k p => ⟨?_, ?_, ?_⟩
  · refine h.1.kx.trans ((k.x _).sub fun r hr => ?_)
    simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact ⟨L.R b.iC b.oC K.ctLen, by simp, Lay.R_sub_R hL cb1 (by omega) (by omega) cb2⟩
  · rw [k.cs .r11 (by decide) (by decide), h.1.r11]
  · have keep : ∀ i' < K.k, bytesAt s'.mem (L.A b.iC (b.oC + K.uLen * i')) K.uLen =
        compressEncode K.du (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀) (rB L s₀) i') := fun i' hi' => by
      have u1 := uSlot (K := K) hi'
      have u2 : K.uLen * i' + K.uLen ≤ K.uLen * K.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi'
      rw [← h.1.c i' hi']
      refine Lay.bytes_keep hL k.frame ?_ (by omega)
      simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true]
      exact sepB_same cb1 (by omega) (by omega) (by omega)
    simp only [Lay.A] at keep p ⊢
    rw [KemLay.ctLen, bytesAt_add, bytes_catK, add_ofNat_add, VG.Proof.MlKem.KPke.ct]
    refine congrArg₂ (· ++ ·) (catK_congr fun i hi => ?_) p
    rw [add_ofNat_add]; exact keep i hi

end

/-! ## The whole of K-PKE.Encrypt -/

theorem mu_sep {K : KemLay} (hK : K.WF) :
    (∀ k < 2 * K.k, [((0 : Nat), oPoly (3 * K.k + 1), (1024 : Nat))].all (sep0 (oPoly k) 1024) = true) ∧
    (∀ N < 2 * K.k + 1, [((0 : Nat), oPoly (3 * K.k + 1), (1024 : Nat))].all (sep0 (oPoly (K.k + N)) 1024) = true) :=
  ⟨fun k hk => by kdecide, fun N hN => by kdecide⟩

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀ : State} (hp : EncPre K L b s₀)
include hp

theorem dec_pre {s₁ : State} (e₁ : EA K L s₀ s₁) :
    Ctx L s₁ ∧ s₁.gpr .r4 = L.ptr b.iE + BitVec.ofNat 32 b.oE ∧
      sepAll L.sizes (b.iE, b.oE, 384 * K.k) [(0, 2048, 1024 * K.k)] = true ∧ L.buf b.iE ∈ s₁.rd ++ s₁.wr := by
  have hK := hp.wf
  exact ⟨EA.ctx hp e₁, by rw [EA.reg e₁ (by simp), hp.r4], sepAll_mono hp.sE (by simp [inB]) (by kdecide),
    by rw [e₁.rd, e₁.wr]; exact hp.wE⟩

omit hp in
theorem v_of {s₃ : State} (t₃ : ∀ k < K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀) k))
    (y₃ : ∀ j < K.k, PolyIs s₃.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀) j)) :
    ∀ k < 2 * K.k, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - K.k)) := fun k hk => by
  by_cases e : k < K.k
  · simp only [e, ↓reduceIte]; exact t₃ k e
  · simp only [e, ↓reduceIte]
    have := y₃ (k - K.k) (by omega)
    rwa [show K.k + (k - K.k) = k by omega] at this

theorem rows_init {s₅ : State} (e₅ : EA K L s₀ s₅) (d₅ : EData K L b s₀ s₅) :
    WP isa (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) s₅ (ERow K L b s₀ 0) :=
  WP.mono flagInit_ok fun _ ⟨k, g11, g9, m⟩ =>
    ⟨(e₅.monoL fun w hw => List.mem_append_left _ hw).trans ((k.weaken (by simp)).mono
      (fun _ h => absurd h List.not_mem_nil)), g9, by rw [g11]; rfl,
      d₅.keep hp.ctx.ok (W := []) (by rw [m]; exact Frame.refl _ _) rfl rfl,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem data5 {s₄ s₅ : State} (ρ₄ : bytesAt s₄.mem (L.A 0 oSeed) 32 = ρE K L b s₀)
    (v₄ : ∀ k < 2 * K.k, PolyIs s₄.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - K.k)))
    (E₄ : ∀ N, K.k ≤ N → N < 2 * K.k + 1 → PolyIs s₄.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀) N))
    (f₅ : Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) s₄.mem s₅.mem)
    (μ₅ : PolyIs s₅.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀))) : EData K L b s₀ s₅ := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  exact ⟨(Lay.bytes_keep hL f₅ (hp.ctx.sepAll0 (by decide) (by kdecide)) (by decide)).trans ρ₄,
    fun k hk => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs) ((mu_sep hK).1 k hk)) (v₄ k hk),
    fun N h3 h7 => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs) ((mu_sep hK).2 N h7)) (E₄ N h3 h7), μ₅⟩

theorem encrypt_ok : WP isa K.encrypt s₀ fun s => KeptX [.r9, .r10, .r11] (L.RL (encW K b)) s₀ s ∧
    s.gpr .r11 = (if okE K L b s₀ K.k then 1 else 0) ∧
    bytesAt s.mem (L.A b.iC b.oC) K.ctLen =
      VG.Proof.MlKem.KPke.ct K.p (aE K L b s₀) (ekB K L b s₀) (mB L b s₀) (rB L s₀) := by
  have hL := hp.ctx.ok
  have hK := hp.wf
  refine WP.seq (WP.mono (enc1_ok hp) fun s₁ ⟨e₁, _, ρ₁⟩ => ?_)
  obtain ⟨hc₁, g4, hsE, hr₁⟩ := dec_pre hp e₁
  refine WP.seq (WP.mono (decT_init (K := K) (L := L) (i := b.iE) (o := b.oE)) fun s₁' h₁' => ?_)
  refine WP.seq (WP.mono (decT_loop hK hc₁ g4 hsE hr₁ h₁') fun s₂ h₂ => ?_)
  obtain ⟨e₂, ρ₂, t₂⟩ := enc2_ok hp e₁ ρ₁ h₂
  refine WP.seq (WP.mono (enc3_ok hp e₂ ρ₂ t₂) fun s₃ ⟨e₃, ρ₃, t₃, y₃⟩ => ?_)
  refine WP.seq (WP.mono (enc4_ok hp e₃ ρ₃ (v_of t₃ y₃)) fun s₄ ⟨e₄, ρ₄, v₄, E₄⟩ => ?_)
  refine WP.seq (WP.mono (enc5a_ok hp e₄) fun s₄' ⟨h₄', a0, a1, a2, a3⟩ => ?_)
  refine WP.seq (WP.mono (enc5b_ok hp e₄ h₄' a0 a1 a2 a3) fun s₅ ⟨e₅, f₅, μ₅⟩ => ?_)
  have d₅ := data5 hp ρ₄ v₄ E₄ f₅ μ₅
  refine WP.seq (WP.mono (rows_init hp e₅ d₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (ERow K L b s₀) (N := K.k) hK.k1 (fun i hi s h => encRow_step hp hi h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (ev1_ok hp h₇.venv) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₈.1 h₈.2 (o := K.oNtt) (by kenc)) fun s₉ ⟨h₉, a0, a1⟩ => ?_)
  refine WP.seq (WP.mono (ev3_ok hp h₉ a0 a1) fun s₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₁₀.1 h₁₀.2 (o := oPoly (3 * K.k)) (by kenc)) fun s₁₁ ⟨h₁₁, b0, b1⟩ => ?_)
  have e₁₁ := h₁₁.1.d.e (2 * K.k) (by omega) (by omega)
  rw [show K.k + 2 * K.k = 3 * K.k by omega] at e₁₁
  refine WP.seq (WP.mono (evAdd_ok hp (.inl rfl) h₁₁ e₁₁ b0 b1) fun s₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₁₂.1 h₁₂.2 (o := oPoly (3 * K.k + 1)) (by kenc)) fun s₁₃ ⟨h₁₃, c0, c1⟩ => ?_)
  refine WP.seq (WP.mono (evAdd_ok hp (.inr rfl) h₁₃ h₁₃.1.d.mu c0 c1) fun s₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (ev8_ok hp h₁₄) fun s₁₅ ⟨h₁₅, d0, d1, d2, d3⟩ => ?_)
  exact ev9_ok hp h₁₅ d0 d1 d2 d3

end

/-! ## The matrix, for the contracts -/

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem enc_some {k : Nat} {ρ r : List Byte} (hk : okEnc k ρ k = true) :
    ∀ i < k, ∀ j < k, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = some (aEnc ρ r i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk j (List.mem_range.mpr hj)
  have h₂ := List.all_eq_true.mp h₁ i (List.mem_range.mpr hi)
  simp only [rowSeed, ↓reduceIte] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [aEnc, effA, rowSeed, ↓reduceIte, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem enc_none {k : Nat} {ρ : List Byte} (hk : okEnc k ρ k = false) :
    ∃ i < k, ∃ j < k, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = none := by
  rw [okEnc, List.all_eq_false] at hk
  obtain ⟨j, hj, h₁⟩ := hk
  rw [Bool.not_eq_true, okRow, List.all_eq_false] at h₁
  obtain ⟨i, hi, h₂⟩ := h₁
  simp only [rowSeed, ↓reduceIte] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

end Enc

end VG.Proof.MlKem.Arm
