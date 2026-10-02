import VerifiedGarbage.Proof.MlKem1024.Arm.RowSum
import VerifiedGarbage.Proof.MlKem1024.Arm.Calls
import VerifiedGarbage.Proof.MlKem.Arm.Encrypt

/-!
# ML-KEM-1024 on 32-bit ARM: K-PKE.Encrypt, correctness

`Proof/MlKem/Arm/Encrypt.lean` for ML-KEM-1024 (`k = 4`, `d_u = 11`, `d_v =
5`). `encrypt4` runs within encapsulation and decapsulation, on buffers the
callers choose (`EB`): the encapsulation key (in `r4`), the message (in `r5`)
and the ciphertext (in `r8`), each at an offset of one of the callers'
buffers; `r` is at 920 in `scratch`. It writes the ciphertext, and changes
nothing but the regions of `encW` (`encrypt_ok`). Its phases: `ρ` copied to
the seed of `SampleNTT`, `t̂` decoded (`decT_loop`), the `PRF`s into `ŷ`, `e₁`
and `e₂`, `μ`, the rows of `u` compressed into the ciphertext (`encRow_step`),
and `v`.
-/

namespace VG.Proof.MlKem1024.Arm

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm
open VG.Proof.MlKem.Arm.Enc (EB sepAll_left sepB_same)

/-! ## Decoding four polynomials -/

/-- The polynomials `0` to `3` decoded from the 1536 bytes at offset `o` of buffer `i` (in `r4`). -/
structure DecInv (L : Lay) (i o : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r9] (L.RL [(0, 2048, 4096)]) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  t : ∀ k < j, PolyIs s.mem (L.A 0 (oPoly k)) (decode12 (bytesAt s₀.mem (L.A i (o + 384 * k)) 384))

theorem decT_slots : ∀ k < 4, [((0 : Nat), oPoly k, (1024 : Nat))].all (fun w => [(0, 2048, 4096)].any (subB0 w)) = true ∧
    (∀ k' < 4, (k' == k || [((0 : Nat), oPoly k, (1024 : Nat))].all (sep0 (oPoly k') 1024)) = true) := by
  decide

theorem decT_step {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h4 : s₀.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : sepAll L.sizes (i, o, 1536) [(0, 2048, 4096)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr)
    {j : Nat} (hj : j < 4) {s : State} (h : DecInv L i o s₀ j s) :
    WP isa decTBody4 s fun s' => DecInv L i o s₀ (j + 1) s' ∧ s'.z = decide (j + 1 = 4) := by
  have hL := hc.ok
  have hc' := h.kx.ctx (by decide) hc
  obtain ⟨c_sub, c_sep⟩ := decT_slots j hj
  have g4 : s.gpr .r4 = L.ptr i + BitVec.ofNat 32 o := by rw [h.kx.cs .r4 (by decide) (by decide) (by decide), h4]
  refine WP.seq (WP.mono (decTArgs_ok hc'.r7 g4 h.r9) fun s₁ ⟨o₁, a0, a1⟩ => ?_)
  rw [at384_eq _ (by omega), ptr_add_add32] at a0
  rw [slot_eq _ (by offs4), show 2048 + 1024 * 0 + 1024 * j = 2048 + 1024 * j by omega] at a1
  have hc₁ := hc'.only o₁
  have hsj : sepAll L.sizes (i, o + 384 * j, 384) [(0, 2048, 4096)] = true := sepAll_mono hs (inB_off (by omega)) rfl
  have hsep : sepB L.sizes (i, o + 384 * j, 384) (0, oPoly j, 1024) = true :=
    sepB_mono (List.all_eq_true.mp hsj _ (List.mem_singleton_self _)) (inB_refl _) (by
      simp only [inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)
  refine WP.seq (decode12L hL a0 a1 hsep (by rw [o₁.rd, o₁.wr, h.kx.rd, h.kx.wr]; exact hr) hc₁.buf0
    fun s₂ k₂ p₂ => ?_)
  have g9 : s₂.gpr .r9 = BitVec.ofNat 32 j := by
    rw [k₂.cs .r9 (by decide) (by decide), o₁.cs .r9 (by decide) (by decide), h.r9]
  refine WP.mono (count_ok (by omega) (by decide) (by decide) g9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_⟩, z'⟩
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
    · have := c_sep k (by omega)
      simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at this
      exact Lay.polyIs_keep hL K.frame (hc.sepAll0 (by offs4) this) (h.t k (by omega))

theorem decT_init {L : Lay} {i o : Nat} {s₀ : State} :
    WP isa (.block [.mov .r9 (.imm 0)]) s₀ (DecInv L i o s₀ 0) :=
  WP.mono (movc_ok .r9 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem decT_loop {L : Lay} {i o : Nat} {s₀ : State} (hc : Ctx L s₀) (h4 : s₀.gpr .r4 = L.ptr i + BitVec.ofNat 32 o)
    (hs : sepAll L.sizes (i, o, 1536) [(0, 2048, 4096)] = true) (hr : L.buf i ∈ s₀.rd ++ s₀.wr) {s : State}
    (h : DecInv L i o s₀ 0 s) : WP isa (.loop decTBody4 .ne) s (DecInv L i o s₀ 4) :=
  wp_loop_ne (DecInv L i o s₀) (N := 4) (by decide) (fun _ hj _ h => decT_step hc h4 hs hr hj h) (fun _ h => h) h

namespace Enc

/-! ## The buffers of K-PKE.Encrypt -/

/-- What `encrypt` changes in `scratch` and the stack. -/
abbrev encW0 : List (Nat × Nat × Nat) :=
  [(0, 0, 840), (0, 952, 1), (0, 1024, 128), (0, 1216, 34), (0, 2048, 17408), (0, 19456, 3072), (1, 0, 8)]

/-- What `encrypt` changes. -/
abbrev encW (b : EB) : List (Nat × Nat × Nat) := encW0 ++ [(b.iC, b.oC, 1568)]

/-- A state `encrypt` runs from. -/
structure EncPre (L : Lay) (b : EB) (s : State) : Prop where
  ctx : Ctx L s
  r4 : s.gpr .r4 = L.ptr b.iE + BitVec.ofNat 32 b.oE
  r5 : s.gpr .r5 = L.ptr b.iM + BitVec.ofNat 32 b.oM
  r8 : s.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC
  sE : sepAll L.sizes (b.iE, b.oE, 1568) encW0 = true
  sM : sepAll L.sizes (b.iM, b.oM, 32) encW0 = true
  sC : sepAll L.sizes (b.iC, b.oC, 1568) encW0 = true
  wE : L.buf b.iE ∈ s.rd ++ s.wr
  wM : L.buf b.iM ∈ s.rd ++ s.wr
  wC : L.buf b.iC ∈ s.wr

/-- The entries of `Â` the products use, from `ρ` and `r`: `Â[i, j]`, or
`ŷ[i]` if its `SampleNTT` does not finish. -/
def aEnc (ρ r : List Byte) (i j : Nat) : Poly := effA true ρ j i (VG.Proof.MlKem.encY r i)

/-- Whether the `SampleNTT`s of the first `i` rows of `Â^⊺` finished. -/
def okEnc (ρ : List Byte) (i : Nat) : Bool := (List.range i).all fun i' => okRow true ρ i' 4

section
variable (L : Lay) (b : EB) (s₀ : State)

/-- `ek`. -/
abbrev ekB : List Byte := bytesAt s₀.mem (L.A b.iE b.oE) 1568
/-- `m`. -/
abbrev mB : List Byte := bytesAt s₀.mem (L.A b.iM b.oM) 32
/-- `r`. -/
abbrev rB : List Byte := bytesAt s₀.mem (L.A 0 oSigma) 32

/-- `ρ`. -/
abbrev ρE : List Byte := ekRho mlKem1024 (ekB L b s₀)
/-- The entries of `Â` the products use. -/
abbrev aE : Nat → Nat → Poly := aEnc (ρE L b s₀) (rB L s₀)
/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
abbrev okE (i : Nat) : Bool := okEnc (ρE L b s₀) i

end

theorem okE_succ (L : Lay) (b : EB) (s₀ : State) (i : Nat) :
    okE L b s₀ (i + 1) = (okE L b s₀ i && okRow true (ρE L b s₀) i 4) := by
  simp only [okE, okEnc, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- Before the rows: what changes is within `encW0`. -/
abbrev EA (L : Lay) (s₀ s : State) : Prop := KeptX [.r9, .r10, .r11] (L.RL encW0) s₀ s

section
variable {L : Lay} {b : EB} {s₀ : State} (hp : EncPre L b s₀)
include hp

theorem EA.ctx {s : State} (h : EA L s₀ s) : Ctx L s := KeptX.ctx h (by decide) hp.ctx

/-- The bytes of a part of a buffer apart from `encW0`. -/
theorem EA.bytes {s : State} (h : EA L s₀ s) {i o l : Nat} (hs : sepAll L.sizes (i, o, l) encW0 = true) :
    bytesAt s.mem (L.A i o) l = bytesAt s₀.mem (L.A i o) l := by
  have := sepAll_bounds hs
  have := hp.ctx.ok.fit i this.1
  exact Lay.bytes_keep hp.ctx.ok h.frame hs (by simp only [Lay.size] at this; omega)

theorem EA.ek {s : State} (h : EA L s₀ s) {k n : Nat} (hk : k + n ≤ 1568) :
    bytesAt s.mem (L.A b.iE (b.oE + k)) n = bytesAt s₀.mem (L.A b.iE (b.oE + k)) n :=
  EA.bytes hp h (sepAll_mono hp.sE (inB_off hk) (by decide))

omit hp in
theorem EA.reg {s : State} (h : EA L s₀ s) {r : Reg} (hr : r ∈ [Reg.r4, .r5, .r7, .r8]) : s.gpr r = s₀.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact h.cs _ (by decide) (by decide) (by decide)

/-! ## `ρ` -/

theorem enc1_ok : WP isa (copy .r4 1536 .r7 oSeed 32) s₀ fun s =>
    EA L s₀ s ∧ Frame (L.RL [(0, oSeed, 32)]) s₀.mem s.mem ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE L b s₀ := by
  have hL := hp.ctx.ok
  have hs : sepB L.sizes (b.iE, b.oE + 1536, 32) (0, oSeed, 32) = true :=
    sepB_mono (List.all_eq_true.mp hp.sE (0, 1216, 34) (by decide)) (inB_off (by omega)) (by decide)
  refine WP.mono (copyLo hL (bo := b.oE) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ hp.r4 hp.ctx.r7 (by decide)
    (by decide) (by decide) (by decide) (by decide) hs hp.wE hp.ctx.buf0) fun s ⟨k, e⟩ =>
    ⟨(k.x _).subL hp.ctx (by decide), k.frame, e.trans ?_⟩
  show _ = ((bytesAt s₀.mem (L.A b.iE b.oE) 1568).drop 1536).take 32
  rw [bytesAt_slice _ _ (by decide), add_ofNat_add]

/-! ## `t̂` -/

theorem enc2_ok {s₁ : State} (h₁ : EA L s₀ s₁) (hρ : bytesAt s₁.mem (L.A 0 oSeed) 32 = ρE L b s₀) {s : State}
    (h : DecInv L b.iE b.oE s₁ 4 s) :
    EA L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE L b s₀ ∧
      ∀ k < 4, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB L b s₀) k) := by
  refine ⟨h₁.trans ((h.kx.weaken (by simp)).subL hp.ctx (by decide)),
    (Lay.bytes_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by decide) (by decide)) (by decide)).trans hρ,
    fun k hk => ?_⟩
  have := h.t k hk
  rw [EA.ek hp h₁ (by omega)] at this
  show PolyIs _ _ (decode12 (((bytesAt s₀.mem (L.A b.iE b.oE) 1568).drop (384 * k)).take 384))
  rw [bytesAt_slice _ _ (by omega), add_ofNat_add]; exact this

/-! ## The `PRF`s -/

omit hp in
theorem prf_ek : (prfLW 0 4).all (fun w => encW0.any (subB0 w)) = true ∧
    (prfLW 4 9).all (fun w => encW0.any (subB0 w)) = true ∧
    (prfLW 0 4).all (sep0 oSeed 32) = true ∧ (prfLW 4 9).all (sep0 oSeed 32) = true ∧
    (∀ k < 4, (prfLW 0 4).all (sep0 (oPoly k) 1024) = true) ∧
    (∀ k < 8, (prfLW 4 9).all (sep0 (oPoly k) 1024) = true) ∧ encW0.all (sep0 oSigma 32) = true := by
  decide

theorem enc3_ok {s₂ : State} (h₂ : EA L s₀ s₂) (hρ : bytesAt s₂.mem (L.A 0 oSeed) 32 = ρE L b s₀)
    (ht : ∀ k < 4, PolyIs s₂.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB L b s₀) k)) :
    WP isa (prfLoop4 true 0 4) s₂ fun s => EA L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE L b s₀ ∧
      (∀ k < 4, PolyIs s.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB L b s₀) k)) ∧
      ∀ j < 4, PolyIs s.mem (L.A 0 (oPoly (4 + j))) (VG.Proof.MlKem.encY (rB L s₀) j) := by
  have hc := EA.ctx hp h₂
  obtain ⟨c1, -, c3, -, c5, -, c7⟩ := prf_ek
  refine WP.mono (prfLoop_ok hc true (N₀ := 0) (N₁ := 4) (by decide) (by decide)
    (EA.bytes hp h₂ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, fun j hj => ?_⟩
  · exact h₂.trans ((k.weaken (by simp)).subL hp.ctx c1)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c3) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs4) (c5 k' hk')) (ht k' hk')
  · exact p j (Nat.zero_le _) hj

theorem enc4_ok {s₃ : State} (h₃ : EA L s₀ s₃) (hρ : bytesAt s₃.mem (L.A 0 oSeed) 32 = ρE L b s₀)
    (hv : ∀ k < 8, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < 4 then VG.Proof.MlKem.ekT (ekB L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - 4))) :
    WP isa (prfLoop4 false 4 9) s₃ fun s => EA L s₀ s ∧ bytesAt s.mem (L.A 0 oSeed) 32 = ρE L b s₀ ∧
      (∀ k < 8, PolyIs s.mem (L.A 0 (oPoly k)) (if k < 4 then VG.Proof.MlKem.ekT (ekB L b s₀) k
        else VG.Proof.MlKem.encY (rB L s₀) (k - 4))) ∧
      ∀ N, 4 ≤ N → N < 9 → PolyIs s.mem (L.A 0 (oPoly (4 + N))) (VG.Proof.MlKem.cbd (rB L s₀) N) := by
  have hc := EA.ctx hp h₃
  obtain ⟨-, c2, -, c4, -, c6, c7⟩ := prf_ek
  refine WP.mono (prfLoop_ok hc false (N₀ := 4) (N₁ := 9) (by decide) (by decide)
    (EA.bytes hp h₃ (hp.ctx.sepAll0 (by decide) c7))) fun s ⟨k, p⟩ => ⟨?_, ?_, fun k' hk' => ?_, p⟩
  · exact h₃.trans ((k.weaken (by simp)).subL hp.ctx c2)
  · rw [← hρ]; exact Lay.bytes_keep hp.ctx.ok k.frame (hc.sepAll0 (by decide) c4) (by decide)
  · exact Lay.polyIs_keep hp.ctx.ok k.frame (hc.sepAll0 (by offs4) (c6 k' hk')) (hv k' hk')

/-! ## `μ` -/

omit hp in
theorem muArgs_ok {s : State} {P M : BitVec 32} (h7 : s.gpr .r7 = P) (h5 : s.gpr .r5 = M) :
    WP isa (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly 13)]) s
      fun s' => Only s s' ∧ s'.gpr .r0 = M ∧ s'.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧
        s'.gpr .r2 = BitVec.ofNat 32 1 ∧ s'.gpr .r3 = P + BitVec.ofNat 32 (oPoly 13) := by
  have e1 : encodable (32 : BitVec 32) = true := by decide
  have e2 : encodable (1 : BitVec 32) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 (oPoly 13)) = true := by decide
  run_block [ptrTo, e1, e2, e3, h7, h5]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem enc5a_ok {s₄ : State} (h₄ : EA L s₀ s₄) :
    WP isa (.block [.mov .r0 (.reg .r5), .mov .r1 (.imm 32), .mov .r2 (.imm 1), ptrTo .r3 .r7 (oPoly 13)]) s₄
      fun s => (EA L s₀ s ∧ s.mem = s₄.mem) ∧ s.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM ∧
        s.gpr .r1 = BitVec.ofNat 32 (32 * 1) ∧ s.gpr .r2 = BitVec.ofNat 32 1 ∧
        s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly 13) := by
  have hc := EA.ctx hp h₄
  have g5 : s₄.gpr .r5 = L.ptr b.iM + BitVec.ofNat 32 b.oM := by rw [EA.reg h₄ (by simp), hp.r5]
  exact WP.mono (muArgs_ok hc.r7 g5) fun s₁ ⟨o₁, a0, a1, a2, a3⟩ =>
    ⟨⟨h₄.trans (o₁.x _ _), o₁.mem⟩, a0, a1, a2, a3⟩

theorem enc5b_ok {s₄ s : State} (h₄ : EA L s₀ s₄) (h : EA L s₀ s ∧ s.mem = s₄.mem)
    (a0 : s.gpr .r0 = L.ptr b.iM + BitVec.ofNat 32 b.oM) (a1 : s.gpr .r1 = BitVec.ofNat 32 (32 * 1))
    (a2 : s.gpr .r2 = BitVec.ofNat 32 1) (a3 : s.gpr .r3 = L.ptr 0 + BitVec.ofNat 32 (oPoly 13)) :
    WP isa callDecompress s fun s' => EA L s₀ s' ∧ Frame (L.RL [(0, oPoly 13, 1024)]) s₄.mem s'.mem ∧
      PolyIs s'.mem (L.A 0 (oPoly 13)) (decodeDecompress 1 (mB L b s₀)) := by
  have hc := EA.ctx hp h.1
  have hs : sepB L.sizes (b.iM, b.oM, 32 * 1) (0, oPoly 13, 1024) = true :=
    sepB_mono (List.all_eq_true.mp hp.sM (0, 2048, 17408) (by decide)) (inB_refl _) (by decide)
  refine decompressL hp.ctx.ok a0 a1 a2 a3 (by decide) hs (by rw [h.1.rd, h.1.wr]; exact hp.wM)
    hc.buf0 fun s' k p => ⟨?_, ?_, ?_⟩
  · exact h.1.trans ((k.x _).subL hp.ctx (by decide))
  · rw [← h.2]; exact k.frame
  · rw [h.2, show 32 * 1 = 32 from rfl, EA.bytes hp h₄ hp.sM] at p; exact p

end

/-! ## What the rows and `v` use -/

/-- The polynomials the rows and `v` use: `ρ`, `t̂`, `ŷ`, `e₁`, `e₂` and `μ`. -/
structure EData (L : Lay) (b : EB) (s₀ s : State) : Prop where
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = ρE L b s₀
  v : ∀ k < 8, PolyIs s.mem (L.A 0 (oPoly k)) (if k < 4 then VG.Proof.MlKem.ekT (ekB L b s₀) k
    else VG.Proof.MlKem.encY (rB L s₀) (k - 4))
  e : ∀ N, 4 ≤ N → N < 9 → PolyIs s.mem (L.A 0 (oPoly (4 + N))) (VG.Proof.MlKem.cbd (rB L s₀) N)
  mu : PolyIs s.mem (L.A 0 (oPoly 13)) (decodeDecompress 1 (mB L b s₀))

theorem EData.keep {L : Lay} {b : EB} {s₀ s s' : State} (hL : L.Ok) (h : EData L b s₀ s) {W : List (Nat × Nat × Nat)}
    (hf : Frame (L.RL W) s.mem s'.mem) (h1 : sepAll L.sizes (0, 1216, 32) W = true)
    (h2 : sepAll L.sizes (0, 2048, 14336) W = true) : EData L b s₀ s' := by
  have hp : ∀ k < 14, sepAll L.sizes (0, oPoly k, 1024) W = true := fun k hk =>
    sepAll_left h2 (by simp only [inB, oPoly, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega)
  exact ⟨(Lay.bytes_keep hL hf h1 (by decide)).trans h.rho, fun k hk => Lay.polyIs_keep hL hf (hp k (by omega)) (h.v k hk),
    fun N h3 h7 => Lay.polyIs_keep hL hf (hp (4 + N) (by omega)) (h.e N h3 h7), Lay.polyIs_keep hL hf (hp 13 (by omega)) h.mu⟩

/-- After the rows `i' < i`. -/
structure ERow (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) : Prop where
  K : KeptX [.r9, .r10, .r11] (L.RL (encW b)) s₀ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 i
  r11 : s.gpr .r11 = if okE L b s₀ i then 1 else 0
  d : EData L b s₀ s
  c : ∀ i' < i, bytesAt s.mem (L.A b.iC (b.oC + 352 * i')) 352 =
    compressEncode 11 (VG.Proof.MlKem.encU1024 (aE L b s₀) (rB L s₀) i')

/-- In row `i` (from `s`), with the sum `f`. -/
structure RB (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) (f : Poly) (s' : State) : Prop where
  K : KeptX [.r9, .r10, .r11] (L.RL rowW) s s'
  r9 : s'.gpr .r9 = BitVec.ofNat 32 i
  r11 : s'.gpr .r11 = if okE L b s₀ (i + 1) then 1 else 0
  acc : PolyIs s'.mem (L.A 0 oAcc4) f

/-- In row `i`, after its encoding. -/
structure RC (L : Lay) (b : EB) (s₀ : State) (i : Nat) (s : State) (s' : State) : Prop where
  K : KeptX [.r9, .r10, .r11] (L.RL (rowW ++ [(b.iC, b.oC + 352 * i, 352)])) s s'
  r9 : s'.gpr .r9 = BitVec.ofNat 32 i
  r11 : s'.gpr .r11 = if okE L b s₀ (i + 1) then 1 else 0
  cb : bytesAt s'.mem (L.A b.iC (b.oC + 352 * i)) 352 =
    compressEncode 11 (VG.Proof.MlKem.encU1024 (aE L b s₀) (rB L s₀) i)

theorem row_facts : rowW.all (fun w => encW0.any (subB0 w)) = true ∧ rowW.all (fun w => encW0.any (inB w)) = true ∧
    rowW.all (sep0 1216 32) = true ∧ rowW.all (sep0 2048 14336) = true ∧
    [((0 : Nat), oAcc4, (1024 : Nat)), (0, oNtt4, 1024)].all (fun w => rowW.any (subB0 w)) = true ∧
    [((0 : Nat), oAcc4, (1024 : Nat))].all (fun w => rowW.any (subB0 w)) = true ∧
    (∀ i < 4, rowW.all (sep0 (oPoly (4 + (4 + i))) 1024) = true) := by
  decide

section
variable {L : Lay} {b : EB} {s₀ : State} (hp : EncPre L b s₀)
include hp

/-- The part `[k, k + n)` of `c` apart from regions inside `encW0`. -/
theorem cSep {k n : Nat} (hk : k + n ≤ 1568) {W : List (Nat × Nat × Nat)}
    (hW : W.all (fun w => encW0.any (inB w)) = true) : sepAll L.sizes (b.iC, b.oC + k, n) W = true :=
  sepAll_mono hp.sC (inB_off hk) hW

theorem cData {k n : Nat} (hk : k + n ≤ 1568) :
    sepAll L.sizes (0, 1216, 32) [(b.iC, b.oC + k, n)] = true ∧
      sepAll L.sizes (0, 2048, 14336) [(b.iC, b.oC + k, n)] = true := by
  have c1 := cSep hp hk (W := [(0, 1216, 32)]) (by decide)
  have c2 := cSep hp hk (W := [(0, 2048, 14336)]) (by decide)
  simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at c1 c2 ⊢
  exact ⟨sepB_symm c1, sepB_symm c2⟩

theorem cBound : b.iC < L.sizes.length ∧ b.oC + 1568 ≤ L.size b.iC := sepAll_bounds hp.sC

theorem ERow.rowPre {i : Nat} (hi : i < 4) {s : State} (h : ERow L b s₀ i s) :
    RowPre L (ρE L b s₀) (VG.Proof.MlKem.encY (rB L s₀)) i (okE L b s₀ i) s :=
  ⟨h.K.ctx (by decide) hp.ctx, hi, h.r9, h.r11, h.d.rho, fun j hj => by
    have := h.d.v (4 + j) (by omega)
    have e : ¬ (4 + j < 4) := by omega
    simp only [e, ↓reduceIte, show 4 + j - 4 = j by omega] at this
    exact this⟩

section
variable {i : Nat} (hi : i < 4) {s : State} (h : ERow L b s₀ i s)
include hi h

omit hi in
theorem RB.ctx {f : Poly} {s' : State} (r : RB L b s₀ i s f s') : Ctx L s' :=
  r.K.ctx (by decide) (h.K.ctx (by decide) hp.ctx)

omit hi in
theorem er2_ok {s₁ : State}
    (r : RowInv L true (ρE L b s₀) (VG.Proof.MlKem.encY (rB L s₀)) i (okE L b s₀ i) s 4 s₁) :
    WP isa (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 oNtt4]) s₁ fun s₂ =>
      RB L b s₀ i s (VG.Proof.MlKem.dot4 (fun j => aE L b s₀ j i) (VG.Proof.MlKem.encY (rB L s₀))) s₂ ∧
      s₂.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ s₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4 := by
  have hc₁ := r.kx.ctx (by decide) (h.K.ctx (by decide) hp.ctx)
  refine WP.mono (accArgs_ok hc₁.r7 (by decide) (by decide)) fun s₂ ⟨o₂, a0, a1⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, a0, a1⟩
  · exact (r.kx.weaken (by simp)).trans (o₂.x _ _)
  · rw [o₂.cs .r9 (by decide) (by decide), r.kx.cs .r9 (by decide) (by decide) (by decide), h.r9]
  · rw [o₂.cs .r11 (by decide) (by decide), r.r11, okE_succ]
  · rw [o₂.mem, ← rowAcc_four]; exact r.acc

omit hi in
theorem er3_ok {f : Poly} {s₂ : State} (r : RB L b s₀ i s f s₂) (g0 : s₂.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4)
    (g1 : s₂.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4) : WP isa callNttInv s₂ (RB L b s₀ i s (nttInv f)) := by
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, c5, -, -⟩ := row_facts
  exact nttInvL hp.ctx.ok g0 g1 (hc.sep00 (by decide) (by decide) (by decide)) hc.buf0 hc.buf0 r.acc
    fun s₃ k₃ p₃ => ⟨r.K.trans ((k₃.x _).subL hp.ctx c5), by rw [k₃.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₃.cs .r11 (by decide) (by decide), r.r11], p₃⟩

theorem er4_ok {f : Poly} {s₃ : State} (r : RB L b s₀ i s f s₃) :
    WP isa (.block (ptrTo .r0 .r7 oAcc4 :: slotAt .r1 .r9 (oPoly 8))) s₃ fun s₄ => RB L b s₀ i s f s₄ ∧
      s₄.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ s₄.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + (4 + i))) := by
  have hc := r.ctx hp h
  refine WP.mono (ptrSlot_ok (i := i) hc.r7 r.r9 (by decide) (by decide)) fun s₄ ⟨o₄, a0, a1⟩ => ?_
  rw [slot_eq _ (by offs4), show oPoly 8 + 1024 * i = oPoly (4 + (4 + i)) by offs4] at a1
  exact ⟨⟨r.K.trans (o₄.x _ _), by rw [o₄.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₄.cs .r11 (by decide) (by decide), r.r11], by rw [o₄.mem]; exact r.acc⟩, a0, a1⟩

theorem er5_ok {f : Poly} {s₄ : State} (r : RB L b s₀ i s f s₄) (g0 : s₄.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4)
    (g1 : s₄.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly (4 + (4 + i)))) :
    WP isa callAdd s₄ (RB L b s₀ i s (add f (VG.Proof.MlKem.cbd (rB L s₀) (4 + i)))) := by
  have hc := r.ctx hp h
  obtain ⟨-, -, -, -, -, c6, c7⟩ := row_facts
  have he : PolyIs s₄.mem (L.A 0 (oPoly (4 + (4 + i)))) (VG.Proof.MlKem.cbd (rB L s₀) (4 + i)) :=
    Lay.polyIs_keep hp.ctx.ok r.K.frame (hc.sepAll0 (by offs4) (c7 i hi)) (h.d.e (4 + i) (by omega) (by omega))
  exact addL hp.ctx.ok g0 g1 (hc.sep00 (by offs4) (by offs4) (by offs4)) hc.buf0 (mem_rd_wr hc.buf0) r.acc he
    fun s₅ k₅ p₅ => ⟨r.K.trans ((k₅.x _).subL hp.ctx c6), by rw [k₅.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₅.cs .r11 (by decide) (by decide), r.r11], p₅⟩

omit hp hi h in
theorem cArgs_ok {s : State} {P C : BitVec 32} {i : Nat} (h7 : s.gpr .r7 = P) (h8 : s.gpr .r8 = C)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 i) :
    WP isa (.block (([ptrTo .r0 .r7 oAcc4, .mov .r1 (.imm 11)] : List Instr) ++ at352 .r2 .r8 .r9 ++
      ([.mov .r3 (.imm 352)] : List Instr))) s
      fun s' => Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 oAcc4 ∧ s'.gpr .r1 = BitVec.ofNat 32 11 ∧
        s'.gpr .r2 = C + BitVec.ofNat 32 i <<< 8 + BitVec.ofNat 32 i <<< 6 + BitVec.ofNat 32 i <<< 5 ∧
        s'.gpr .r3 = BitVec.ofNat 32 (32 * 11) := by
  have e1 : encodable (BitVec.ofNat 32 oAcc4) = true := by decide
  have e2 : encodable (11 : BitVec 32) = true := by decide
  have e3 : encodable (352 : BitVec 32) = true := by decide
  run_block [at352, ptrTo, e1, e2, e3, h7, h8, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem er6_ok {f : Poly} {s₅ : State} (r : RB L b s₀ i s f s₅) :
    WP isa (.block (([ptrTo .r0 .r7 oAcc4, .mov .r1 (.imm 11)] : List Instr) ++ at352 .r2 .r8 .r9 ++
      ([.mov .r3 (.imm 352)] : List Instr))) s₅
      fun s₆ => RB L b s₀ i s f s₆ ∧ s₆.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧
        s₆.gpr .r1 = BitVec.ofNat 32 11 ∧ s₆.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 352 * i) ∧
        s₆.gpr .r3 = BitVec.ofNat 32 (32 * 11) := by
  have hc := r.ctx hp h
  have g8 : s₅.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC := by
    rw [r.K.cs .r8 (by decide) (by decide) (by decide), h.K.cs .r8 (by decide) (by decide) (by decide), hp.r8]
  refine WP.mono (cArgs_ok hc.r7 g8 r.r9) fun s₆ ⟨o₆, a0, a1, a2, a3⟩ => ?_
  rw [at352_eq _ (by omega), ptr_add_add32] at a2
  exact ⟨⟨r.K.trans (o₆.x _ _), by rw [o₆.cs .r9 (by decide) (by decide), r.r9],
    by rw [o₆.cs .r11 (by decide) (by decide), r.r11], by rw [o₆.mem]; exact r.acc⟩, a0, a1, a2, a3⟩

theorem er7_ok {s₆ : State} (r : RB L b s₀ i s (VG.Proof.MlKem.encU1024 (aE L b s₀) (rB L s₀) i) s₆)
    (g0 : s₆.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4) (g1 : s₆.gpr .r1 = BitVec.ofNat 32 11)
    (g2 : s₆.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 352 * i)) (g3 : s₆.gpr .r3 = BitVec.ofNat 32 (32 * 11)) :
    WP isa callCompress4 s₆ (RC L b s₀ i s) := by
  have hc := r.ctx hp h
  have hs : sepB L.sizes (0, oAcc4, 1024) (b.iC, b.oC + 352 * i, 32 * 11) = true := by
    have := cSep hp (k := 352 * i) (n := 352) (by omega) (W := [(0, oAcc4, 1024)]) (by decide)
    simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact sepB_symm this
  exact compressL4 hp.ctx.ok g0 g1 g2 g3 (by decide) hs (mem_rd_wr hc.buf0)
    (by rw [r.K.wr, h.K.wr]; exact hp.wC) r.acc fun s₇ k₇ p₇ =>
    ⟨(r.K.monoL (by simp)).trans ((k₇.x _).monoL (by simp)), by rw [k₇.cs .r9 (by decide) (by decide), r.r9],
      by rw [k₇.cs .r11 (by decide) (by decide), r.r11], p₇⟩

theorem er8_ok {s₇ : State} (r : RC L b s₀ i s s₇) :
    WP isa (.block (count .r9 4)) s₇ fun s' => ERow L b s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 4) := by
  have hL := hp.ctx.ok
  obtain ⟨r1, r2, r3, r4, -, -, -⟩ := row_facts
  obtain ⟨cb1, cb2⟩ := cBound hp
  refine WP.mono (count_ok (by omega) (by decide) (by decide) r.r9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', ?_, ?_, ?_⟩, z'⟩
  all_goals have K : KeptX [.r9, .r10, .r11] (L.RL (rowW ++ [(b.iC, b.oC + 352 * i, 352)])) s s' :=
    r.K.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · refine h.K.trans ?_
    have e : ∀ w ∈ L.RL (rowW ++ [(b.iC, b.oC + 352 * i, 352)]), ∃ w' ∈ L.RL (encW b), Region.Sub w w' := by
      intro w hw
      simp only [Lay.RL, List.map_append, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨w', hw', hs⟩ := hp.ctx.subL r1 w hw
        exact ⟨w', by simp only [Lay.RL, List.map_append, List.mem_append]; exact .inl hw', hs⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hw; subst hw
        exact ⟨L.R b.iC b.oC 1568, by simp, Lay.R_sub_R hL cb1 (by omega) (by omega) cb2⟩
    exact K.sub e
  · rw [k'.cs .r11 (by decide) (by decide) (by decide), r.r11]
  · obtain ⟨d1, d2⟩ := cData hp (k := 352 * i) (n := 352) (by omega)
    exact h.d.keep hL K.frame (sepAll_append (hp.ctx.sepAll0 (by decide) r3) d1)
      (sepAll_append (hp.ctx.sepAll0 (by decide) r4) d2)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.cb
    · have s1 : sepAll L.sizes (b.iC, b.oC + 352 * i', 352) rowW = true := cSep hp (by omega) r2
      have s2 : sepAll L.sizes (b.iC, b.oC + 352 * i', 352) [(b.iC, b.oC + 352 * i, 352)] = true := by
        simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true]
        exact sepB_same cb1 (by simp only [Lay.size] at cb2; omega) (by simp only [Lay.size] at cb2; omega)
          (by omega)
      rw [← h.c i' (by omega)]
      exact Lay.bytes_keep hL K.frame (sepAll_append s1 s2) (by decide)

end

theorem encRow_step {i : Nat} (hi : i < 4) {s : State} (h : ERow L b s₀ i s) :
    WP isa encRowBody4 s fun s' => ERow L b s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 4) :=
  WP.seq (WP.mono (rowSum_ok (transpose := true) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (er2_ok hp h r₁) fun _ ⟨r₂, a0, a1⟩ =>
    WP.seq (WP.mono (er3_ok hp h r₂ a0 a1) fun _ r₃ =>
    WP.seq (WP.mono (er4_ok hp hi h r₃) fun _ ⟨r₄, b0, b1⟩ =>
    WP.seq (WP.mono (er5_ok hp hi h r₄ b0 b1) fun _ r₅ =>
    WP.seq (WP.mono (er6_ok hp hi h r₅) fun _ ⟨r₆, c0, c1, c2, c3⟩ =>
    WP.seq (WP.mono (er7_ok hp hi h r₆ c0 c1 c2 c3) fun _ r₇ => er8_ok hp hi h r₇)))))))

end

/-! ## `v` -/

/-- What the steps of `v` keep: what the rows left. -/
structure VEnv (L : Lay) (b : EB) (s₀ s : State) : Prop where
  K : KeptX [.r9, .r10, .r11] (L.RL (encW b)) s₀ s
  r11 : s.gpr .r11 = if okE L b s₀ 4 then 1 else 0
  d : EData L b s₀ s
  c : ∀ i' < 4, bytesAt s.mem (L.A b.iC (b.oC + 352 * i')) 352 =
    compressEncode 11 (VG.Proof.MlKem.encU1024 (aE L b s₀) (rB L s₀) i')

/-- A region of `scratch` the steps of `v` may change. -/
def vOK (w : Nat × Nat × Nat) : Bool :=
  encW0.any (subB0 w) && encW0.any (inB w) && sep0 1216 32 w && sep0 2048 14336 w

theorem vOK_facts : dotW.all vOK = true ∧ [((0 : Nat), oAcc4, (1024 : Nat)), (0, oNtt4, 1024)].all vOK = true ∧
    [((0 : Nat), oAcc4, (1024 : Nat))].all vOK = true := by
  decide

section
variable {L : Lay} {b : EB} {s₀ : State} (hp : EncPre L b s₀)
include hp

theorem VEnv.keep {s s' : State} (h : VEnv L b s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (k : KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.r9, .r10]) (hW : W.all vOK = true) : VEnv L b s₀ s' := by
  have hL := hp.ctx.ok
  have hc := h.K.ctx (by decide) hp.ctx
  have w1 : W.all (fun w => encW0.any (subB0 w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.1.1
  have w2 : W.all (fun w => encW0.any (inB w)) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.1.2
  have w3 : W.all (sep0 1216 32) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.1.2
  have w4 : W.all (sep0 2048 14336) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [vOK, Bool.and_eq_true] at this; exact this.2
  refine ⟨h.K.trans ?_, ?_, h.d.keep hL k.frame (hc.sepAll0 (by decide) w3) (hc.sepAll0 (by decide) w4),
    fun i' hi' => (Lay.bytes_keep hL k.frame (cSep hp (by omega) w2) (by decide)).trans (h.c i' hi')⟩
  · refine ((k.weaken fun x hx' => ?_).subL hp.ctx w1).monoL fun w hw => List.mem_append_left _ hw
    have := hx x hx'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl <;> simp
  · rw [k.cs .r11 (by decide) (by decide) (fun hm => by have := hx _ hm; simp at this), h.r11]

omit hp in
theorem ERow.venv {s : State} (h : ERow L b s₀ 4 s) : VEnv L b s₀ s := ⟨h.K, h.r11, h.d, h.c⟩

theorem ev1_ok {s : State} (h : VEnv L b s₀ s) :
    WP isa dotP4 s fun s' => VEnv L b s₀ s' ∧ PolyIs s'.mem (L.A 0 oAcc4)
      (VG.Proof.MlKem.dot4 (VG.Proof.MlKem.ekT (ekB L b s₀)) (VG.Proof.MlKem.encY (rB L s₀))) := by
  have hc := h.K.ctx (by decide) hp.ctx
  refine WP.mono (dot_ok hc (fun j hj => ?_) (fun j hj => ?_)) fun s' ⟨k, p⟩ =>
    ⟨h.keep hp k (by simp) vOK_facts.1, p⟩
  · have := h.d.v j (by omega); simp only [hj, ↓reduceIte] at this; exact this
  · have := h.d.v (4 + j) (by omega)
    have e : ¬ (4 + j < 4) := by omega
    simp only [e, ↓reduceIte, show 4 + j - 4 = j by omega] at this
    exact this

theorem evArgs_ok {s : State} {f : Poly} (h : VEnv L b s₀ s) (hf : PolyIs s.mem (L.A 0 oAcc4) f) {o : Nat}
    (he : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block [ptrTo .r0 .r7 oAcc4, ptrTo .r1 .r7 o]) s fun s' => (VEnv L b s₀ s' ∧ PolyIs s'.mem (L.A 0 oAcc4) f) ∧
      s'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧ s'.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 o := by
  have hc := h.K.ctx (by decide) hp.ctx
  exact WP.mono (accArgs_ok hc.r7 (by decide) he) fun s' ⟨o', a0, a1⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl, by rw [o'.mem]; exact hf⟩, a0, a1⟩

theorem ev3_ok {s : State} {f : Poly} (h : VEnv L b s₀ s ∧ PolyIs s.mem (L.A 0 oAcc4) f)
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4) (g1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 oNtt4) :
    WP isa callNttInv s fun s' => VEnv L b s₀ s' ∧ PolyIs s'.mem (L.A 0 oAcc4) (nttInv f) := by
  have hc := h.1.K.ctx (by decide) hp.ctx
  exact nttInvL hp.ctx.ok g0 g1 (hc.sep00 (by decide) (by decide) (by decide)) hc.buf0 hc.buf0 h.2
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) vOK_facts.2.1, p⟩

theorem evAdd_ok {s : State} {f g : Poly} {k : Nat} (hk : k = 12 ∨ k = 13) (h : VEnv L b s₀ s ∧ PolyIs s.mem (L.A 0 oAcc4) f)
    (hg : PolyIs s.mem (L.A 0 (oPoly k)) g)
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4) (g1 : s.gpr .r1 = L.ptr 0 + BitVec.ofNat 32 (oPoly k)) :
    WP isa callAdd s fun s' => VEnv L b s₀ s' ∧ PolyIs s'.mem (L.A 0 oAcc4) (add f g) := by
  have hc := h.1.K.ctx (by decide) hp.ctx
  exact addL hp.ctx.ok g0 g1 (hc.sep00 (by offs4) (by rcases hk with rfl | rfl <;> decide)
    (by rcases hk with rfl | rfl <;> decide)) hc.buf0 (mem_rd_wr hc.buf0) h.2 hg
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) vOK_facts.2.2, p⟩

omit hp in
theorem vArgs_ok {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h8 : s.gpr .r8 = C) :
    WP isa (.block [ptrTo .r0 .r7 oAcc4, .mov .r1 (.imm 5), ptrTo .r2 .r8 1408, .mov .r3 (.imm 160)]) s
      fun s' => Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 oAcc4 ∧ s'.gpr .r1 = BitVec.ofNat 32 5 ∧
        s'.gpr .r2 = C + BitVec.ofNat 32 1408 ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * 5) := by
  have e1 : encodable (BitVec.ofNat 32 oAcc4) = true := by decide
  have e2 : encodable (5 : BitVec 32) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 1408) = true := by decide
  have e4 : encodable (160 : BitVec 32) = true := by decide
  run_block [ptrTo, e1, e2, e3, e4, h7, h8]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem ev8_ok {s : State} {f : Poly} (h : VEnv L b s₀ s ∧ PolyIs s.mem (L.A 0 oAcc4) f) :
    WP isa (.block [ptrTo .r0 .r7 oAcc4, .mov .r1 (.imm 5), ptrTo .r2 .r8 1408, .mov .r3 (.imm 160)]) s
      fun s' => (VEnv L b s₀ s' ∧ PolyIs s'.mem (L.A 0 oAcc4) f) ∧ s'.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4 ∧
        s'.gpr .r1 = BitVec.ofNat 32 5 ∧ s'.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 1408) ∧
        s'.gpr .r3 = BitVec.ofNat 32 (32 * 5) := by
  have hc := h.1.K.ctx (by decide) hp.ctx
  have g8 : s.gpr .r8 = L.ptr b.iC + BitVec.ofNat 32 b.oC := by
    rw [h.1.K.cs .r8 (by decide) (by decide) (by decide), hp.r8]
  exact WP.mono (vArgs_ok hc.r7 g8) fun s' ⟨o', a0, a1, a2, a3⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o'.x _ _) (fun _ h => absurd h List.not_mem_nil) rfl, by rw [o'.mem]; exact h.2⟩, a0, a1,
      by rw [a2, ptr_add_add32], a3⟩

omit hp in
theorem bytes1568 (m : Mem) (p : Addr) :
    bytesAt m p 1568 = bytesAt m p 352 ++ bytesAt m (p + BitVec.ofNat 64 352) 352 ++
      bytesAt m (p + BitVec.ofNat 64 704) 352 ++ bytesAt m (p + BitVec.ofNat 64 1056) 352 ++
      bytesAt m (p + BitVec.ofNat 64 1408) 160 := by
  rw [show (1568 : Nat) = 352 + (352 + (352 + (352 + 160))) from rfl, bytesAt_add, bytesAt_add, bytesAt_add,
    bytesAt_add, add_ofNat_add, add_ofNat_add, add_ofNat_add]
  simp only [List.append_assoc]

theorem ev9_ok {s : State} (h : VEnv L b s₀ s ∧ PolyIs s.mem (L.A 0 oAcc4)
      (VG.Proof.MlKem.encV1024 (ekB L b s₀) (mB L b s₀) (rB L s₀)))
    (g0 : s.gpr .r0 = L.ptr 0 + BitVec.ofNat 32 oAcc4) (g1 : s.gpr .r1 = BitVec.ofNat 32 5)
    (g2 : s.gpr .r2 = L.ptr b.iC + BitVec.ofNat 32 (b.oC + 1408)) (g3 : s.gpr .r3 = BitVec.ofNat 32 (32 * 5)) :
    WP isa callCompress4 s fun s' => KeptX [.r9, .r10, .r11] (L.RL (encW b)) s₀ s' ∧
      s'.gpr .r11 = (if okE L b s₀ 4 then 1 else 0) ∧
      bytesAt s'.mem (L.A b.iC b.oC) 1568 = VG.Proof.MlKem.ct1024 (aE L b s₀) (ekB L b s₀) (mB L b s₀) (rB L s₀) := by
  have hL := hp.ctx.ok
  have hc := h.1.K.ctx (by decide) hp.ctx
  obtain ⟨cb1, cb2⟩ := cBound hp
  have hs : sepB L.sizes (0, oAcc4, 1024) (b.iC, b.oC + 1408, 32 * 5) = true := by
    have := cSep hp (k := 1408) (n := 160) (by omega) (W := [(0, oAcc4, 1024)]) (by decide)
    simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true] at this
    exact sepB_symm this
  refine compressL4 hL g0 g1 g2 g3 (by decide) hs (mem_rd_wr hc.buf0)
    (by rw [h.1.K.wr]; exact hp.wC) h.2 fun s' k p => ⟨?_, ?_, ?_⟩
  · refine h.1.K.trans ((k.x _).sub fun r hr => ?_)
    simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact ⟨L.R b.iC b.oC 1568, by simp, Lay.R_sub_R hL cb1 (by omega) (by omega) cb2⟩
  · rw [k.cs .r11 (by decide) (by decide), h.1.r11]
  · have keep : ∀ i' < 4, bytesAt s'.mem (L.A b.iC (b.oC + 352 * i')) 352 =
        compressEncode 11 (VG.Proof.MlKem.encU1024 (aE L b s₀) (rB L s₀) i') := fun i' hi' => by
      rw [← h.1.c i' hi']
      refine Lay.bytes_keep hL k.frame ?_ (by decide)
      simp only [sepAll, List.all_cons, List.all_nil, Bool.and_true]
      exact sepB_same cb1 (by simp only [Lay.size] at cb2; omega) (by simp only [Lay.size] at cb2; omega) (by omega)
    have c0 := keep 0 (by decide)
    have c1 := keep 1 (by decide)
    have c2 := keep 2 (by decide)
    have c3 := keep 3 (by decide)
    simp only [Lay.A] at c0 c1 c2 c3 p ⊢
    rw [bytes1568, add_ofNat_add, add_ofNat_add, add_ofNat_add, add_ofNat_add]
    rw [show b.oC + 352 * 0 = b.oC + 0 from rfl] at c0
    rw [show 352 * 1 = 352 from rfl] at c1
    rw [show 352 * 2 = 704 from rfl] at c2
    rw [show 352 * 3 = 1056 from rfl] at c3
    rw [show 32 * 5 = 160 from rfl] at p
    rw [Nat.add_zero] at c0
    rw [c0, c1, c2, c3, p]; rfl

end

/-! ## The whole of K-PKE.Encrypt -/

theorem mu_sep : (∀ k < 8, [((0 : Nat), oPoly 13, (1024 : Nat))].all (sep0 (oPoly k) 1024) = true) ∧
    (∀ N < 9, [((0 : Nat), oPoly 13, (1024 : Nat))].all (sep0 (oPoly (4 + N)) 1024) = true) := by
  decide

section
variable {L : Lay} {b : EB} {s₀ : State} (hp : EncPre L b s₀)
include hp

theorem dec_pre {s₁ : State} (e₁ : EA L s₀ s₁) :
    Ctx L s₁ ∧ s₁.gpr .r4 = L.ptr b.iE + BitVec.ofNat 32 b.oE ∧
      sepAll L.sizes (b.iE, b.oE, 1536) [(0, 2048, 4096)] = true ∧ L.buf b.iE ∈ s₁.rd ++ s₁.wr :=
  ⟨EA.ctx hp e₁, by rw [EA.reg e₁ (by simp), hp.r4], sepAll_mono hp.sE (by simp [inB]) (by decide),
    by rw [e₁.rd, e₁.wr]; exact hp.wE⟩

omit hp in
theorem v_of {s₃ : State} (t₃ : ∀ k < 4, PolyIs s₃.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB L b s₀) k))
    (y₃ : ∀ j < 4, PolyIs s₃.mem (L.A 0 (oPoly (4 + j))) (VG.Proof.MlKem.encY (rB L s₀) j)) :
    ∀ k < 8, PolyIs s₃.mem (L.A 0 (oPoly k)) (if k < 4 then VG.Proof.MlKem.ekT (ekB L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - 4)) := fun k hk => by
  by_cases e : k < 4
  · simp only [e, ↓reduceIte]; exact t₃ k e
  · simp only [e, ↓reduceIte]
    have := y₃ (k - 4) (by omega)
    rwa [show 4 + (k - 4) = k by omega] at this

theorem rows_init {s₅ : State} (e₅ : EA L s₀ s₅) (d₅ : EData L b s₀ s₅) :
    WP isa (.block [.mov .r11 (.imm 1), .mov .r9 (.imm 0)]) s₅ (ERow L b s₀ 0) :=
  WP.mono flagInit_ok fun _ ⟨k, g11, g9, m⟩ =>
    ⟨(e₅.monoL fun w hw => List.mem_append_left _ hw).trans ((k.weaken (by simp)).mono
      (fun _ h => absurd h List.not_mem_nil)), g9, by rw [g11]; rfl,
      d₅.keep hp.ctx.ok (W := []) (by rw [m]; exact Frame.refl _ _) rfl rfl,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem data5 {s₄ s₅ : State} (ρ₄ : bytesAt s₄.mem (L.A 0 oSeed) 32 = ρE L b s₀)
    (v₄ : ∀ k < 8, PolyIs s₄.mem (L.A 0 (oPoly k)) (if k < 4 then VG.Proof.MlKem.ekT (ekB L b s₀) k
      else VG.Proof.MlKem.encY (rB L s₀) (k - 4)))
    (E₄ : ∀ N, 4 ≤ N → N < 9 → PolyIs s₄.mem (L.A 0 (oPoly (4 + N))) (VG.Proof.MlKem.cbd (rB L s₀) N))
    (f₅ : Frame (L.RL [(0, oPoly 13, 1024)]) s₄.mem s₅.mem)
    (μ₅ : PolyIs s₅.mem (L.A 0 (oPoly 13)) (decodeDecompress 1 (mB L b s₀))) : EData L b s₀ s₅ :=
  have hL := hp.ctx.ok
  ⟨(Lay.bytes_keep hL f₅ (hp.ctx.sepAll0 (by decide) (by decide)) (by decide)).trans ρ₄,
    fun k hk => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs4) (mu_sep.1 k hk)) (v₄ k hk),
    fun N h3 h7 => Lay.polyIs_keep hL f₅ (hp.ctx.sepAll0 (by offs4) (mu_sep.2 N h7)) (E₄ N h3 h7), μ₅⟩

theorem encrypt_ok : WP isa encrypt4 s₀ fun s => KeptX [.r9, .r10, .r11] (L.RL (encW b)) s₀ s ∧
    s.gpr .r11 = (if okE L b s₀ 4 then 1 else 0) ∧
    bytesAt s.mem (L.A b.iC b.oC) 1568 = VG.Proof.MlKem.ct1024 (aE L b s₀) (ekB L b s₀) (mB L b s₀) (rB L s₀) := by
  have hL := hp.ctx.ok
  refine WP.seq (WP.mono (enc1_ok hp) fun s₁ ⟨e₁, _, ρ₁⟩ => ?_)
  obtain ⟨hc₁, g4, hsE, hr₁⟩ := dec_pre hp e₁
  refine WP.seq (WP.mono (decT_init (L := L) (i := b.iE) (o := b.oE)) fun s₁' h₁' => ?_)
  refine WP.seq (WP.mono (decT_loop hc₁ g4 hsE hr₁ h₁') fun s₂ h₂ => ?_)
  obtain ⟨e₂, ρ₂, t₂⟩ := enc2_ok hp e₁ ρ₁ h₂
  refine WP.seq (WP.mono (enc3_ok hp e₂ ρ₂ t₂) fun s₃ ⟨e₃, ρ₃, t₃, y₃⟩ => ?_)
  refine WP.seq (WP.mono (enc4_ok hp e₃ ρ₃ (v_of t₃ y₃)) fun s₄ ⟨e₄, ρ₄, v₄, E₄⟩ => ?_)
  refine WP.seq (WP.mono (enc5a_ok hp e₄) fun s₄' ⟨h₄', a0, a1, a2, a3⟩ => ?_)
  refine WP.seq (WP.mono (enc5b_ok hp e₄ h₄' a0 a1 a2 a3) fun s₅ ⟨e₅, f₅, μ₅⟩ => ?_)
  have d₅ := data5 hp ρ₄ v₄ E₄ f₅ μ₅
  refine WP.seq (WP.mono (rows_init hp e₅ d₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (ERow L b s₀) (N := 4) (by decide) (fun i hi s h => encRow_step hp hi h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (ev1_ok hp h₇.venv) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₈.1 h₈.2 (o := oNtt4) (by decide)) fun s₉ ⟨h₉, a0, a1⟩ => ?_)
  refine WP.seq (WP.mono (ev3_ok hp h₉ a0 a1) fun s₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₁₀.1 h₁₀.2 (o := oPoly 12) (by decide)) fun s₁₁ ⟨h₁₁, b0, b1⟩ => ?_)
  refine WP.seq (WP.mono (evAdd_ok hp (.inl rfl) h₁₁ (h₁₁.1.d.e 8 (by decide) (by decide)) b0 b1)
    fun s₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (evArgs_ok hp h₁₂.1 h₁₂.2 (o := oPoly 13) (by decide)) fun s₁₃ ⟨h₁₃, c0, c1⟩ => ?_)
  refine WP.seq (WP.mono (evAdd_ok hp (.inr rfl) h₁₃ h₁₃.1.d.mu c0 c1) fun s₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (ev8_ok hp h₁₄) fun s₁₅ ⟨h₁₅, d0, d1, d2, d3⟩ => ?_)
  exact ev9_ok hp h₁₅ d0 d1 d2 d3

end

/-! ## The matrix, for the contracts -/

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem enc_some {ρ r : List Byte} (hk : okEnc ρ 4 = true) :
    ∀ i < 4, ∀ j < 4, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = some (aEnc ρ r i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk j (List.mem_range.mpr hj)
  have h₂ := List.all_eq_true.mp h₁ i (List.mem_range.mpr hi)
  simp only [rowSeed, ↓reduceIte] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [aEnc, effA, rowSeed, ↓reduceIte, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem enc_none {ρ : List Byte} (hk : okEnc ρ 4 = false) :
    ∃ i < 4, ∃ j < 4, sampleNTT 280 (VG.Proof.MlKem.matSeed ρ i j) = none := by
  rw [okEnc, List.all_eq_false] at hk
  obtain ⟨j, hj, h₁⟩ := hk
  rw [Bool.not_eq_true, okRow, List.all_eq_false] at h₁
  obtain ⟨i, hi, h₂⟩ := h₁
  simp only [rowSeed, ↓reduceIte] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

end Enc

end VG.Proof.MlKem1024.Arm
