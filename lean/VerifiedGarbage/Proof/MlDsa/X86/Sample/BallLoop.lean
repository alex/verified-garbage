import VerifiedGarbage.Proof.MlDsa.X86.Sample.Ball

/-!
# ML-DSA on x86 (32-bit): the loop of `vg_mldsa_sample_in_ball`

Untrusted: everything here is checked by Lean. Iteration `k` takes the byte
`j` of the output: while `i < 256` (`cmp_piece`), if `j ≤ i`, it copies
`c[j]` to `c[i]` and tests the next sign bit, the low bit of the first word
(`move_ok`); stores `±1` to `c[j]` (`sign_piece`) and shifts the two words
right by one bit (`shift_ok`), incrementing `i`: `bStep` of
`Proof/MlDsa/Sample/Ball.lean`. Its branches and addresses depend on `i`,
`j` and the sign bits, functions of `c̃`, which agree in two runs with the
same `c̃` (`QPub`).
-/

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp bMove bShift bSet bTry bBody qImm)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt IPoly)
open VG.Proof.MlDsa.X86.Sample.RejNtt (nil_piece)

/-- The state of iteration `k`. -/
abbrev S' (s₀ : State) (k : Nat) : IPoly × Nat := st (L.Msg s₀) (τ s₀) k

/-- The byte of iteration `k`. -/
abbrev j' (s₀ : State) (k : Nat) : Nat := (jb (L.Msg s₀) k).toNat

/-- The signs used before iteration `k`. -/
abbrev t' (s₀ : State) (k : Nat) : Nat := (S' s₀ k).2 + τ s₀ - 256

/-- The sign bits. -/
abbrev G (s₀ : State) : Nat := Sg (L.Msg s₀)

/-- The coefficient iteration `k` sets `c[j]` to. -/
abbrev sg (s₀ : State) (k : Nat) : Int := if (signs (Xb (L.Msg s₀))).getD (t' s₀ k) false then -1 else 1

theorem G_lt (s₀ : State) : G s₀ < 2 ^ 64 := by
  have := leNat_lt ((Xb (L.Msg s₀)).take 8)
  rwa [List.length_take, Xb_length, show min 8 272 = 8 from rfl] at this

theorem sg_eq (s₀ : State) (k : Nat) : sg s₀ k = if (G s₀).testBit (t' s₀ k) then -1 else 1 := by
  simp only [sg, signs_getD]

/-- The polynomial with `c[i] ← c[j]`. -/
abbrev P1 (s₀ : State) (k : Nat) : IPoly := (S' s₀ k).1.set! (S' s₀ k).2 (S' s₀ k).1[j' s₀ k]!

/-- After `c[i] ← c[j]`, with the next sign bit in `ebx` (and ZF). -/
structure M1 (s₀ : State) (k : Nat) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 272, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (Xb (L.Msg s₀)).getD p 0
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (848 + k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (264 - k)
  ebp : s.gpr .ebp = L.aP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 (S' s₀ k).2
  eax : s.gpr .eax = L.aP s₀ + BitVec.ofNat 32 (4 * j' s₀ k)
  poly : ∀ jj < 256, coeffAt s.mem (L.aA s₀) jj = zw (ofInt (P1 s₀ k)[jj]!)
  lo : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k)
  hi : s.mem.readW (argAddr s₀ 2) 32 = BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 32))
  ebx : s.gpr .ebx = BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k)
  lt : (S' s₀ k).2 < 256
  le : j' s₀ k ≤ (S' s₀ k).2

/-! ## Addresses -/

theorem quad_add (x p : BitVec 32) (m : Nat) (hx : x = BitVec.ofNat 32 m) :
    x + x + (x + x) + p = p + BitVec.ofNat 32 (4 * m) := by
  rw [hx, ofNat_add_ofNat, ofNat_add_ofNat, BitVec.add_comm]
  congr 2; omega

theorem coef_ea {s₀ : State} (hp : QPre s₀) {i : Nat} (hi : i < 256) :
    (L.aP s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (L.aA s₀) i := by
  have ha := hp.1.a_fit
  rw [ea_add (by simp only [L] at ha ⊢; omega)]; rfl

theorem coef_in {s₀ s : State} (hp : QPre s₀) (h : Base L s₀ s) {i : Nat} (hi : i < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (L.aA s₀) i) 4 :=
  let ⟨r, hr, hc⟩ := hp.1.inA h.wr hi; ⟨r, List.mem_append_right _ hr, hc⟩

theorem coef_arg_sep {s₀ : State} (hp : QPre s₀) {i a : Nat} (hi : i < 256) (ha : a < 5) :
    Mem.Sep (argAddr s₀ a) 4 (coeffAddr (L.aA s₀) i) 4 :=
  fun x h₁ h₂ => hp.1.a_g x ((coeff_contains _ hi).byte h₂) ((arg_contains (n := 5) ha hp.1.sp').byte h₁)

/-! ## Moving `c[j]` to `c[i]` -/

theorem move_ok {s₀ : State} (hp : QPre s₀) {k : Nat} {s : State} (h : BI s₀ k (S' s₀ k) s)
    (hlt : (S' s₀ k).2 < 256) (hax : s.gpr .eax = BitVec.ofNat 32 (j' s₀ k)) (hle : j' s₀ k ≤ (S' s₀ k).2) :
    WP isa (.block bMove) s fun s' => M1 s₀ k s' ∧ eval .e s' = some (!(G s₀).testBit (t' s₀ k)) := by
  have hj : j' s₀ k < 256 := by omega
  have eaj := coef_ea hp hj
  have eai := coef_ea hp hlt
  have inj := coef_in hp h.toBase hj
  have ini := hp.1.inA h.wr hlt
  have a₁ := h.argEa (i := 1)
  have i₁ := h.argIn hp.1 (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have hvj : s.mem.readW (coeffAddr (L.aA s₀) (j' s₀ k)) 32 = zw (ofInt (S' s₀ k).1[j' s₀ k]!) := h.poly _ hj
  have rlo : ∀ W : BitVec 32, (s.mem.writeW (coeffAddr (L.aA s₀) (S' s₀ k).2) W).readW (argAddr s₀ 1) 32 =
      BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k) := fun W => by
    rw [Mem.readW_writeW_sep (coef_arg_sep hp hlt (by decide)) (by decide)]; exact h.lo
  have fa : ∀ W : BitVec 32, Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) (S' s₀ k).2) W) :=
    fun W => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hlt)
  have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = s.gpr .esi → s'.gpr .ecx = s.gpr .ecx →
      s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = s.gpr .edi →
      s'.gpr .eax = L.aP s₀ + BitVec.ofNat 32 (4 * j' s₀ k) →
      s'.gpr .ebx = BitVec.ofNat 32 (G s₀ / 2 ^ t' s₀ k) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (coeffAddr (L.aA s₀) (S' s₀ k).2) (zw (ofInt (S' s₀ k).1[j' s₀ k]!)) →
      M1 s₀ k s' := by
    intro s' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    refine ⟨⟨by rw [e1, h.esp], by rw [e8, h.rd], by rw [e9, h.wr], ?_⟩, fun p hp' => ?_, by rw [e2, h.esi],
      by rw [e3, h.ecx], by rw [e4, h.ebp], by rw [e5, h.edi], e6, fun jj hjj => ?_, by rw [e10]; exact rlo _,
      ?_, e7, hlt, hle⟩
    · rw [e10]; exact h.frame.writeW (r := L.aR s₀) (by simp) _ (coeff_contains _ hlt)
    · rw [e10]
      refine ((fa _) _ fun r hr hc => ?_).trans (h.out p hp')
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
    · rw [e10, coeffAt_writeW _ _ hjj hlt, P1, ipoly_set!_get _ _ (by simp only [n]; omega)]
      by_cases e : (S' s₀ k).2 = jj
      · rw [ifT e, ifT e]
      · rw [ifF e, ifF e]; exact h.poly jj hjj
    · rw [e10, Mem.readW_writeW_sep (coef_arg_sep hp hlt (by decide)) (by decide)]; exact h.hi
  apply WP.of_runBlock
  simp (config := {decide := true}) only [bMove, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, hax, h.ebp, h.edi, quad_add _ _ _ rfl, eaj, eai, inj, ini, hvj, a₁, i₁,
    rlo, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fin _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl, ?_⟩
  simp only [eval, signBit_eq]

/-! ## Two runs agree -/

namespace QPub
variable {s₀ s₀' : State} (hq : QPub s₀ s₀')
include hq

theorem eτ : τ s₀ = τ s₀' := by rw [τ, τ, hq.1.2 2 (by decide)]
theorem eS (k : Nat) : S' s₀ k = S' s₀' k := by simp only [S', hq.2, hq.eτ]
theorem ej (k : Nat) : j' s₀ k = j' s₀' k := by simp only [j', hq.2]
theorem et (k : Nat) : t' s₀ k = t' s₀' k := by simp only [t', hq.eS k, hq.eτ]
theorem eG : G s₀ = G s₀' := by simp only [G, hq.2]

end QPub

/-! ## The sign -/

theorem sign_piece (k : Nat) :
    Piece QPre QPub (fun s₀ s => M1 s₀ k s ∧ eval .e s = some (!(G s₀).testBit (t' s₀ k)))
      (fun s₀ s => M1 s₀ k s ∧ s.gpr .edx = zw (ofInt (sg s₀ k)))
      (.ite .e (.block [.mov .edx (.imm 1)]) (.block [.mov .edx (.imm (qImm - 1))])) := by
  refine Piece.ite (fun s₀ => !(G s₀).testBit (t' s₀ k)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eG, hq.et]) ?_ ?_
  · refine Piece.taint [] (fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    have hs : sg s₀ k = 1 := by
      rw [sg_eq]; simp only [Bool.not_eq_true'] at hb; rw [hb]; rfl
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.setReg, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
      by simp [h.edi], by simp [h.eax], h.poly, h.lo, h.hi, by simp [h.ebx], h.lt, h.le⟩, ?_⟩
    rw [hs]; simp; rfl
  · refine Piece.taint [] (fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    have hs : sg s₀ k = -1 := by
      rw [sg_eq]; simp only [Bool.not_eq_false'] at hb; rw [hb]; rfl
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.setReg, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
      by simp [h.edi], by simp [h.eax], h.poly, h.lo, h.hi, by simp [h.ebx], h.lt, h.le⟩, ?_⟩
    rw [hs]; simp; rfl

/-! ## `c[j] ← ±1`, and the sign bits shifted -/

theorem st_set {s₀ : State} {k : Nat} (hk : k < 264) (hlt : (S' s₀ k).2 < 256) (hle : j' s₀ k ≤ (S' s₀ k).2) :
    S' s₀ (k + 1) = ((P1 s₀ k).set! (j' s₀ k) (sg s₀ k), (S' s₀ k).2 + 1) := by
  rw [S', st_succ _ _ hk, bStep, ifT (show (S' s₀ k).2 < n by simp only [n]; omega), ifF (Nat.not_lt.mpr hle)]

theorem shift_ok {s₀ : State} (hp : QPre s₀) {k : Nat} (hk : k < 264) {s : State} (h : M1 s₀ k s)
    (hdx : s.gpr .edx = zw (ofInt (sg s₀ k))) :
    WP isa (.block bShift) s fun s' => BI s₀ k (S' s₀ (k + 1)) s' := by
  have hj : j' s₀ k < 256 := by have := h.lt; have := h.le; omega
  have eaj := coef_ea hp hj
  have inj := hp.1.inA h.wr hj
  have a₁ := h.argEa (i := 1)
  have a₂ := h.argEa (i := 2)
  have i₂ := h.argIn hp.1 (i := 2) (by decide)
  have w₁ := h.argInW hp.1 (i := 1) (by decide)
  have w₂ := h.argInW hp.1 (i := 2) (by decide)
  simp only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
  have rhi : ∀ W : BitVec 32, (s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) W).readW (argAddr s₀ 2) 32 =
      BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 32)) := fun W => by
    rw [Mem.readW_writeW_sep (coef_arg_sep hp hj (by decide)) (by decide)]; exact h.hi
  have ge : 256 - τ s₀ ≤ (S' s₀ k).2 := st_ge (L.Msg s₀) (τ s₀) k
  have hτ := hp.τ_le
  have et : (S' s₀ (k + 1)).2 + τ s₀ - 256 = t' s₀ k + 1 := by
    rw [st_set hk h.lt h.le]; simp only [t']; omega
  have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = s.gpr .esi → s'.gpr .ecx = s.gpr .ecx →
      s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = s.gpr .edi + 1 → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = ((s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) (zw (ofInt (sg s₀ k)))).writeW (argAddr s₀ 1)
        (BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 1)))).writeW (argAddr s₀ 2)
        (BitVec.ofNat 32 (G s₀ / 2 ^ (t' s₀ k + 1 + 32))) →
      BI s₀ k (S' s₀ (k + 1)) s' := by
    intro s' e1 e2 e3 e4 e5 e6 e7 e8
    have fg : Frame [L.gR s₀] (s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) (zw (ofInt (sg s₀ k)))) s'.mem := by
      rw [e8]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')).writeW
        (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')
    have fa : Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) (j' s₀ k)) (zw (ofInt (sg s₀ k)))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)
    have fw : Frame (L.W s₀) (P0 s₀).mem s'.mem :=
      (h.frame.trans (fa.mono (by simp))).trans (fg.mono (by simp))
    refine ⟨⟨by rw [e1, h.esp], by rw [e6, h.rd], by rw [e7, h.wr], fw⟩, fun p hp' => ?_, by rw [e2, h.esi],
      by rw [e3, h.ecx], by rw [e4, h.ebp], ?_, fun jj hjj => ?_, ?_, ?_⟩
    · rw [fg.bytes (R := ⟨L.sA s₀, 2048⟩) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.s_g)
        (show (2048 : Nat) ≤ 2 ^ 64 by decide) (show 840 + p < 2048 by omega)]
      refine (fa _ fun r hr hc => ?_).trans (h.out p hp')
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
    · rw [e5, h.edi, st_set hk h.lt h.le, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
    · rw [coeffAt_eq, fg.readW (coeff_contains _ hjj) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g)
        (by decide), ← coeffAt_eq, coeffAt_writeW _ _ hjj hj, st_set hk h.lt h.le,
        ipoly_set!_get _ _ (by simp only [n]; omega)]
      by_cases e : j' s₀ k = jj
      · rw [ifT e, ifT e]
      · rw [ifF e, ifF e]; exact h.poly jj hjj
    · rw [e8, Mem.readW_writeW_sep (slots_sep hp) (by decide), Mem.readW_writeW_self32, et]
    · rw [e8, Mem.readW_writeW_self32, et]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [bShift, argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.eax, h.ebx, hdx, eaj, inj, a₁, a₂, i₂, w₁, w₂, rhi, signs_shift,
    signs_shift_hi (G_lt s₀), ite_true, ite_false, Option.some.injEq, exists_eq_left']
  exact fin _ (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl

/-! ## An iteration -/

theorem st_skip {s₀ : State} {k : Nat} (hk : k < 264) (hgt : (S' s₀ k).2 < j' s₀ k) :
    S' s₀ (k + 1) = S' s₀ k := by
  rw [S', st_succ _ _ hk, bStep]
  by_cases hl : (S' s₀ k).2 < n
  · rw [ifT hl, ifT hgt]
  · rw [ifF hl]

theorem st_full {s₀ : State} {k : Nat} (hk : k < 264) (hf : ¬ (S' s₀ k).2 < 256) : S' s₀ (k + 1) = S' s₀ k := by
  rw [S', st_succ _ _ hk, bStep, ifF (show ¬ (S' s₀ k).2 < n by simp only [n]; omega)]

theorem set_piece (k : Nat) (hk : k < 264) :
    Piece QPre QPub (fun s₀ s => ((BI s₀ k (S' s₀ k) s ∧ (S' s₀ k).2 < 256 ∧
        s.gpr .eax = BitVec.ofNat 32 (j' s₀ k)) ∧ eval .b s = some (decide ((S' s₀ k).2 < j' s₀ k))) ∧
        decide ((S' s₀ k).2 < j' s₀ k) = false)
      (fun s₀ s => BI s₀ k (S' s₀ (k + 1)) s) bSet := by
  refine Piece.seq (Piece.taint [.eax, .edi, .ebp, .esp]
    (fun s₀ s hp ⟨⟨⟨h, hlt, hax⟩, _⟩, hb⟩ => move_ok hp h hlt hax (by simp at hb; omega))
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨h, _, hax⟩, _⟩, _⟩ ⟨⟨⟨h', _, hax'⟩, _⟩, _⟩ r hr => ?_) (by taint_decide))
    (Piece.seq (sign_piece k) (Piece.taint [.eax, .edi, .esp] (fun s₀ s hp ⟨h, hdx⟩ => shift_ok hp hk h hdx)
      (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by taint_decide)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [hax, hax', hq.ej]
    · rw [h.edi, h'.edi, hq.eS]
    · rw [h.ebp, h'.ebp, hq.1.aP hL]
    · rw [h.esp, h'.esp, hq.1.e1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.eax, h'.eax, hq.ej, hq.1.aP hL]
    · rw [h.edi, h'.edi, hq.eS]
    · rw [h.esp, h'.esp, hq.1.e1]

theorem try_piece (k : Nat) (hk : k < 264) :
    Piece QPre QPub (fun s₀ s => BI s₀ k (S' s₀ k) s ∧ (S' s₀ k).2 < 256)
      (fun s₀ s => BI s₀ k (S' s₀ (k + 1)) s) bTry := by
  refine Piece.seq (B := fun s₀ s => (BI s₀ k (S' s₀ k) s ∧ (S' s₀ k).2 < 256 ∧
      s.gpr .eax = BitVec.ofNat 32 (j' s₀ k)) ∧ eval .b s = some (decide ((S' s₀ k).2 < j' s₀ k))) ?_
    (Piece.ite (fun s₀ => decide ((S' s₀ k).2 < j' s₀ k)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.eS, hq.ej]) ?_ (set_piece k hk))
  · refine Piece.taint [.esi] (fun s₀ s hp ⟨h, hlt⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
      (by taint_decide)
    · have hs := hp.1.s_fit
      have e0 : (L.sP s₀ + BitVec.ofNat 32 (848 + k) + BitVec.ofNat 32 0).setWidth 64 =
          L.sA s₀ + BitVec.ofNat 64 (840 + (8 + k)) := by
        rw [ea_add (by simp only [L] at hs ⊢; omega)]; congr 2; omega
      have i0 := hp.1.inS' h.wr (o := 840 + (8 + k)) (n := 1) (by omega)
      have v0 := h.out (8 + k) (by omega)
      have hle : (S' s₀ k).2 ≤ 256 := st_le (L.Msg s₀) (τ s₀) k
      apply WP.of_runBlock
      simp (config := {decide := true}) only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags, Option.map_some,
        Option.bind_some, h.esi, e0, i0, v0, ite_true, ite_false, Option.some.injEq, exists_eq_left']
      refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ecx], by simp [h.ebp],
        by simp [h.edi], h.poly, h.lo, h.hi⟩, hlt, ?_⟩, ?_⟩
      · exact eq_ofNat_of_toNat (toNat_byte32 _)
      · simp only [eval, h.edi, toNat_byte32, toNat_ofNat32 (show (S' s₀ k).2 < 2 ^ 32 by omega)]
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esi, h'.esi, hq.1.sP hL]
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => st_skip hk (of_decide_eq_true hb) ▸ h

theorem body_piece (k : Nat) (hk : k < 264) :
    Piece QPre QPub (fun s₀ s => BI s₀ k (S' s₀ k) s)
      (fun s₀ s => BI s₀ (k + 1) (S' s₀ (k + 1)) s ∧ eval .ne s = some (decide (k + 1 < 264))) bBody := by
  refine Piece.seq (B := fun s₀ s => BI s₀ k (S' s₀ k) s ∧ eval .b s = some (decide ((S' s₀ k).2 < 256)))
    (Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide))
    (Piece.seq (B := fun s₀ s => BI s₀ k (S' s₀ (k + 1)) s)
      (Piece.ite (fun s₀ => decide ((S' s₀ k).2 < 256)) (fun _ _ _ h => h.2)
        (fun s₀ s₀' _ _ hq => by rw [hq.eS])
        ((try_piece k hk).mono (fun _ _ _ ⟨⟨h, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h)
        (nil_piece fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => st_full hk (of_decide_eq_false hb) ▸ h))
      (Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)))
  · have hle : (S' s₀ k).2 ≤ 256 := st_le (L.Msg s₀) (τ s₀) k
    have h256 : (256 : BitVec 32).toNat = 256 := rfl
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨h.esp, h.rd, h.wr, h.frame⟩, h.out, h.esi, h.ecx, h.ebp, h.edi, h.poly, h.lo, h.hi⟩, ?_⟩
    simp only [eval, h.edi, h256, toNat_ofNat32 (show (S' s₀ k).2 < 2 ^ 32 by omega)]
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, by simp [h.ebp], by simp [h.edi], h.poly,
      h.lo, h.hi⟩, ?_⟩
    · simp only [ite_true, h.esi]
      rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2
    · simp only [ite_true, h.ecx]
      exact cnt_next hk
    · simp only [eval, h.ecx]
      exact cnt_ne hk (by omega)

theorem loop_piece : Piece QPre QPub (fun s₀ s => BI s₀ 0 (S' s₀ 0) s) (fun s₀ s => BI s₀ 264 (S' s₀ 264) s)
    (.loop bBody .ne) :=
  Piece.loop (fun k s₀ s => BI s₀ k (S' s₀ k) s) (by decide) fun k hk => body_piece k hk

end VG.Proof.MlDsa.X86.Sample.Ball
