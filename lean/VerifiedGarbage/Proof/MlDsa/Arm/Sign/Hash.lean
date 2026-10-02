import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Keccak

/-!
# ML-DSA signing on ARMv7: `H` of pieces of memory

`shakeAt ps out len` zeroes the Keccak state, absorbs the pieces `ps`, pads
and squeezes `len` bytes to `out`: `H` of their concatenation (`shake_ok`),
leaking only the addresses (`shake_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`. -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : Spec.Sha3.State := absorb rate (pad rate suffix m)

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

/-- `H(s, d) = SHAKE256(s, 8d)`: rate 136, suffix `0x1f`. -/
theorem H_eq (m : List Byte) (d : Nat) : H m d = squeezeFrom 136 (padded 136 (BitVec.ofNat 8 0x1f) m) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) : Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

/-- A piece of the message: absorbed as `vg_keccak_absorb` needs, its register kept by the calls. -/
def pieceChk (bs : List (Reg × Nat)) (p : Ptr × Nat) : Bool :=
  kabsChk bs p.1 p.2 && decide (p.1.1 ∈ bases)

/-- The bytes of the pieces, concatenated. -/
abbrev pieces (s : State) (ps : List (Ptr × Nat)) : List Byte := ps.flatMap fun p => bytesAt s.mem (pa s p.1) p.2

theorem pieces_length (s : State) (ps : List (Ptr × Nat)) : (pieces s ps).length = totLen ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pieces, List.flatMap_cons, List.length_append, VG.Proof.MlKem.bytesAt_length] at ih ⊢
    rw [ih]; simp [totLen]

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem pieceChk_keep {p : Ptr × Nat} (h : pieceChk (rbs ++ wbs) p = true) :
    keepB (rbs ++ wbs) [(sc 0, 200), (sc 200, 640)] p.1 p.2 = true := by
  simp only [pieceChk, kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hin, _⟩, _⟩, s1⟩, s2⟩, hcs⟩ := h
  simp only [keepB, List.all_cons, List.all_nil, s1, s2, hin, decide_eq_true hcs, Bool.and_self]

theorem pieces_keep {s s' : State} (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) :
    ∀ {ps : List (Ptr × Nat)}, (∀ p ∈ ps, keepB (rbs ++ wbs) ws p.1 p.2 = true) → pieces s' ps = pieces s ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [pieces, List.flatMap_cons]
    rw [L.keepBytes hP (h p (List.mem_cons_self ..))]
    exact congrArg _ (pieces_keep L hP fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hcs_trans {s s₁ s₂ : State} (h₁ : CS s s₁) (h₂ : CS s₁ s₂) : CS s s₂ := CS.trans h₁ h₂

theorem bases_all : ∀ w ∈ [((sc 0 : Ptr), 200), ((sc 200 : Ptr), 640)], w.1.1 ∈ bases := by
  decide

/-- What absorbing the pieces `ps` from position `pos` does. -/
def AbsOk (D : Nat) (rbs wbs : List (Reg × Nat)) (rate : Nat) (ps : List (Ptr × Nat)) : Prop :=
  ∀ (s : State) (_ : Lay D rbs wbs s) (pos : Nat) (msg : List Byte),
    ps.all (pieceChk (rbs ++ wbs)) = true → pos < rate → pos = msg.length % rate →
    Repr s.mem (pa s (sc 0)) rate msg →
    WP isa (absAll rate ps pos) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧
      CS s s' ∧ Repr s'.mem (pa s (sc 0)) rate (msg ++ pieces s ps)

theorem absAll_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) : ∀ (ps : List (Ptr × Nat)), AbsOk D rbs wbs rate ps
  | [] => fun _ _ _ _ _ _ _ hR => WP.block_nil ⟨PostB.refl _ _ _, fun _ _ _ => rfl, by simpa using hR⟩
  | (p, l) :: ps => by
    intro s L pos msg hps hpos hm hR
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : kabsChk (rbs ++ wbs) p l = true := by
      simp only [pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    refine WP.seq (WP.mono (kabs_ok L hD hk hkc hrate hpos) fun s₁ ⟨hP₁, hc₁, hR₁⟩ => ?_)
    have L₁ := L.post hP₁ hcs
    have e0 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
    have hR₁' := hR₁ msg hR hm
    rw [← e0] at hR₁'
    have h3 : ((pos + l) % rate) = (msg ++ bytesAt s.mem (pa s p) l).length % rate := by
      rw [List.length_append, VG.Proof.MlKem.bytesAt_length, hm, Nat.mod_add_mod]
    refine WP.mono (absAll_ok hcs hD hk hrate ps s₁ L₁ ((pos + l) % rate) (msg ++ bytesAt s.mem (pa s p) l) hps.2
      (Nat.mod_lt _ hr0) h3 hR₁') fun s₂ ⟨hP₂, hc₂, hR₂⟩ =>
        ⟨PPostB.trans hP₁ hP₂ bases_all (fun w hw => hw) (fun w hw => hw), hcs_trans hc₁ hc₂, ?_⟩
    rw [e0, pieces_keep L hP₁ fun q hq => pieceChk_keep (List.all_eq_true.mp hps.2 q hq)] at hR₂
    simpa only [pieces, List.flatMap_cons, List.append_assoc] using hR₂

/-- The output: `len` bytes to `out`. -/
def shakeChk (bs wbs : List (Reg × Nat)) (ps : List (Ptr × Nat)) (out : Ptr) (len : Nat) : Bool :=
  kChk bs wbs && ps.all (pieceChk bs) && ksqzChk bs wbs out len

theorem shakeChk_spec {bs wbs : List (Reg × Nat)} {ps : List (Ptr × Nat)} {out : Ptr} {len : Nat}
    (h : shakeChk bs wbs ps out len = true) :
    kChk bs wbs = true ∧ ps.all (pieceChk bs) = true ∧ ksqzChk bs wbs out len = true := by
  simp only [shakeChk, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem shake_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : shakeChk (rbs ++ wbs) wbs ps out len = true) {s : State} (L : Lay D rbs wbs s) :
    WP isa (shakeAt ps out len) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧
      CS s s' ∧ bytesAt s'.mem (pa s out) len = H (pieces s ps) len := by
  obtain ⟨hk, hps, hsq⟩ := shakeChk_spec hc
  have hocs : out.1 ∈ bases := (ksqzChk_spec hsq).2.2.1
  have hrate : (136 : Nat) ∈ rates := by decide
  refine WP.seq (WP.mono (kzero_ok L hk) fun s₁ ⟨hP₁, hc₁, hz⟩ => ?_)
  have L₁ := L.post hP₁ hcs
  have e1 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
  have hpk : ∀ p ∈ ps, keepB (rbs ++ wbs) [(sc 0, 200)] p.1 p.2 = true := fun p hp => by
    have := pieceChk_keep (List.all_eq_true.mp hps p hp)
    simp only [keepB, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this ⊢
    exact ⟨this.1, this.2.1⟩
  have epc : pieces s₁ ps = pieces s ps := pieces_keep L hP₁ hpk
  refine WP.seq (WP.mono (absAll_ok hcs hD hk hrate ps s₁ L₁ 0 [] hps (by decide) rfl
    (by rw [e1]; exact repr_nil hz)) fun s₂ ⟨hP₂, hc₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂ hcs
  have e2 : pa s₂ (sc 0) = pa s₁ (sc 0) := hP₂.pa (by decide)
  rw [List.nil_append, epc] at hR₂
  refine WP.seq (WP.mono (kpad_ok L₂ hD hk hrate (pos := totLen ps % 136) (Nat.mod_lt _ (by decide))
    (show 0x1f < 256 by decide)) fun s₃ ⟨hP₃, hc₃, hS₃⟩ => ?_)
  have L₃ := L₂.post hP₃ hcs
  have e3 : pa s₃ (sc 0) = pa s₂ (sc 0) := hP₃.pa (by decide)
  have hS := hS₃ (pieces s ps) (by rw [e2]; exact hR₂) (by rw [pieces_length])
  refine WP.mono (ksqz_ok L₃ hD hk hsq hrate) fun s₄ ⟨hP₄, hc₄, ho⟩ => ?_
  have eo : pa s₃ out = pa s out := by rw [hP₃.pa hocs, hP₂.pa hocs, hP₁.pa hocs]
  have h12 : PPostB D s s₂ [(sc 0, 200), (sc 200, 640)] :=
    PPostB.trans hP₁ hP₂ bases_all (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_self ..)
      (fun w hw => hw)
  have h123 : PPostB D s s₃ [(sc 0, 200), (sc 200, 640)] := PPostB.trans h12 hP₃ bases_all (fun w hw => hw) (fun w hw => hw)
  have hcs4 : ∀ w ∈ [((sc 0 : Ptr), 200), (out, len), ((sc 200 : Ptr), 640)], w.1.1 ∈ bases := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    exacts [by decide, hocs, by decide]
  refine ⟨PPostB.trans h123 hP₄ hcs4 (fun w hw => ?_) (fun w hw => ?_),
    hcs_trans (hcs_trans (hcs_trans hc₁ hc₂) hc₃) hc₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h <;> simp [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h <;> simp [h]
  rw [← eo, ho, e3, hS, H_eq]

/-! ## Constant time -/

theorem LRel.step (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c : Prog isa}
    (htr : RelCT isa (LRel D rbs wbs) c fun _ _ => True)
    (hok : ∀ x, Lay D rbs wbs x → WP isa c x fun x' => ∃ W, PostB D x x' W) :
    RelCT isa (LRel D rbs wbs) c (LRel D rbs wbs) :=
  VG.Proof.MlDsa.Arm.Sign.postDep htr (F := fun x x' => ∃ W, PostB D x x' W) (fun x y h => ⟨hok x h.lx, hok y h.ly⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hcs hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  VG.Proof.MlDsa.Arm.Sign.postDep (block_nomem_tr fun _ hi => absurd hi List.not_mem_nil)
    (F := fun x x' => x' = x) (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem absAll_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) :
    ∀ (ps : List (Ptr × Nat)) (pos : Nat), ps.all (pieceChk (rbs ++ wbs)) = true → pos < rate →
      RelCT isa (LRel D rbs wbs) (absAll rate ps pos) (LRel D rbs wbs)
  | [], _, _, _ => nil_tr
  | (p, l) :: ps, pos, hps, hpos => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : kabsChk (rbs ++ wbs) p l = true := by
      simp only [pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    exact RelCT.seq (LRel.step hcs (kabs_tr hD hk hkc hrate hpos)
      fun x Lx => WP.mono (kabs_ok Lx hD hk hkc hrate hpos) fun _ h => ⟨_, h.1⟩)
      (absAll_tr hcs hD hk hrate ps ((pos + l) % rate) hps.2 (Nat.mod_lt _ hr0))

theorem shake_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 8 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : shakeChk (rbs ++ wbs) wbs ps out len = true) :
    RelCT isa (LRel D rbs wbs) (shakeAt ps out len) (LRel D rbs wbs) := by
  obtain ⟨hk, hps, hsq⟩ := shakeChk_spec hc
  have hrate : (136 : Nat) ∈ rates := by decide
  have i0 : inB (rbs ++ wbs) (sc 0) 200 = true := (kChk_spec hk).2.2.1
  refine RelCT.seq (LRel.step hcs (kzero_tr fun x y h => h.eq i0)
    fun x Lx => WP.mono (kzero_ok Lx hk) fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (absAll_tr hcs hD hk hrate ps 0 hps (by decide)) (RelCT.seq (LRel.step hcs
      (kpad_tr hD hk hrate (Nat.mod_lt _ (by decide)))
      fun x Lx => WP.mono (kpad_ok Lx hD hk hrate (Nat.mod_lt _ (by decide)) (show 0x1f < 256 by decide))
        fun _ h => ⟨_, h.1⟩)
      (LRel.step hcs (ksqz_tr hD hk hsq hrate) fun x Lx => WP.mono (ksqz_ok Lx hD hk hsq hrate) fun _ h => ⟨_, h.1⟩)))

end

end VG.Proof.MlDsa.Arm.Sign
