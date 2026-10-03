import VerifiedGarbage.Proof.MlKem.X86_64.FragOf

/-!
# ML-KEM-768 on x86-64: the hash functions of the top-level functions

`hashAt ps rate suffix out len` zeroes the Keccak state, absorbs the pieces
`ps`, pads and squeezes `len` bytes to `out`: the output of the sponge from
the padded state of their concatenation (`hash_ok`, which
`Proof/MlKem/KPke.lean` relates to `G`, `H`, `J` and `PRF`), leaking only the
addresses (`hash_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt rates Repr squeezeFrom)

/-! ## Composing what calls leave -/

theorem Post.refl (s : State) (W : List Region) : Post s s W := ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Post.trans {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : Post s s₁ W₁) (h₂ : Post s₁ s₂ W₂)
    (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : Post s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.cs r hr).trans (h₁.cs r hr), ?_⟩
  have f₂ := h₂.frame
  rw [h₁.rsp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

theorem map_toR_post {s s' : State} {W : List Region} (hP : Post s s' W) {ws : List (Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ calleeSaved) : ws.map (toR s') = ws.map (toR s) :=
  List.map_congr_left fun w hw => by simp only [toR, hP.pa (h w hw)]

theorem PPost.trans {s s₁ s₂ : State} {ws₁ ws₂ ws : List (Ptr × Nat)} (h₁ : PPost s s₁ ws₁)
    (h₂ : PPost s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ calleeSaved) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : PPost s s₂ ws := by
  have h₂' : Post s₁ s₂ (ws₂.map (toR s)) := by rw [← map_toR_post h₁ hcs]; exact h₂
  refine Post.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

/-- A block that keeps the callee-saved registers and the permissions, and writes within `W`. -/
theorem post_of_keep {rs : List Reg} {s s' : State} {W : List Region} (k : Keep rs s s')
    (hrs : ∀ r ∈ calleeSaved, r ∉ rs) (hf : Frame W s.mem s'.mem) : Post s s' W :=
  ⟨k.2.1, k.2.2, fun r hr => k.gpr (hrs r hr), hf.mono fun _ hr => List.mem_append_left _ hr⟩

theorem sub_a {α : Type} {a b c : α} : ∀ w ∈ [a], w ∈ [a, b, c] := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_self ..

theorem sub_ab {α : Type} {a b c : α} : ∀ w ∈ [a, b], w ∈ [a, b, c] := fun w hw => by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact List.mem_cons_self ..
  · rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem sub_acb {α : Type} {a b c : α} : ∀ w ∈ [a, c, b], w ∈ [a, b, c] := fun w hw => by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact List.mem_cons_self ..
  rcases List.mem_cons.mp hw with rfl | hw
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem cs3 {a b c : Ptr × Nat} (ha : a.1.1 ∈ calleeSaved) (hb : b.1.1 ∈ calleeSaved) (hc : c.1.1 ∈ calleeSaved) :
    ∀ w ∈ [a, b, c], w.1.1 ∈ calleeSaved := fun w hw => by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ha
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hb
  · rw [List.mem_singleton] at hw; subst hw; exact hc

/-! ## Zeroing the state -/

theorem kzero_okP (s : State) (hw : Covers [⟨pa s (sc 0), 200⟩] s.wr) :
    WP isa (.block kzero) s fun s' => PPost s s' [(sc 0, 200)] ∧ stateAt s'.mem (pa s (sc 0)) = Spec.Sha3.zero :=
  WP.mono (kzero_ok s hw) fun _ ⟨hz, hf, k⟩ => ⟨post_of_keep k (by decide) hf, hz⟩

/-! ## Absorbing pieces -/

/-- A piece of the message: absorbed as `vg_keccak_absorb` needs, its register kept by the calls. -/
def pieceChk (bs wbs : List (Reg × Nat)) (p : Ptr × Nat) : Bool :=
  kabsChk bs wbs p.1 p.2 && decide (NA p.1) && decide (p.1.1 ∈ bases)

theorem pieceChk_keep {bs wbs : List (Reg × Nat)} {p : Ptr × Nat} (h : pieceChk bs wbs p = true) :
    keepB bs [(sc 0, 200), (sc 200, 640)] p.1 p.2 = true := by
  simp only [pieceChk, kabsChk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _, hin⟩, _⟩, s1⟩, s2⟩, _⟩, hcs⟩ := h
  simp only [keepB, List.all_cons, List.all_nil, s1, s2, hin, decide_eq_true hcs, Bool.and_self]

/-- The bytes of the pieces, concatenated. -/
abbrev pieces (s : State) (ps : List (Ptr × Nat)) : List Byte := ps.flatMap fun p => bytesAt s.mem (pa s p.1) p.2

theorem pieces_length (s : State) (ps : List (Ptr × Nat)) : (pieces s ps).length = totLen ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pieces, List.flatMap_cons, List.length_append, bytesAt_length] at ih ⊢
    rw [ih]; simp [totLen]

theorem pieces_keep {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) : ∀ {ps : List (Ptr × Nat)},
    (∀ p ∈ ps, keepB (rbs ++ wbs) ws p.1 p.2 = true) → pieces s' ps = pieces s ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [pieces, List.flatMap_cons]
    rw [L.keepBytes hP (h p (List.mem_cons_self ..))]
    exact congrArg _ (pieces_keep L hP fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- What absorbing the pieces `ps` from position `pos` does. -/
def AbsOk (rbs wbs : List (Reg × Nat)) (rate : Nat) (ps : List (Ptr × Nat)) : Prop :=
  ∀ {s : State} (_ : Lay rbs wbs s) (pos : Nat) (msg : List Byte),
    ps.all (pieceChk (rbs ++ wbs) wbs) = true → pos < rate → pos = msg.length % rate →
    Repr s.mem (pa s (sc 0)) rate msg →
    WP isa (absAll rate ps pos) s fun s' => PPost s s' [(sc 0, 200), (sc 200, 640)] ∧
      Repr s'.mem (pa s (sc 0)) rate (msg ++ pieces s ps)

theorem absAll_nil (rbs wbs : List (Reg × Nat)) (rate : Nat) : AbsOk rbs wbs rate [] :=
  fun _ _ _ _ _ _ hR => WP.block_nil ⟨Post.refl _ _, by simpa using hR⟩

theorem absAll_cons {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {rate : Nat} (hrate : rate ∈ rates) (p : Ptr) (l : Nat) {ps : List (Ptr × Nat)}
    (IH : AbsOk rbs wbs rate ps) : AbsOk rbs wbs rate ((p, l) :: ps) := by
  intro s L pos msg hps hpos hm hR
  simp only [List.all_cons, Bool.and_eq_true] at hps
  have hp := hps.1
  have hna : NA p := by
    simp only [pieceChk, Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1.2
  have hkc : kabsChk (rbs ++ wbs) wbs p l = true := by
    simp only [pieceChk, Bool.and_eq_true] at hp; exact hp.1.1
  have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
  rw [absAll]
  refine WP.seq (WP.mono (kabs_ok hna (KAbsH.of L hkc hrate hpos)) fun s₁ ⟨hP₁, hR₁⟩ => ?_)
  have hP₁' : PPost s s₁ [(sc 0, 200), (sc 200, 640)] := hP₁
  have L₁ := L.post hP₁.b hcs
  have e0 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
  have hR₁' := hR₁ msg hR hm
  rw [← e0] at hR₁'
  have h3 : ((pos + l) % rate) = (msg ++ bytesAt s.mem (pa s p) l).length % rate := by
    rw [List.length_append, bytesAt_length, hm, Nat.mod_add_mod]
  refine WP.mono (IH L₁ ((pos + l) % rate) (msg ++ bytesAt s.mem (pa s p) l) hps.2 (Nat.mod_lt _ hr0) h3 hR₁')
    fun s₂ ⟨hP₂, hR₂⟩ => ⟨PPost.trans hP₁' hP₂ (by decide) (fun w hw => hw) (fun w hw => hw), ?_⟩
  rw [e0, pieces_keep L hP₁'.b fun q hq => pieceChk_keep (List.all_eq_true.mp hps.2 q hq)] at hR₂
  simpa only [pieces, List.flatMap_cons, List.append_assoc] using hR₂

theorem absAll_ok {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {rate : Nat}
    (hrate : rate ∈ rates) (ps : List (Ptr × Nat)) : AbsOk rbs wbs rate ps := by
  induction ps with
  | nil => exact absAll_nil rbs wbs rate
  | cons p ps ih => exact absAll_cons hcs hrate p.1 p.2 ih

/-! ## The hash -/

/-- The output: `len` bytes to `out`, from position 0. -/
def hashChk (bs wbs : List (Reg × Nat)) (ps : List (Ptr × Nat)) (rate : Nat) (out : Ptr) (len : Nat) : Bool :=
  decide (rate ∈ rates) && kChk bs wbs && ps.all (pieceChk bs wbs) && ksqzChk bs wbs out len &&
    decide (NA out) && decide (out.1 ∈ calleeSaved)

theorem hashChk_spec {bs wbs : List (Reg × Nat)} {ps : List (Ptr × Nat)} {rate : Nat} {out : Ptr} {len : Nat}
    (h : hashChk bs wbs ps rate out len = true) :
    rate ∈ rates ∧ kChk bs wbs = true ∧ ps.all (pieceChk bs wbs) = true ∧ ksqzChk bs wbs out len = true ∧
      NA out ∧ out.1 ∈ calleeSaved := by
  simp only [hashChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem hash_ok {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {ps : List (Ptr × Nat)} {rate suffix : Nat} {out : Ptr} {len : Nat}
    (hc : hashChk (rbs ++ wbs) wbs ps rate out len = true) (hsuf : suffix < 256) {s : State} (L : Lay rbs wbs s) :
    WP isa (hashAt ps rate suffix out len) s fun s' => PPost s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧
      bytesAt s'.mem (pa s out) len =
        squeezeFrom rate (padded rate (BitVec.ofNat 8 suffix) (pieces s ps)) 0 len := by
  obtain ⟨hrate, hk, hps, hsq, hna, hocs⟩ := hashChk_spec hc
  obtain ⟨_, _, _, _, _, w0, _⟩ := kChk_spec L hk
  have hr0 : 0 < rate := by
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hrate; omega
  refine WP.seq (WP.mono (kzero_okP s w0) fun s₁ ⟨hP₁, hz⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  have e1 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
  have hpk : ∀ p ∈ ps, keepB (rbs ++ wbs) [(sc 0, 200)] p.1 p.2 = true := fun p hp => by
    have := pieceChk_keep (List.all_eq_true.mp hps p hp)
    simp only [keepB, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this ⊢
    exact ⟨this.1, this.2.1⟩
  have epc : pieces s₁ ps = pieces s ps := pieces_keep L hP₁.b hpk
  refine WP.seq (WP.mono (absAll_ok hcs hrate ps L₁ 0 [] hps hr0 rfl (by rw [e1]; exact repr_nil hz))
    fun s₂ ⟨hP₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b hcs
  have e2 : pa s₂ (sc 0) = pa s₁ (sc 0) := hP₂.pa (by decide)
  rw [List.nil_append, epc] at hR₂
  refine WP.seq (WP.mono (kpad_ok hsuf (KPadH.of L₂ hk hrate (pos := totLen ps % rate) (Nat.mod_lt _ hr0)))
    fun s₃ ⟨hP₃, hS₃⟩ => ?_)
  have hP₃' : PPost s₂ s₃ [(sc 0, 200), (sc 200, 640)] := hP₃
  have L₃ := L₂.post hP₃.b hcs
  have e3 : pa s₃ (sc 0) = pa s₂ (sc 0) := hP₃.pa (by decide)
  have hS := hS₃ (pieces s ps) (by rw [e2]; exact hR₂) (by rw [pieces_length])
  refine WP.mono (ksqz_ok hna (KSqzH.of L₃ hsq hrate)) fun s₄ ⟨hP₄, ho⟩ => ?_
  have hP₄' : PPost s₃ s₄ [(sc 0, 200), (out, len), (sc 200, 640)] := hP₄
  have eo : pa s₃ out = pa s out := by
    rw [hP₃.pa hocs, hP₂.pa hocs, hP₁.pa hocs]
  refine ⟨PPost.trans (PPost.trans (PPost.trans hP₁ hP₂ (by decide) sub_a sub_ab) hP₃'
    (by decide) (fun w hw => hw) sub_ab) hP₄' (cs3 (by decide) hocs (by decide)) (fun w hw => hw) sub_acb, ?_⟩
  rw [← eo, ho, e3, hS]

/-! ## Constant time -/

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem LRel.step {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c : Prog isa}
    (htr : RelCT isa (LRel rbs wbs) c fun _ _ => True)
    (hok : ∀ x, Lay rbs wbs x → WP isa c x fun x' => ∃ W, Post x x' W) :
    RelCT isa (LRel rbs wbs) c (LRel rbs wbs) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, Post x x' W) (fun x y h => ⟨hok x h.1, hok y h.2.1⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hcs hx.b hy.b

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  RelCT.postDep (block_nomem_tr fun _ hi => absurd hi List.not_mem_nil) (F := fun x x' => x' = x)
    (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem kChk_in {bs wbs : List (Reg × Nat)} (h : kChk bs wbs = true) : inB bs (sc 0) 200 = true := by
  simp only [kChk, wrOk, rdOk, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem absAll_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {rate : Nat}
    (hrate : rate ∈ rates) (hk : kChk (rbs ++ wbs) wbs = true) :
    ∀ (ps : List (Ptr × Nat)) (pos : Nat), ps.all (pieceChk (rbs ++ wbs) wbs) = true → pos < rate →
      RelCT isa (LRel rbs wbs) (absAll rate ps pos) (LRel rbs wbs)
  | [], _, _, _ => nil_tr
  | (p, l) :: ps, pos, hps, hpos => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hp := hps.1
    have hna : NA p := by
      simp only [pieceChk, Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1.2
    have hkc : kabsChk (rbs ++ wbs) wbs p l = true := by
      simp only [pieceChk, Bool.and_eq_true] at hp; exact hp.1.1
    have hin : inB (rbs ++ wbs) p l = true := by
      simp only [kabsChk, rdOk, Bool.and_eq_true] at hkc; exact hkc.1.1.1.2.2
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    exact RelCT.seq (LRel.step hcs (RelCT.mono (kabs_tr hna) (fun x y h =>
        ⟨KAbsH.of h.1 hkc hrate hpos, KAbsH.of h.2.1 hkc hrate hpos, h.eq (kChk_in hk), h.eq hin, h.2.2.2⟩)
        fun _ _ _ => trivial)
      fun x Lx => WP.mono (kabs_ok hna (KAbsH.of Lx hkc hrate hpos)) fun _ h => ⟨_, h.1⟩)
      (absAll_tr hcs hrate hk ps ((pos + l) % rate) hps.2 (Nat.mod_lt _ hr0))

theorem hash_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {ps : List (Ptr × Nat)} {rate suffix : Nat} {out : Ptr} {len : Nat}
    (hc : hashChk (rbs ++ wbs) wbs ps rate out len = true) (hsuf : suffix < 256) :
    RelCT isa (LRel rbs wbs) (hashAt ps rate suffix out len) fun _ _ => True := by
  obtain ⟨hrate, hk, hps, hsq, hna, _⟩ := hashChk_spec hc
  have hr0 : 0 < rate := by
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hrate; omega
  have hin : inB (rbs ++ wbs) out len = true := by
    simp only [ksqzChk, wrOk, rdOk, Bool.and_eq_true] at hsq; exact hsq.1.1.1.2.1.2
  refine RelCT.seq (LRel.step hcs (kzero_tr fun x y h => h.eq (kChk_in hk))
    fun x Lx => WP.mono (kzero_okP x (kChk_spec Lx hk).2.2.2.2.2.1) fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (absAll_tr hcs hrate hk ps 0 hps hr0) (RelCT.seq (LRel.step hcs (RelCT.mono (kpad_tr hsuf)
      (fun x y h => ⟨KPadH.of h.1 hk hrate (Nat.mod_lt _ hr0), KPadH.of h.2.1 hk hrate (Nat.mod_lt _ hr0),
        h.eq (kChk_in hk), h.2.2.2⟩) fun _ _ _ => trivial)
      fun x Lx => WP.mono (kpad_ok hsuf (KPadH.of Lx hk hrate (Nat.mod_lt _ hr0))) fun _ h => ⟨_, h.1⟩)
      (RelCT.mono (ksqz_tr hna) (fun x y h => ⟨KSqzH.of h.1 hsq hrate, KSqzH.of h.2.1 hsq hrate,
        h.eq (kChk_in hk), h.eq hin, h.2.2.2⟩) fun _ _ _ => trivial)))

end VG.Proof.MlKem.X86_64
