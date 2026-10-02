import VerifiedGarbage.Proof.MlKem.X86.TopHash

/-!
# ML-KEM on x86 (32-bit): the code of the top-level functions between calls

Storing a byte in `scratch` (`st8_piece`), copying words (`copyW_piece`), and,
after a call of `vg_mlkem_sample_ntt`, keeping the AND of the values it
returned and masking the polynomial it sampled (`maskA_piece`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem wp_andr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d &&& s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d &&& s.gpr r) false false).setReg d (s.gpr d &&& s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_subr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - s.gpr r) (decide ((s.gpr d).toNat < (s.gpr r).toNat))
      (subOverflow (s.gpr d) (s.gpr r) (s.gpr d - s.gpr r))).setReg d (s.gpr d - s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_store' {b r : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 4)
    (k : ∀ s', (∀ x, s'.gpr x = s.gpr x) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (s.ea (at_ b disp)) (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ b disp) r :: is)) s Q :=
  wp_store hin (k _ (fun _ => rfl) rfl rfl rfl)

theorem wp_store8 {b : Reg} {r : Reg8} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 1)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (s.ea (at_ b disp)) ((s.gpr r.reg).setWidth 8) } Q) :
    WP isa (.block (.store8 (at_ b disp) r :: is)) s Q :=
  wp_cons (by simp only [exec, State.store8, hin, ite_true]) k

/-! ## A byte -/

theorem st8_piece (o v : Nat) (hc : Y.okW ⟨Y.sc, o, 1⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block (st8 o v)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block (st8 o v)) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have ea : (s.gpr .esi + BitVec.ofNat 32 o).setWidth 64 = Buf.addr s₀ ⟨Y.sc, o, 1⟩ := by rw [h.esi]
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 1) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    have hin : InRegions s.wr (Buf.addr s₀ ⟨Y.sc, o, 1⟩) 1 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 1) (Nat.le_refl _)
      simpa using this
    refine wp_movi fun s₁ o₁ v₁ => ?_
    have h₁ := h.only o₁ (by decide) (by decide)
    have ea₁ : s₁.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 1⟩ := by
      simp only [State.ea, at_]; rw [o₁.gpr _ (by decide)]; exact ea
    refine wp_store8 (by rw [ea₁, h₁.wr, ← h.wr]; exact hin) (WP.block_nil_iff.mpr ?_)
    refine hQ s₀ s _ hp ha ⟨h₁.esp, h₁.rd, h₁.wr, h₁.esi, ?_⟩ ?_
    · show Frame _ _ (s₁.mem.writeW _ _)
      rw [ea₁]; exact h₁.frame.writeW (w := 8) hr _ hcr
    · show s₁.mem.writeW _ _ = _
      rw [ea₁, o₁.mem, show s₁.gpr Reg8.al.reg = BitVec.ofNat 32 v from v₁]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## Copying words -/

/-- The bytes after a word is written at offset `4k`. -/
theorem wordw_bytes {m : Mem} {d : Addr} {w : BitVec 32} {k j : Nat} (hk : 4 * k + 4 < 2 ^ 64)
    (hj : j < 4 * k + 4) :
    (m.writeW (d + BitVec.ofNat 64 (4 * k)) w) (d + BitVec.ofNat 64 j) =
      if 4 * k ≤ j then w.extractLsb' (8 * (j - 4 * k)) 8 else m (d + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW, Mem.write]
  by_cases e : 4 * k ≤ j
  · have t : (d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k))).toNat = j - 4 * k := by
      rw [show d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 (j - 4 * k) by
        rw [show j = 4 * k + (j - 4 * k) by omega, BitVec.ofNat_add]; bv_omega]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left e, t, ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right e, ite_eq_right fun h => ?_]
    have t : (d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k))).toNat = 2 ^ 64 - (4 * k - j) := by
      have : d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 j - BitVec.ofNat 64 (4 * k) := by
        bv_omega
      rw [this, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
        Nat.mod_eq_of_lt (a := 4 * k) (by omega)]
      omega
    rw [t] at h
    omega

theorem copyW_piece (sa so da dO n : Nat) (hn : 0 < n) (hn' : n < 2 ^ 30)
    (hc : (Y.ok ⟨sa, so, 4 * n⟩ && Y.okW ⟨da, dO, 4 * n⟩ && Y.sep ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩) = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .edi ⟨sa, so, 4 * n⟩ ++
      ptrTo Y.sc .ebp ⟨da, dO, 4 * n⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 n))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, 4 * n⟩] s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, 4 * n⟩) (4 * n) = bytesAt s.mem (Buf.addr s₀ ⟨sa, so, 4 * n⟩) (4 * n) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (copyW Y.sc ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩ n) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, hD⟩, dSD⟩ := hc'
  have hD₁ := (Lay.okW_iff.mp hD).1
  let S : Buf := ⟨sa, so, 4 * n⟩
  let D : Buf := ⟨da, dO, 4 * n⟩
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .edi = S.ptr s₀ ∧ s₁.gpr .ebp = D.ptr s₀ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n) (fun s₀ s hp h => ?_) hA t₁) ?_
  · simp only [List.append_assoc]
    refine ptrTo_ok hp h hS fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ hD₁ fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  refine Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃⟩ => ?_)
    (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃⟩ ⟨_, _, _, _, e₁', e₂', e₃'⟩ r hr => ?_) t₂
  · have fS : (S.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hS
    have fD : (D.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hD₁
    have dd := Buf.disj hp hS hD₁ dSD
    let I : Nat → State → Prop := fun k u => Ctx Y s₀ u ∧ u.gpr .edi = S.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ebp = D.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (n - k) ∧
      Frame [D.rgn s₀] s.mem u.mem ∧ ∀ j < 4 * k, u.mem (D.addr s₀ + BitVec.ofNat 64 j) = s.mem (S.addr s₀ + BitVec.ofNat 64 j)
    have i0 : I 0 s₁ := ⟨h₁, by rw [e₁]; simp, by rw [e₂]; simp, e₃, by rw [m₁]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    refine (wp_count hn I i0 fun k hk u ⟨cu, du, bu, xu, fu, cpu⟩ => ?_).mono fun u ⟨cu, _, _, _, fu, cpu⟩ => ?_
    · have eS : u.ea (at_ .edi 0) = S.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, du]; rw [ea_add (by omega)]; rfl
      have eD : u.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, bu]; rw [ea_add (by omega)]; rfl
      have hinS : InRegions (u.rd ++ u.wr) (S.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegR hp hS cu.rd cu.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine wp_movm' (by rw [eS]; exact hinS) fun u₁ o₁ v₁ => ?_
      have c₁ := cu.only o₁ (by decide) (by decide)
      have eD₁ : u₁.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        rw [← eD]; simp only [State.ea, at_, o₁.gpr _ (by decide : Reg.ebp ∉ [Reg.eax])]
      have hinD : InRegions u₁.wr (D.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegW hp hD₁ (Lay.okW_iff.mp hD).2 c₁.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine wp_store' (by rw [eD₁]; exact hinD) fun u₂ g₂ r₂ w₂ m₂ => ?_
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hD₁ (Lay.okW_iff.mp hD).2 (o := 4 * k) (n := 4)
        (show 4 * k + 4 ≤ 4 * n by omega)
      have c₂ : Ctx Y s₀ u₂ := ⟨by rw [g₂]; exact c₁.esp, by rw [r₂]; exact c₁.rd, by rw [w₂]; exact c₁.wr,
        by rw [g₂]; exact c₁.esi, by rw [m₂, eD₁]; exact c₁.frame.writeW hr _ hcr⟩
      refine wp_addi fun u₃ o₃ v₃ => wp_addi fun u₄ o₄ v₄ => wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
      have c₅ := ((c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)).only o₅ (by decide)
        (by decide)
      have m₅ : u₅.mem = u₁.mem.writeW (D.addr s₀ + BitVec.ofNat 64 (4 * k)) (u.mem.readW (S.addr s₀ +
          BitVec.ofNat 64 (4 * k)) 32) := by
        rw [o₅.mem, o₄.mem, o₃.mem, m₂, eD₁, v₁, eS]
      have ex : u₄.gpr .ecx = BitVec.ofNat 32 (n - k) := by
        rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), xu]
      refine ⟨⟨c₅, ?_, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_⟩, ?_⟩
      · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃, g₂, o₁.gpr _ (by decide), du]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [o₅.gpr _ (by decide), v₄, o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), bu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [m₅, o₁.mem]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨D.addr s₀, 4 * n⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      · intro j hj
        rw [m₅, o₁.mem, wordw_bytes (by omega) hj]
        split
        · rename_i e
          rw [← Mem.readW_byte _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
            show 4 * k + (j - 4 * k) = j by omega]
          exact fu.bytes (R := S.rgn s₀) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact dd) (by show 4 * n ≤ 2 ^ 64; omega)
            (show j < 4 * n by omega)
        · exact cpu j (by omega)
      · show u₅.zf.map (!·) = _
        rw [z₅, ex]; exact cnt_ne hk (by omega)
    · refine hQ s₀ s u hp ha cu fu ?_
      exact List.map_congr_left fun j hj => cpu j (List.mem_range.mp hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.ptr hS]
    · rw [e₂, e₂', hq.ptr hD₁]
    · rw [e₃, e₃']

/-! ## After `SampleNTT` -/

theorem maskA_piece (ao po : Nat)
    (hc : (Y.okW ⟨Y.sc, ao, 4⟩ && Y.okW ⟨Y.sc, po, 1024⟩ && Y.sep ⟨Y.sc, ao, 4⟩ ⟨Y.sc, po, 1024⟩) = true)
    {ht : Taint.Hint VG.X86.Taint.T} (tt : (VG.X86.taint.check (τr [.esi]) (maskA ao po) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨Y.sc, ao, 4⟩, Buf.rgn s₀ ⟨Y.sc, po, 1024⟩] s.mem s'.mem →
      s'.mem.readW (Buf.addr s₀ ⟨Y.sc, ao, 4⟩) 32 = s.mem.readW (Buf.addr s₀ ⟨Y.sc, ao, 4⟩) 32 &&& s.gpr .eax →
      (∀ i < 256, coeffAt s'.mem (Buf.addr s₀ ⟨Y.sc, po, 1024⟩) i =
        coeffAt s.mem (Buf.addr s₀ ⟨Y.sc, po, 1024⟩) i &&& (0 - s.gpr .eax)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (maskA ao po) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hC, hP⟩, dCP⟩ := hc'
  have hC₁ := (Lay.okW_iff.mp hC).1
  have hP₁ := (Lay.okW_iff.mp hP).1
  let C : Buf := ⟨Y.sc, ao, 4⟩
  let P : Buf := ⟨Y.sc, po, 1024⟩
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have dd := Buf.disj hp hC₁ hP₁ dCP
    have fP : (P.ptr s₀).toNat + 1024 ≤ 2 ^ 32 := Buf.fit hp hP₁
    have eC : ∀ u : State, u.gpr .esi = arg s₀ Y.sc → u.ea (at_ .esi ao) = C.addr s₀ := fun u e => by
      simp only [State.ea, at_, e]; rfl
    obtain ⟨rC, hrC, hcC⟩ := Buf.contains hp hC₁ (Lay.okW_iff.mp hC).2 (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcC
    have inC : InRegions (s.rd ++ s.wr) (C.addr s₀) 4 := by
      have := Buf.inRegR hp hC₁ h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have inCw : InRegions s.wr (C.addr s₀) 4 := by
      have := Buf.inRegW hp hC₁ (Lay.okW_iff.mp hC).2 h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine WP.seq (wp_movi fun s₁ o₁ v₁ => wp_subr fun s₂ o₂ v₂ => ?_)
    have c₂ := (h.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
    have inC₂ : InRegions (s₂.rd ++ s₂.wr) (C.addr s₀) 4 := by
      have := Buf.inRegR hp hC₁ c₂.rd c₂.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine wp_movm' (by rw [eC s₂ c₂.esi]; exact inC₂) fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine wp_andr fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_store' (by rw [eC s₄ c₄.esi, c₄.wr, ← h.wr]; exact inCw) fun s₅ g₅ r₅ w₅ m₅ => ?_
    have c₅ : Ctx Y s₀ s₅ := ⟨by rw [g₅]; exact c₄.esp, by rw [r₅]; exact c₄.rd, by rw [w₅]; exact c₄.wr,
      by rw [g₅]; exact c₄.esi, by rw [m₅, eC s₄ c₄.esi]; exact c₄.frame.writeW hrC _ hcC⟩
    refine wp_movr' fun s₆ o₆ v₆ => wp_addi fun s₇ o₇ v₇ => wp_movi fun s₈ o₈ v₈ => WP.block_nil_iff.mpr ?_
    have c₈ := ((c₅.only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)).only o₈ (by decide)
      (by decide)
    -- the state after the first block
    have rE : s₈.gpr .edx = 0 - s.gpr .eax := by
      rw [o₈.gpr _ (by decide), o₇.gpr _ (by decide), o₆.gpr _ (by decide), g₅, o₄.gpr _ (by decide),
        o₃.gpr _ (by decide), v₂, v₁, o₁.gpr _ (by decide)]
    have m₈ : s₈.mem = s.mem.writeW (C.addr s₀) (s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax) := by
      rw [o₈.mem, o₇.mem, o₆.mem, m₅, eC s₄ c₄.esi, v₄, v₃, eC s₂ c₂.esi, o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), o₁.gpr _ (by decide), o₄.mem, o₃.mem, o₂.mem, o₁.mem]
    have fC : Frame [C.rgn s₀] s.mem s₈.mem := by
      rw [m₈]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have cP : ∀ i < 256, coeffAt s₈.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i := fun i hi =>
      Frame.readW fC (coeff_contains _ (show i < n by rw [n_eq]; exact hi)) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact dd.symm) (by decide)
    have aC : s₈.mem.readW (C.addr s₀) 32 = s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax := by
      rw [m₈]; exact Mem.readW_writeW_self32 _ _ _
    let I : Nat → State → Prop := fun k u => Ctx Y s₀ u ∧ u.gpr .edi = P.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ecx = BitVec.ofNat 32 (256 - k) ∧ u.gpr .edx = 0 - s.gpr .eax ∧
      Frame [C.rgn s₀, P.rgn s₀] s.mem u.mem ∧ u.mem.readW (C.addr s₀) 32 = s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax ∧
      (∀ i < k, coeffAt u.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i &&& (0 - s.gpr .eax)) ∧
      (∀ i, k ≤ i → i < 256 → coeffAt u.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i)
    have i0 : I 0 s₈ := ⟨c₈, by rw [o₈.gpr _ (by decide), v₇, v₆, g₅, c₄.esi]; simp; rfl,
      v₈, rE, fC.mono (by simp), aC, fun i hi => absurd hi (by omega), fun i _ hi => cP i hi⟩
    refine (wp_count (N := 256) (by decide) I i0 fun k hk u ⟨cu, du, xu, eu, fu, au, lo, hi⟩ => ?_).mono
      fun u ⟨cu, _, _, _, fu, au, lo, _⟩ => hQ s₀ s u hp ha cu fu au lo
    have eP : u.ea (at_ .edi 0) = coeffAddr (P.addr s₀) k := by
      simp only [State.ea, at_, du]; rw [ea_add (by omega)]; rfl
    have hk' : k < n := by rw [n_eq]; exact hk
    have inP : InRegions u.wr (coeffAddr (P.addr s₀) k) 4 :=
      Buf.inRegW hp hP₁ (Lay.okW_iff.mp hP).2 cu.wr (show 4 * k + 4 ≤ 1024 by omega)
    obtain ⟨rP, hrP, hcP⟩ := Buf.contains hp hP₁ (Lay.okW_iff.mp hP).2 (o := 4 * k) (n := 4)
      (show 4 * k + 4 ≤ 1024 by omega)
    have inP' : InRegions (u.rd ++ u.wr) (coeffAddr (P.addr s₀) k) 4 :=
      Buf.inRegR hp hP₁ cu.rd cu.wr (show 4 * k + 4 ≤ 1024 by omega)
    refine wp_movm' (by rw [eP]; exact inP') fun u₁ o₁ v₁ => ?_
    have c₁ := cu.only o₁ (by decide) (by decide)
    refine wp_andr fun u₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    have eP₂ : u₂.ea (at_ .edi 0) = coeffAddr (P.addr s₀) k := by
      rw [← eP]; simp only [State.ea, at_]; rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide)]
    refine wp_store' (by rw [eP₂, c₂.wr, ← cu.wr]; exact inP) fun u₃ g₃ r₃ w₃ m₃ => ?_
    have c₃ : Ctx Y s₀ u₃ := ⟨by rw [g₃]; exact c₂.esp, by rw [r₃]; exact c₂.rd, by rw [w₃]; exact c₂.wr,
      by rw [g₃]; exact c₂.esi, by rw [m₃, eP₂]; exact c₂.frame.writeW hrP _ hcP⟩
    refine wp_addi fun u₄ o₄ v₄ => wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
    have c₅ := (c₃.only o₄ (by decide) (by decide)).only o₅ (by decide) (by decide)
    have val : u₂.gpr .eax = coeffAt s.mem (P.addr s₀) k &&& (0 - s.gpr .eax) := by
      rw [v₂, v₁, o₁.gpr _ (by decide), eu, eP, ← coeffAt_eq, hi k (Nat.le_refl _) hk]
    have m₅ : u₅.mem = u.mem.writeW (coeffAddr (P.addr s₀) k) (coeffAt s.mem (P.addr s₀) k &&& (0 - s.gpr .eax)) := by
      rw [o₅.mem, o₄.mem, m₃, eP₂, val, o₂.mem, o₁.mem]
    have ex : u₄.gpr .ecx = BitVec.ofNat 32 (256 - k) := by
      rw [o₄.gpr _ (by decide), g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), xu]
    refine ⟨⟨c₅, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_, ?_, fun i hi' => ?_, fun i hi₁ hi₂ => ?_⟩, ?_⟩
    · rw [o₅.gpr _ (by decide), v₄, g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), du]
      show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), eu]
    · rw [m₅]; exact fu.writeW (r := P.rgn s₀) (by simp) _ (coeff_contains _ hk')
    · rw [m₅, Mem.readW_writeW_sep (dd.sep (Region.contains_self _ _) (coeff_contains _ hk')) (by decide)]
      exact au
    · rw [m₅, coeffAt_writeW _ _ (by rw [n_eq]; omega) hk']
      split
      · rename_i e; subst e; rfl
      · exact lo i (by omega)
    · rw [m₅, coeffAt_writeW_ne _ _ (by rw [n_eq]; omega) hk' (by omega)]
      exact hi i (by omega) hi₂
    · show u₅.zf.map (!·) = _
      rw [z₅, ex]; exact cnt_ne hk (by decide)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## `esi`, a word, and the value returned -/

/-- `esi ← scratch`, at the start of the body. -/
theorem ldsc_piece {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * Y.sc)))]) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) (Ctx Y) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * Y.sc)))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) tt
  · subst e
    have ea : (P0 s₀).ea (at_ .esp (20 + 4 * Y.sc)) = argAddr s₀ Y.sc := P0_argAddr s₀ Y.sc
    refine wp_movm' (by rw [ea]; exact P0_argIn hp.sc_lt hp.sp' hp.gwr) fun s₁ o₁ v₁ => WP.block_nil_iff.mpr ?_
    refine ⟨by rw [o₁.gpr _ (by decide)], o₁.rd, o₁.wr, ?_, by rw [o₁.mem]; exact Frame.refl _ _⟩
    rw [v₁, ea]
    exact P0_arg hp.E0_big hp.sc_lt hp.sp' (by rw [hp.fr16]; exact hp.stk_g.sub_left hp.frame_sub)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-- A word of `scratch` set to `v`. -/
theorem st32_piece (o v : Nat) (hc : Y.okW ⟨Y.sc, o, 4⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (at_ .esi o) .eax])
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) (BitVec.ofNat 32 v) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (at_ .esi o) .eax]) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    have hin : InRegions s.wr (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 4 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine wp_movi fun s₁ o₁ v₁ => ?_
    have h₁ := h.only o₁ (by decide) (by decide)
    have ea₁ : s₁.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 4⟩ := by
      simp only [State.ea, at_]; rw [h₁.esi]
    refine wp_store' (by rw [ea₁, h₁.wr, ← h.wr]; exact hin) fun s₂ g₂ r₂ w₂ m₂ => WP.block_nil_iff.mpr ?_
    refine hQ s₀ s _ hp ha ⟨by rw [g₂]; exact h₁.esp, by rw [r₂]; exact h₁.rd, by rw [w₂]; exact h₁.wr,
      by rw [g₂]; exact h₁.esi, ?_⟩ ?_
    · rw [m₂, ea₁]; exact h₁.frame.writeW hr _ hcr
    · rw [m₂, ea₁, o₁.mem, v₁]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-- `eax ←` a word of `scratch`. -/
theorem ld32_piece (o : Nat) (hc : Y.ok ⟨Y.sc, o, 4⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.mem (at_ .esi o))]) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → s'.mem = s.mem →
      s'.gpr .eax = s.mem.readW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 32 → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.mov .eax (.mem (at_ .esi o))]) := by
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have hin : InRegions (s.rd ++ s.wr) (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 4 := by
      have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have ea : s.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 4⟩ := by simp only [State.ea, at_]; rw [h.esi]
    refine wp_movm' (by rw [ea]; exact hin) fun s₁ o₁ v₁ => WP.block_nil_iff.mpr ?_
    exact hQ s₀ s s₁ hp ha (h.only o₁ (by decide) (by decide)) o₁.mem (by rw [v₁, ea])
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

end VG.Proof.MlKem.X86.Top
