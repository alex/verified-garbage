import VerifiedGarbage.Proof.Rc2.X86.Stream.InitPre

/-!
# Streaming RC2-CBC on x86 (32-bit): the IV and the key expansion's arguments

Untrusted: everything here is checked by Lean. With valid lengths, `init`
copies the IV to `ctx + 128`, saves our caller's `ebx` and `esi` in
`scratch[512..520)`, and loads the arguments of `vg_rc2_expand_key`
(`initArgs_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

/-- `Common` after a store within the chaining value or the scratch space. -/
theorem Common.store {s₀ s s' : State} (h : Common s₀ s) {a : Addr} {v : BitVec 32}
    (u : Mupd s s' (s.mem.writeW a v)) {r : Region} (hr : r ∈ [cvR s₀, scR s₀]) (ha : r.Contains a 4) :
    Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame.writeW hr _ ha⟩

theorem initArgs_ok {s₀ s : State} (hp : Pre s₀) (hi : il s₀ = 8) (hc : Common s₀ s) (hm : s.mem = s₀.mem)
    (hb : s.gpr .ebx = s₀.gpr .ebx) (hs : s.gpr .esi = s₀.gpr .esi) {Q : State → Prop}
    (hQ : ∀ t, Common s₀ t → t.gpr .eax = key s₀ → t.gpr .ecx = arg s₀ 1 → t.gpr .edx = arg s₀ 2 →
      t.gpr .esi = ctx s₀ → t.gpr .ebx = scr s₀ →
      Spec.Rc2.blockAt t.mem (cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (ivA s₀) →
      t.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx → t.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi →
      Q t) :
    WP isa (.block initArgs) s Q := by
  have hif := hp.i_fit
  have hcf := hp.c_fit
  have iv4 : addr (iv s₀) 4 = ivA s₀ + BitVec.ofNat 64 4 := addr_eq (by omega)
  have c128 : addr (ctx s₀) 128 = cA s₀ + BitVec.ofNat 64 128 := hp.ctx_addr (by decide)
  have c132 : addr (ctx s₀) 132 = cA s₀ + BitVec.ofNat 64 132 := hp.ctx_addr (by decide)
  have ivIn₀ : InRegions (s₀.rd ++ s₀.wr) (addr (iv s₀) 0) 4 := by
    rw [addr_eq (by have := (iv s₀).isLt; omega)]
    exact ⟨ivR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  have ivIn₄ : InRegions (s₀.rd ++ s₀.wr) (addr (iv s₀) 4) 4 := by
    rw [iv4]; exact ⟨ivR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  have iv0 : addr (iv s₀) 0 = ivA s₀ := by
    rw [addr_eq (by have := (iv s₀).isLt; omega)]; exact BitVec.add_zero _
  have cvC (d : Nat) (hd : 128 ≤ d) (hd' : d + 4 ≤ 136) : (cvR s₀).Contains (cA s₀ + BitVec.ofNat 64 d) 4 :=
    Offset.contains _ hd (by omega) (by omega)
  have cvIn (d : Nat) (hd : 128 ≤ d) (hd' : d + 4 ≤ 136) : InRegions s₀.wr (cA s₀ + BitVec.ofNat 64 d) 4 :=
    ⟨ctxR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  have scC (d : Nat) (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) 4 := by
    rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega)
  have scIn (d : Nat) (hd : d + 4 ≤ 576) : InRegions s₀.wr (addr (scr s₀) d) 4 :=
    ⟨scR s₀, by simp [hp.wr], scC d hd⟩
  simp only [initArgs, save, List.cons_append, List.nil_append]
  refine wp_arg hp hc (i := 3) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 5) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  have eax₂ : s₂.gpr .eax = iv s₀ := by rw [u₂.other _ (by decide)]; exact u₁.gpr
  refine wp_ldm (o := 0) eax₂ (by rw [c₂.rd, c₂.wr]; exact ivIn₀) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_stm (o := 128) (B := ctx s₀) (by rw [u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₃.wr, c₂.wr, c128]; exact cvIn 128 (by decide) (by decide)) fun s₄ u₄ => ?_
  have c₄ := c₃.store u₄ (r := cvR s₀) (by simp) (by rw [c128]; exact cvC 128 (by decide) (by decide))
  refine wp_ldm (o := 4) (B := iv s₀) (by rw [u₄.gpr, u₃.other _ (by decide)]; exact eax₂)
    (by rw [c₄.rd, c₄.wr]; exact ivIn₄) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_stm (o := 132) (B := ctx s₀) (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₅.wr, c₄.wr, c132]; exact cvIn 132 (by decide) (by decide)) fun s₆ u₆ => ?_
  have c₆ := c₅.store u₆ (r := cvR s₀) (by simp) (by rw [c132]; exact cvC 132 (by decide) (by decide))
  -- The chaining value.
  have m₆ : s₆.mem = s₀.mem.writeW (cA s₀ + BitVec.ofNat 64 128) (s₀.mem.readW (ivA s₀) 64) := by
    have r₄ : s₄.mem.readW (ivA s₀ + BitVec.ofNat 64 4) 32 = s₀.mem.readW (ivA s₀ + BitVec.ofNat 64 4) 32 := by
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hm, c128]
      refine Mem.readW_writeW_sep (Region.Disjoint.sep (hp.i_c.sub_right cv_sub) ?_ ?_) (by decide)
      · exact Offset.contains_base _ (by omega) (by omega)
      · exact contains_prefix _ (by decide)
    have m₄ : s₄.mem = s₀.mem.writeW (cA s₀ + BitVec.ofNat 64 128) (s₀.mem.readW (ivA s₀) 32) := by
      rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, hm, iv0, c128]
    rw [u₆.mem, u₅.gpr, u₅.mem, iv4, r₄, c132, m₄,
      show cA s₀ + BitVec.ofNat 64 132 = cA s₀ + BitVec.ofNat 64 128 + BitVec.ofNat 64 4 by
        rw [Offset.add_add],
      ← Word32.write64_pair, ← Word32.read64_pair]
  have cv₆ : Spec.Rc2.blockAt s₆.mem (cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (ivA s₀) := by
    rw [m₆, blockAt_copy]
  -- Our caller's registers.
  refine wp_arg hp c₆ (i := 6) (by decide) fun s₇ u₇ => ?_
  have c₇ := c₆.upd u₇ (by decide) (by decide) (by decide)
  have g₇ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) (h₃ : r ≠ .edx) : s₇.gpr r = s.gpr r := by
    rw [u₇.other _ h₁, u₆.gpr, u₅.other _ h₃, u₄.gpr, u₃.other _ h₃, u₂.other _ h₂, u₁.other _ h₁]
  refine wp_stm (o := 512) (B := scr s₀) u₇.gpr (by rw [u₇.wr, c₆.wr]; exact scIn 512 (by decide)) fun s₈ u₈ => ?_
  have c₈ := c₇.store u₈ (r := scR s₀) (by simp) (scC 512 (by decide))
  refine wp_stm (o := 516) (B := scr s₀) (by rw [u₈.gpr]; exact u₇.gpr) (by rw [u₈.wr, c₇.wr]; exact scIn 516 (by decide))
    fun s₉ u₉ => ?_
  have c₉ := c₈.store u₉ (r := scR s₀) (by simp) (scC 516 (by decide))
  have m₉ : s₉.mem = (s₇.mem.writeW (addr (scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₉.mem, u₈.mem, u₈.gpr, g₇ _ (by decide) (by decide) (by decide),
      g₇ _ (by decide) (by decide) (by decide), hb, hs]
  have f₉ : Frame [scR s₀] s₇.mem s₉.mem := by
    rw [m₉]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (scC 512 (by decide))).writeW
      (List.mem_singleton_self _) _ (scC 516 (by decide))
  have cv₉ : Spec.Rc2.blockAt s₉.mem (cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (ivA s₀) := by
    rw [Proof.Rc2.blockAt_frame f₉ _ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_s.sub_left cv_sub), u₇.mem]
    exact cv₆
  have w₁ : s₉.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx := by
    rw [m₉, Mem.readW_writeW_sep _ (by decide), Mem.readW_writeW_self32]
    rw [hp.scr_addr (d := 512) (by decide), hp.scr_addr (d := 516) (by decide)]
    exact Offset.sep _ (by decide) (by decide) (by decide)
  have w₂ : s₉.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi := by rw [m₉, Mem.readW_writeW_self32]
  -- The arguments.
  refine wp_mov fun s₁₀ u₁₀ => ?_
  have c₁₀ := c₉.upd u₁₀ (by decide) (by decide) (by decide)
  refine wp_mov fun s₁₁ u₁₁ => ?_
  have c₁₁ := c₁₀.upd u₁₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁₁ (i := 2) (by decide) fun s₁₂ u₁₂ => ?_
  have c₁₂ := c₁₁.upd u₁₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁₂ (i := 1) (by decide) fun s₁₃ u₁₃ => ?_
  have c₁₃ := c₁₂.upd u₁₃ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁₃ (i := 0) (by decide) fun s₁₄ u₁₄ => WP.block_nil ?_
  have mem : s₁₄.mem = s₉.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  refine hQ s₁₄ (c₁₃.upd u₁₄ (by decide) (by decide) (by decide)) u₁₄.gpr
    (by rw [u₁₄.other _ (by decide), u₁₃.gpr])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.gpr, u₈.gpr]; exact u₇.gpr)
    (by rw [mem]; exact cv₉) (by rw [mem]; exact w₁) (by rw [mem]; exact w₂)

end VG.Proof.Rc2.X86.Stream.Init
