import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateCopy

/-!
# Streaming RC2-CBC on x86 (32-bit): the copies before CBC

With `out_len ≠ 0`: the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, and the rest of the data to the pending block
(`long_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem sub_eq' (x y : BitVec 32) (h : y.toNat ≤ x.toNat) : x - y = BitVec.ofNat 32 (x.toNat - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem sub_add_eq (x y z : BitVec 32) (h : y.toNat ≤ z.toNat + x.toNat) :
    x - y + z = BitVec.ofNat 32 (z.toNat + x.toNat - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt; have := y.isLt; have := z.isLt
  omega

section
variable {s₀ s : State} (hp : Pre s₀) (hc : Common s₀ s) {Q : State → Prop}
include hp hc

theorem toOut₁_ok
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .esi = ctx s₀ → t.gpr .edx = op s₀ →
      t.gpr .ecx = BitVec.ofNat 32 (p s₀) → Q t) :
    WP isa (.block toOut₁) s Q := by
  refine wp_arg hp hc (i := 0) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 4) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_
  exact hQ s₃ (c₂.upd u₃ (by decide) (by decide) (by decide)) (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.gpr, ofNat_toNat])

theorem toOut₂_ok (hpO : p s₀ ≤ O s₀)
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .esi = dp s₀ → t.gpr .edx = s.gpr .edx →
      t.gpr .ecx = BitVec.ofNat 32 (O s₀ - p s₀) → Q t) :
    WP isa (.block toOut₂) s Q := by
  refine wp_arg hp hc (i := 2) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 5) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_sub fun s₄ u₄ _ => WP.block_nil ?_
  refine hQ s₄ (c₃.upd u₄ (by decide) (by decide) (by decide)) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]) ?_
  rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr]
  exact sub_eq' _ _ hpO

theorem toPending_ok (hle : O s₀ ≤ p s₀ + len s₀)
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .esi = s.gpr .esi → t.gpr .edx = ctx s₀ →
      t.gpr .ecx = BitVec.ofNat 32 (p s₀ + len s₀ - O s₀) → Q t) :
    WP isa (.block toPending) s Q := by
  refine wp_arg hp hc (i := 0) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 3) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 5) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_sub fun s₄ u₄ _ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine wp_arg hp c₄ (i := 1) (by decide) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_add fun s₆ u₆ _ => WP.block_nil ?_
  refine hQ s₆ (c₅.upd u₆ (by decide) (by decide) (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]) ?_
  rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr]
  exact sub_add_eq _ _ _ hle

end

theorem long_ok {s₀ s : State} (hp : Pre s₀) (hO : O s₀ ≠ 0) (hc : Common s₀ s)
    (hf : Frame [scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' →
      Spec.Rc2.bytesAt s'.mem (oA s₀) (O s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀) →
      Spec.Rc2.bytesAt s'.mem (cA s₀ + BitVec.ofNat 64 136) ((p s₀ + len s₀) % 8) =
        Spec.Rc2.bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀)) ((p s₀ + len s₀) % 8) → Q s') :
    WP isa long s Q := by
  have hOe := hp.O_eq
  have hpl := hp.p_lt
  have hpO : p s₀ ≤ O s₀ := by omega
  have hOL : O s₀ - p s₀ ≤ len s₀ := by omega
  have hR : p s₀ + len s₀ - O s₀ = (p s₀ + len s₀) % 8 := by omega
  have hRlt : (p s₀ + len s₀) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hcf := hp.c_fit
  have hdf := hp.d_fit
  have hof := hp.o_fit
  have hlen : len s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  have hC : addr (ctx s₀) 136 = cA s₀ + BitVec.ofNat 64 136 := addr_eq (by omega)
  have hS : addr (dp s₀) 0 = dA s₀ := by
    rw [addr_eq (by have := (dp s₀).isLt; omega)]; exact BitVec.add_zero _
  have hO0 : addr (op s₀) 0 = oA s₀ := by
    rw [addr_eq (by have := (op s₀).isLt; omega)]; exact BitVec.add_zero _
  have hOp : addr (op s₀ + BitVec.ofNat 32 (p s₀)) 0 = oA s₀ + BitVec.ofNat 64 (p s₀) := by
    rw [addr_add (by omega), Nat.add_zero]
  have hSp (h0 : 0 < (p s₀ + len s₀) % 8) :
      addr (dp s₀ + BitVec.ofNat 32 (O s₀ - p s₀)) 0 = dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀) := by
    rw [addr_add (by omega), Nat.add_zero]
  have inR {a : Addr} {n : Nat} {R : Region} (hR : R ∈ s₀.rd ++ s₀.wr) (hs : Region.Sub ⟨a, n⟩ R)
      (hn : n < 2 ^ 64) {t : State} (hc : Common s₀ t) :
      ∀ i < n, InRegions (t.rd ++ t.wr) (a + BitVec.ofNat 64 i) 1 := by
    rw [hc.rd, hc.wr]; exact inBytes hR hs hn
  have outR {a : Addr} {n : Nat} {R : Region} (hR : R ∈ s₀.wr) (hs : Region.Sub ⟨a, n⟩ R)
      (hn : n < 2 ^ 64) {t : State} (hc : Common s₀ t) : ∀ i < n, InRegions t.wr (a + BitVec.ofNat 64 i) 1 := by
    rw [hc.wr]; exact inBytes hR hs hn
  have ctxIn : ctxR s₀ ∈ s₀.wr := by simp [hp.wr]
  have oIn : oR s₀ ∈ s₀.wr := by simp [hp.wr]
  have ctxIn' : ctxR s₀ ∈ s₀.rd ++ s₀.wr := List.mem_append_right _ ctxIn
  have dIn : dR s₀ ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by simp [hp.rd])
  have pendSrc : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 136, p s₀⟩ (pendR s₀) := Region.sub_prefix (by omega)
  have pendDst : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 136, (p s₀ + len s₀) % 8⟩ (pendR s₀) :=
    Region.sub_prefix (by omega)
  have outA : Region.Sub ⟨oA s₀, p s₀⟩ (oR s₀) := Region.sub_prefix hpO
  have outB : Region.Sub ⟨oA s₀ + BitVec.ofNat 64 (p s₀), O s₀ - p s₀⟩ (oR s₀) :=
    Offset.sub_base _ (by omega)
  have datA : Region.Sub ⟨dA s₀, O s₀ - p s₀⟩ (dR s₀) := Region.sub_prefix hOL
  have datB : Region.Sub ⟨dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀), (p s₀ + len s₀) % 8⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  have pc {r : Region} (h : Region.Sub r (pendR s₀)) : Region.Sub r (ctxR s₀) :=
    fun a ha => Pre.pend_sub a (h a ha)
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  -- The pending bytes to `out`.
  refine WP.seq (toOut₁_ok hp hc fun s₁ c₁ mem₁ esi₁ edx₁ ecx₁ => ?_)
  refine WP.seq (copy_ok (sd := 136) (dd := 0) (n := p s₀) (S := ctx s₀) (D := op s₀) (by omega)
    (by omega) (by omega)
    (by rw [hC]; exact inR ctxIn' (pc pendSrc) (by omega) c₁)
    (by rw [hO0]; exact outR oIn outA (by omega) c₁)
    (by rw [hC, hO0]; exact (hp.c_o.sub_left (pc pendSrc)).sub_right outA)
    esi₁ edx₁ ecx₁ fun s₂ k₂ => ?_)
  have c₂ := c₁.copy hp k₂ (.inr (by rw [hO0]; exact outA))
  have f₂ := copy_frame k₂
  have b₂ := copy_bytes k₂ (by omega)
  rw [hO0] at f₂ b₂
  rw [hC, mem₁] at b₂
  -- The first `out_len - pending_len` bytes of data after them.
  refine WP.seq (toOut₂_ok hp c₂ hpO fun s₃ c₃ mem₃ esi₃ edx₃ ecx₃ => ?_)
  rw [k₂.edx] at edx₃
  refine WP.seq (copy_ok (sd := 0) (dd := 0) (n := O s₀ - p s₀) (S := dp s₀)
    (D := op s₀ + BitVec.ofNat 32 (p s₀)) (by omega) (by omega)
    (by rw [toNat_add_ofNat (by omega)]; omega)
    (by rw [hS]; exact inR dIn datA (by omega) c₃)
    (by rw [hOp]; exact outR oIn outB (by omega) c₃)
    (by rw [hS, hOp]; exact (hp.d_o.sub_left datA).sub_right outB)
    esi₃ edx₃ ecx₃ fun s₄ k₄ => ?_)
  have c₄ := c₃.copy hp k₄ (.inr (by rw [hOp]; exact outB))
  have f₄ := copy_frame k₄
  have b₄ := copy_bytes k₄ (by omega)
  rw [hOp] at f₄ b₄
  rw [hS, mem₃] at b₄
  -- The rest to the pending block.
  refine WP.seq (toPending_ok hp c₄ (by omega) fun s₅ c₅ mem₅ esi₅ edx₅ ecx₅ => ?_)
  rw [k₄.esi] at esi₅
  rw [hR] at ecx₅
  refine copy_ok (sd := 0) (dd := 136) (n := (p s₀ + len s₀) % 8)
    (S := dp s₀ + BitVec.ofNat 32 (O s₀ - p s₀)) (D := ctx s₀) (by omega)
    (by
      rcases Nat.eq_zero_or_pos ((p s₀ + len s₀) % 8) with h0 | h0
      · have := (dp s₀ + BitVec.ofNat 32 (O s₀ - p s₀)).isLt; omega
      · rw [toNat_add_ofNat (by omega)]; omega) (by omega)
    (fun i hi => by rw [hSp (by omega)]; exact inR dIn datB (by omega) c₅ i hi)
    (by rw [hC]; exact outR ctxIn (pc pendDst) (by omega) c₅)
    (by
      rcases Nat.eq_zero_or_pos ((p s₀ + len s₀) % 8) with h0 | h0
      · intro a h; simp only [Region.Contains, h0] at h; omega
      · rw [hSp h0, hC]; exact (hp.c_d.symm.sub_left datB).sub_right (pc pendDst))
    esi₅ edx₅ ecx₅ fun s₆ k₆ => ?_
  have c₆ := c₅.copy hp k₆ (.inl (by rw [hC]; exact pendDst))
  have f₆ := copy_frame k₆
  have b₆ := copy_bytes k₆ (by omega)
  rw [hC] at f₆ b₆
  rw [mem₅] at b₆
  rw [mem₅] at f₆
  rw [mem₃] at f₄
  rw [mem₁] at f₂
  refine hQ s₆ c₆ ?_ ?_
  · -- `out`: the pending bytes, then the data.
    have hsplit : Spec.Rc2.bytesAt s₆.mem (oA s₀) (O s₀) = Spec.Rc2.bytesAt s₆.mem (oA s₀) (p s₀) ++
        Spec.Rc2.bytesAt s₆.mem (oA s₀ + BitVec.ofNat 64 (p s₀)) (O s₀ - p s₀) := by
      rw [← Proof.Rc2.bytesAt_add, Nat.add_sub_cancel' hpO]
    have e₁ : Spec.Rc2.bytesAt s₆.mem (oA s₀) (p s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) := by
      rw [Proof.Rc2.bytesAt_frame f₆ _ _ (by omega) (sing ((hp.c_o.sub_left (pc pendDst)).sub_right outA).symm),
        Proof.Rc2.bytesAt_frame f₄ _ _ (by omega) (sing (Offset.base_disjoint _ (by omega) (by omega))), b₂,
        Proof.Rc2.bytesAt_frame hf _ _ (by omega) (sing (hp.c_s.sub_left (pc pendSrc)))]
    have e₂ : Spec.Rc2.bytesAt s₆.mem (oA s₀ + BitVec.ofNat 64 (p s₀)) (O s₀ - p s₀) =
        Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀) := by
      rw [Proof.Rc2.bytesAt_frame f₆ _ _ (by omega) (sing ((hp.c_o.sub_left (pc pendDst)).sub_right outB).symm),
        b₄, Proof.Rc2.bytesAt_frame f₂ _ _ (by omega) (sing ((hp.d_o.sub_left datA).sub_right outA)),
        Proof.Rc2.bytesAt_frame hf _ _ (by omega) (sing (hp.d_s.sub_left datA))]
    rw [hsplit, e₁, e₂]
  · -- The pending block: the rest of the data.
    rcases Nat.eq_zero_or_pos ((p s₀ + len s₀) % 8) with h0 | h0
    · rw [h0]; rfl
    rw [b₆, hSp h0, Proof.Rc2.bytesAt_frame f₄ _ _ (by omega) (sing ((hp.d_o.sub_left datB).sub_right outB)),
      Proof.Rc2.bytesAt_frame f₂ _ _ (by omega) (sing ((hp.d_o.sub_left datB).sub_right outA)),
      Proof.Rc2.bytesAt_frame hf _ _ (by omega) (sing (hp.d_s.sub_left datB))]

end VG.Proof.Rc2.X86.Stream.Update
