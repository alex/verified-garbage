import VerifiedGarbage.Proof.MlKem.X86_64.FragS
import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-!
# ML-KEM on x86-64: four entries of the matrix at once

Untrusted: everything here is checked by Lean. In a layout: the seed
`ρ ‖ j ‖ i` of an entry, with `ρ` at `SB`, to `34 k` bytes into `scratch`
(`seedAt_ok`), and the four seeds of entries `e₀, …, e₀ + 3` of a matrix of
`n` columns (`SeedsIs`); then `vg_mlkem_sample_ntt4`, of any implementation
(`Sample4Impl`), of those seeds to the four polynomials from `a`
(`sample4At_ok`), which changes `r15` (so what it leaves is `PostB`), and
the whole (`quad_ok`), and its constant time for a given `ρ` (`quad_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {rbs wbs : List (Reg × Nat)}

/-! ## A seed -/

theorem rbx_ne_rax : Reg.rbx ≠ .rax := by decide

/-- What seed `k` writes. -/
abbrev seedW (k : Nat) : List (Ptr × Nat) :=
  [(sc (34 * k), 32)] ++ ([(sc (34 * k + 32), 1)] ++ [(sc (34 * k + 33), 1)])

/-- The copy of `ρ` and the two bytes of seed `k`. -/
def seedChk (bs wbs : List (Reg × Nat)) (k : Nat) : Bool :=
  copyChk bs wbs (sc (34 * k)) (sc oSB) 32 && inB wbs (sc (34 * k + 32)) 1 && inB wbs (sc (34 * k + 33)) 1 &&
    keepB bs [(sc (34 * k + 32), 1)] (sc (34 * k)) 32 && keepB bs [(sc (34 * k + 33), 1)] (sc (34 * k)) 32 &&
    keepB bs [(sc (34 * k + 33), 1)] (sc (34 * k + 32)) 1

theorem seedAt_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {k i j : Nat}
    (hi : i < 256) (hj : j < 256) (hc : seedChk (rbs ++ wbs) wbs k = true) :
    WP isa (seedAt k i j) s fun s' => PPost s s' (seedW k) ∧
      bytesAt s'.mem (pa s' (sc (34 * k))) 34 = matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j := by
  simp only [seedChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hcp, h32⟩, h33⟩, k1⟩, k2⟩, k3⟩ := hc
  unfold seedAt
  refine WP.seq (WP.mono (copy_okL L (by decide) hcp) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  rw [WP.block_append_iff]
  refine WP.mono (setB_okL L₁ rbx_ne_rax hj h32) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have L₂ := L₁.post hP₂.b hcs
  refine WP.mono (setB_okL L₂ rbx_ne_rax hi h33) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have e2 : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun o => hP₂.pa rbx_cs
  have e3 : ∀ o, pa s₃ (sc o) = pa s₂ (sc o) := fun o => hP₃.pa rbx_cs
  have hρ : bytesAt s₃.mem (pa s₃ (sc (34 * k))) 32 = bytesAt s.mem (pa s (sc oSB)) 32 := by
    rw [L₂.keepBytes hP₃.b k2, L₁.keepBytes hP₂.b k1, show pa s₁ (sc (34 * k)) = pa s (sc (34 * k)) from hP₁.pa rbx_cs,
      hb₁]
  have hjb : bytesAt s₃.mem (pa s₃ (sc (34 * k + 32))) 1 = [BitVec.ofNat 8 j] := by
    rw [L₂.keepBytes hP₃.b k3, e2]; exact hb₂
  have hib : bytesAt s₃.mem (pa s₃ (sc (34 * k + 33))) 1 = [BitVec.ofNat 8 i] := by
    rw [e3]; exact hb₃
  refine ⟨PPost.app hP₁ (PPost.app hP₂ hP₃ fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact rbx_cs)
    (fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw; rcases hw with rfl | rfl <;> exact rbx_cs),
    seed_eq hρ ?_ ?_⟩
  · rw [← hjb, pa, pa, off_add]
  · rw [← hib, pa, pa, off_add]

/-- `ρ` at `SB`, and the seeds of entries `e₀, …, e₀ + K - 1` of a matrix
of `n` columns, from `scratch`. -/
structure SeedsIs (ρ : List Byte) (n e₀ K : Nat) (s : State) : Prop where
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ
  seeds : ∀ k < K, bytesAt s.mem (pa s (sc (34 * k))) 34 = matSeed ρ ((e₀ + k) / n) ((e₀ + k) % n)

/-- Seed `K`, keeping `ρ` and the seeds before it. -/
def seedsChk (bs wbs : List (Reg × Nat)) (K : Nat) : Bool :=
  seedChk bs wbs K && keepB bs (seedW K) (sc oSB) 32 &&
    (List.range K).all fun k => keepB bs (seedW K) (sc (34 * k)) 34

theorem seed_step {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte}
    {n e₀ K : Nat} (he : e₀ + K < 256) (hc : seedsChk (rbs ++ wbs) wbs K = true) (h : SeedsIs ρ n e₀ K s) :
    WP isa (seedAt K ((e₀ + K) / n) ((e₀ + K) % n)) s fun s' =>
      PPost s s' (seedW K) ∧ SeedsIs ρ n e₀ (K + 1) s' := by
  simp only [seedsChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hs, kB⟩, kS⟩ := hc
  refine WP.mono (seedAt_ok L hcs (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) he)
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) he) hs) fun s' ⟨hP, hb⟩ => ⟨hP, ?_, fun k hk => ?_⟩
  · rw [L.keepBytes hP.b kB]; exact h.sb
  · rcases (by omega : k < K ∨ k = K) with hk | rfl
    · rw [L.keepBytes hP.b (kS k hk)]; exact h.seeds k hk
    · rw [hb, h.sb]

/-! ## The call -/

/-- The seeds, the four polynomials from `sc oa` and the working space at `sc oz`. -/
def s4Chk (bs wbs : List (Reg × Nat)) (oa oz : Nat) : Bool :=
  rdOk bs (sc 0) 136 && wrOk bs wbs (sc oa) 4096 && wrOk bs wbs (sc oz) 8192 && sepB bs (sc 0) 136 (sc oa) 4096 &&
    sepB bs (sc 0) 136 (sc oz) 8192 && sepB bs (sc oa) 4096 (sc oz) 8192

/-- What a call of `vg_mlkem_sample_ntt4` of the seeds at `scratch` to `sc oa` needs. -/
structure S4H (oa oz : Nat) (s : State) : Prop where
  offA : oa < 2 ^ 31
  offZ : oz < 2 ^ 31
  dSA : Region.Disjoint ⟨pa s (sc 0), 136⟩ ⟨pa s (sc oa), 4096⟩
  dSZ : Region.Disjoint ⟨pa s (sc 0), 136⟩ ⟨pa s (sc oz), 8192⟩
  dAZ : Region.Disjoint ⟨pa s (sc oa), 4096⟩ ⟨pa s (sc oz), 8192⟩
  kS : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 136⟩
  kA : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oa), 4096⟩
  kZ : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oz), 8192⟩
  nwA : (pa s (sc oa)).toNat + 4096 ≤ 2 ^ 64
  nwZ : (pa s (sc oz)).toNat + 8192 ≤ 2 ^ 64
  c : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩] s.wr

theorem S4H.of {s : State} (L : Lay rbs wbs s) {oa oz : Nat} (hc : s4Chk (rbs ++ wbs) wbs oa oz = true) :
    S4H oa oz s := by
  simp only [s4Chk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨hoa, hra⟩, hwa⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩ := hc
  exact ⟨hoa, hoz, L.disj s1, L.disj s2, L.disj s3, L.stkD hrs, L.stkD hra, L.stkD hrz, L.nwp hra, L.nwp hrz,
    covers_append (covers_cons (L.cR hrs) covers_nil) (covers_cons (L.cR hra) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwa) (covers_cons (L.cW hwz) covers_nil)⟩

theorem s4Glue_ok (oa oz : Nat) (ha : oa < 2 ^ 31) (hz : oz < 2 ^ 31) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ lea .rsi (sc oa) ++ lea .rdx (sc oz))) s fun s1 =>
      ((s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ha, sx_ofNat hz, sx_ofNat (show 0 < 2 ^ 31 by decide), pa_sc0, List.cons_append, List.nil_append]

theorem s4Pre {oa oz : Nat} {s s1 : State} (h : S4H oa oz s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz))
    (k : Keep argRegs s s1) :
    sample4K.pre (s1.callEntry.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [sample4K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hv.1, hv.2.1, hv.2.2]
  exact ⟨trivial, trivial, h.dSA, h.dSZ, h.dAZ, ret_disj s1 (by rw [hsp]; exact h.kS),
    ret_disj s1 (by rw [hsp]; exact h.kA), ret_disj s1 (by rw [hsp]; exact h.kZ),
    stk_disj24 s1 (by rw [hsp]; exact h.kS), stk_disj24 s1 (by rw [hsp]; exact h.kA),
    stk_disj24 s1 (by rw [hsp]; exact h.kZ), h.nwA, h.nwZ⟩

theorem range_all_congr {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).all f = (List.range n).all g := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun H k hk => h k hk ▸ H k hk, fun H k hk => (h k hk).symm ▸ H k hk⟩

/-- Whether `SampleNTT` of the four seeds at `p` all succeed within 280 iterations. -/
abbrev all4 (m : Mem) (p : Addr) : Bool :=
  (List.range 4).all fun k => (sampleNTT minIterations (seed4 m p k)).isSome

/-- What a call of `vg_mlkem_sample_ntt4` leaves. -/
structure S4Post (oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all4 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 4, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIs s'.mem (poly4 (pa s (sc oa)) k) f

theorem S4Post.b {oa oz : Nat} {s s' : State} (h : S4Post oa oz s s') :
    PPostB s s' [(sc oa, 4096), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

theorem sample4At_ok (v : Sample4Impl) {oa oz : Nat} {s : State} (h : S4H oa oz s) :
    WP isa (sample4At v.callee (sc oa) (sc oz)) s (S4Post oa oz s) := by
  have hd := v.depth_le
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.call v.ok v.nosp (by omega) (s4Pre h hv k) (by rw [k.2.1, k.2.2]; exact h.c)
    (by rw [k.2.2]; exact h.w) fun s2 hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  have hsd : ∀ k < 4, seed4 s1.callEntry.mem (pa s (sc 0)) k = seed4 s.mem (pa s (sc 0)) k := fun k hk => by
    unfold seed4
    rw [ce_bytesAt s1 (p := pa s (sc 0) + BitVec.ofNat 64 (34 * k)) (n := 34) (by decide) (by rw [hsp]; exact h.kS.sub_right (Offset.sub_base _ (by omega))), hm]
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2.1, hm₂] at hpost
  rw [hg₂ .rax (by decide), range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
    (hsd k hk)] at hpost
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm, ← hsp]
    exact Frame.below_mono hf (by omega) (by omega)
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hpost.1]
  · rw [hm3]; exact hpost.2 j hj f (by rw [hsd j hj]; exact hf)

theorem sample4At_tr (v : Sample4Impl) {oa oz : Nat} :
    RelCT isa (fun x y => S4H oa oz x ∧ S4H oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136)
      (sample4At v.callee (sc oa) (sc oz)) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (S4H oa oz x ∧ S4H oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = pa x (sc oa) ∧ x1.gpr .rdx = pa x (sc oz)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = pa y (sc oa) ∧ y1.gpr .rdx = pa y (sc oz)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨s4Glue_ok oa oz hx.offA hx.offZ x, s4Glue_ok oa oz hy.offA hy.offZ y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (RelCT.callEx v.ok v.ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, s4Pre hx hv1 k1, s4Pre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
    by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
    by rw [hs1, hs2, e3]⟩
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
    ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2]
  rw [ce_bytesAt x1 (n := 136) (by decide) (by rw [hs1]; exact hx.kS),
    ce_bytesAt y1 (n := 136) (by decide) (by rw [hs2]; exact hy.kS), hm1, hm2, e4]
  simp only [pa, e1, hs1, hs2, e3, and_self]

/-! ## Four entries -/

/-- What entries `e₀, …, e₀ + 3` write. -/
abbrev quadW (oa oz : Nat) : List (Ptr × Nat) :=
  seedW 0 ++ seedW 1 ++ seedW 2 ++ seedW 3 ++ [(sc oa, 4096), (sc oz, 8192)]

def quadChk (bs wbs : List (Reg × Nat)) (oa oz : Nat) : Bool :=
  seedsChk bs wbs 0 && seedsChk bs wbs 1 && seedsChk bs wbs 2 && seedsChk bs wbs 3 && s4Chk bs wbs oa oz

theorem quadChk_spec {bs wbs : List (Reg × Nat)} {oa oz : Nat} (hc : quadChk bs wbs oa oz = true) :
    seedsChk bs wbs 0 = true ∧ seedsChk bs wbs 1 = true ∧ seedsChk bs wbs 2 = true ∧ seedsChk bs wbs 3 = true ∧
      s4Chk bs wbs oa oz = true := by
  simp only [quadChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h0, h1, h2, h3, h4⟩

theorem seed4_eq {ρ : List Byte} {n e₀ : Nat} {s : State} (h : SeedsIs ρ n e₀ 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc 0)) k = matSeed ρ ((e₀ + k) / n) ((e₀ + k) % n) := by
  unfold seed4
  rw [pa, off_add, Nat.zero_add]
  exact h.seeds k hk

/-- The four seeds, then `vg_mlkem_sample_ntt4`, in a layout. -/
theorem quad4_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte}
    {n e₀ : Nat} (he : e₀ + 4 ≤ 256) {oa oz : Nat} (hc : quadChk (rbs ++ wbs) wbs oa oz = true)
    (h : SeedsIs ρ n e₀ 0 s) {v : Callee4} {Q : State → Prop}
    (hQ : ∀ s₄, PPost s s₄ (seedW 0 ++ seedW 1 ++ seedW 2 ++ seedW 3) → SeedsIs ρ n e₀ 4 s₄ →
      Lay rbs wbs s₄ → WP isa (sample4At v (sc oa) (sc oz)) s₄ Q) :
    WP isa (quad v n e₀ (sc oa) (sc oz)) s Q := by
  obtain ⟨c0, c1, c2, c3, _⟩ := quadChk_spec hc
  unfold quad
  refine WP.seq (WP.mono (seed_step L hcs (by omega) c0 h) fun s₁ ⟨P₁, h₁⟩ => ?_)
  have L₁ := L.post P₁.b hcs
  refine WP.seq (WP.mono (seed_step L₁ hcs (by omega) c1 h₁) fun s₂ ⟨P₂, h₂⟩ => ?_)
  have L₂ := L₁.post P₂.b hcs
  refine WP.seq (WP.mono (seed_step L₂ hcs (by omega) c2 h₂) fun s₃ ⟨P₃, h₃⟩ => ?_)
  have L₃ := L₂.post P₃.b hcs
  refine WP.seq (WP.mono (seed_step L₃ hcs (by omega) c3 h₃) fun s₄ ⟨P₄, h₄⟩ => ?_)
  exact hQ s₄ (PPost.app (PPost.app (PPost.app P₁ P₂ (by decide)) P₃ (by decide)) P₄ (by decide)) h₄
    (L₃.post P₄.b hcs)

theorem quad_ok (v : Sample4Impl) {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {n e₀ : Nat} (he : e₀ + 4 ≤ 256) {oa oz : Nat} (hc : quadChk (rbs ++ wbs) wbs oa oz = true) :
    WP isa (quad v.callee n e₀ (sc oa) (sc oz)) s fun s' => PPostB s s' (quadW oa oz) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 4).all (fun k => (sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e₀ + k) / n) ((e₀ + k) % n))).isSome) then 1 else 0)) ∧
      ∀ k < 4, ∀ f, sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e₀ + k) / n) ((e₀ + k) % n)) = some f →
        PolyIs s'.mem (pa s (sc (oa + 1024 * k))) f := by
  refine quad4_ok L hcs he hc ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ fun s₄ P h₄ L₄ => ?_
  refine WP.mono (sample4At_ok v (S4H.of L₄ (quadChk_spec hc).2.2.2.2)) fun s' h' => ?_
  have ea : pa s₄ (sc oa) = pa s (sc oa) := P.pa rbx_cs
  refine ⟨PPostB.app P.b h'.b (by simp [bases]), ?_, fun k hk f hf => ?_⟩
  · rw [h'.r15, P.cs .r15 (by decide), all4, range_all_congr fun k hk => congrArg
      (fun B => (sampleNTT minIterations B).isSome) (seed4_eq h₄ hk)]
  · have := h'.res k hk f (by rw [seed4_eq h₄ hk]; exact hf)
    rwa [poly4, ea, pa, off_add] at this

/-! ## Constant time -/

theorem copyT0 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 0)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 0)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT1 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 1)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 1)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT2 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 2)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 2)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT3 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 3)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 3)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT {k : Nat} (hk : k < 4) : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * k)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * k)) (sc oSB) 32))).isSome = true := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  exacts [copyT0, copyT1, copyT2, copyT3]

theorem setT : ∀ k < 4, ∀ i < 4, ∀ j < 4, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc (34 * k + 32)) j ++ setB (sc (34 * k + 33)) i)) (.block [])).isSome = true := by
  decide +kernel

/-- Two runs in a layout, each with `ρ` and the first `K` seeds. -/
abbrev RQ (rbs wbs : List (Reg × Nat)) (ρ : List Byte) (n e₀ K : Nat) (x y : State) : Prop :=
  LRel rbs wbs x y ∧ SeedsIs ρ n e₀ K x ∧ SeedsIs ρ n e₀ K y

theorem copyChk_dst {bs wbs : List (Reg × Nat)} {dst src : Ptr} {n : Nat} (hc : copyChk bs wbs dst src n = true) :
    inB bs dst n = true := by
  simp only [copyChk, wrOk, rdOk, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.2

theorem seed_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte} {n e₀ K : Nat} (he : e₀ + K < 256)
    (hK : K < 4) (hi : (e₀ + K) / n < 4) (hj : (e₀ + K) % n < 4) (hc : seedsChk (rbs ++ wbs) wbs K = true) :
    RelCT isa (RQ rbs wbs ρ n e₀ K) (seedAt K ((e₀ + K) / n) ((e₀ + K) % n)) (RQ rbs wbs ρ n e₀ (K + 1)) := by
  have hs : seedChk (rbs ++ wbs) wbs K = true := by
    simp only [seedsChk, Bool.and_eq_true] at hc; exact hc.1.1
  have hcp : copyChk (rbs ++ wbs) wbs (sc (34 * K)) (sc oSB) 32 = true := by
    simp only [seedChk, Bool.and_eq_true] at hs; exact hs.1.1.1.1.1
  have hin := copyChk_dst hcp
  have htr : RelCT isa (LRel rbs wbs) (seedAt K ((e₀ + K) / n) ((e₀ + K) % n)) fun _ _ => True := by
    unfold seedAt
    refine RelCT.seq (LRel.step hcs (taintRel [.rbx] (fun x y h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (copyT hK))
      fun x Lx => WP.mono (copy_okL Lx (by decide) hcp) fun _ h => ⟨_, h.1⟩) ?_
    exact taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (setT K hK _ hi _ hj)
  exact RelCT.postDep (F := fun x x' => PPost x x' (seedW K) ∧ SeedsIs ρ n e₀ (K + 1) x')
    (RelCT.mono htr (fun _ _ h => h.1) fun _ _ h => h)
    (fun x y h => ⟨seed_step h.1.1 hcs he hc h.2.1, seed_step h.1.2.1 hcs he hc h.2.2⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, hx.2, hy.2⟩

theorem bytesAt136 (m : Mem) (p : Addr) :
    bytesAt m p 136 = seed4 m p 0 ++ (seed4 m p 1 ++ (seed4 m p 2 ++ seed4 m p 3)) := by
  rw [show (136 : Nat) = 34 + (34 + (34 + 34)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add]
  simp only [seed4, off_add, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero]

/-- The constant time of the four entries, for a given `ρ`. -/
theorem quad_tr (v : Sample4Impl) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte} {n e₀ : Nat}
    (he : e₀ + 4 ≤ 256) (hij : ∀ k < 4, (e₀ + k) / n < 4 ∧ (e₀ + k) % n < 4) {oa oz : Nat}
    (hc : quadChk (rbs ++ wbs) wbs oa oz = true) :
    RelCT isa (RQ rbs wbs ρ n e₀ 0) (quad v.callee n e₀ (sc oa) (sc oz)) fun _ _ => True := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := quadChk_spec hc
  have hin : inB (rbs ++ wbs) (sc 0) 136 = true := by
    simp only [s4Chk, rdOk, Bool.and_eq_true] at c4; exact c4.1.1.1.1.1.2
  unfold quad
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 0 (by decide)).1 (hij 0 (by decide)).2 c0) ?_
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 1 (by decide)).1 (hij 1 (by decide)).2 c1) ?_
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 2 (by decide)).1 (hij 2 (by decide)).2 c2) ?_
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 3 (by decide)).1 (hij 3 (by decide)).2 c3) ?_
  refine RelCT.mono (sample4At_tr v) (fun x y h => ⟨S4H.of h.1.1 c4, S4H.of h.1.2.1 c4, h.1.eq hin, h.1.2.2.2, ?_⟩)
    fun _ _ h => h
  rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
    seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
    seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]

end VG.Proof.MlKem.X86_64
