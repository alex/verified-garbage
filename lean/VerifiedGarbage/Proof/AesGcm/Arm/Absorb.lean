import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1

/-!
# AES-GCM on ARMv7: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`r5` bytes at `r4` into GHASH, with the accumulator at `St + yo` and the
`r6` buffered bytes at `St + 32` (`absorb_ok`): it fills the buffer
(`headPre_ok`, `head_ok`), absorbs whole blocks (`whole_ok`) and buffers the
rest (`tail_ok`), by the steps of `Proof/Gcm/Stream.lean`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- The regions `absorb` writes. -/
abbrev absFrame (st w sp : BitVec 32) (yo : Nat) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr st + BitVec.ofNat 64 32, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`r4`, `r5`, `r6` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  r6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16)
  data : DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  le : j ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  data : DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H
      (x ++ bytesAt m₀ (State.addr D) j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (absFrame st w sp yo) m₀ s.mem

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (absFrame st w sp yo) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ absFrame st w sp yo, (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

/-- The context is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ absFrame st w sp yo,
    (⟨State.addr c + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L hyo in
/-- A write within the buffer is within what `absorb` writes. -/
theorem buf_absFrame {m m' : Mem} {o k : Nat} (h : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (absFrame st w sp yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

omit L hyo in
theorem gh_absFrame {m m' : Mem} (h : Frame [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp] m m') : Frame (absFrame st w sp yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

end

/-- After `headPre`: `k = min (16 - o, n)` bytes copied into the buffer, the
arguments advanced, and `Z` set iff the buffer is full. -/
structure HeadMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (m₀ : Mem) (k : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  kmin : k = min (16 - x.length % 16) n
  k1 : 1 ≤ k
  k16 : x.length % 16 + k ≤ 16
  kn : k ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 (k)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - k)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16 + k)
  z : s.z = decide (x.length % 16 + k = 16)
  data : DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  buf : bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) (x.length % 16 + k) =
    bytesAt m₀ (State.addr st + BitVec.ofNat 64 32) (x.length % 16) ++
      bytesAt m₀ (State.addr D) (k)
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt m₀ (State.addr st + BitVec.ofNat 64 yo)
  fw : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + x.length % 16), k⟩] m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer: `minLen`, the copy and the comparison with 16. -/
theorem headPre_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa headPre s (fun s' => ∃ k, HeadMid c st w sp k7 k8 yo H x D n s.mem k s') := by
  have hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn32 : n < 2 ^ 32 := h.data.lt32
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r6 h.r5 (by omega) hn32) fun s₁ ⟨h3, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - x.length % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h3
  have hk1 : 1 ≤ k := by omega
  have hk16 : x.length % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, h1, h2, h4, h5, h6, h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r10 32,
      .dp .add .r2 .r2 (.reg .r6), .mov .r1 (.reg .r4), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3),
      .dp .add .r6 .r6 (.reg .r3)] s₁ = some s₂ ∧
      s₂.gpr .r1 = D ∧ s₂.gpr .r2 = st + BitVec.ofNat 32 (32 + x.length % 16) ∧
      s₂.gpr .r4 = D + BitVec.ofNat 32 k ∧ s₂.gpr .r5 = BitVec.ofNat 32 (n - k) ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (x.length % 16 + k) ∧ s₂.gpr .r3 = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    have e10 := hg .r10 (by decide) (by decide)
    have e4 := hg .r4 (by decide) (by decide)
    have e5 := hg .r5 (by decide) (by decide)
    have e6 := hg .r6 (by decide) (by decide)
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e4, h.r4]
    · simp [gpr_setReg, e10, e6, he.r10, h.r6, add32_ofNat_assoc]
    · simp [gpr_setReg, e4, h.r4, h3]
    · simp [gpr_setReg, e5, h.r5, h3, ofNat_sub32 hkn hn32]
    · simp [gpr_setReg, e6, h.r6, h3, ofNat_add32]
    · simp [gpr_setReg, h3]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hk₂' := hk.trans hk₂
  have eB : State.addr (st + BitVec.ofNat 32 (32 + x.length % 16)) =
      State.addr st + BitVec.ofNat 64 (32 + x.length % 16) := L.stA (by omega)
  have lp : LoopPre s₂ D (st + BitVec.ofNat 32 (32 + x.length % 16)) k := by
    refine ⟨h1, h2, h3', hk1, by omega, by have := h.data.fit; omega,
      by rw [L.stN (by omega)]; have := L.sw; omega, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact (h.data.take hkn).rd
    · rw [hk₂'.wr, eB]; exact he.perm.stC (by omega)
    · rw [eB]; exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega))
  refine WP.seq (WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_)
  rw [eB, hk₂'.mem] at hm₃
  obtain ⟨s₄, run₄, hz₄, hg₄, hk₄⟩ := cmpk_ok s₃ .r6 (n := x.length % 16 + k) (k := 16)
    (by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]) (by omega)
    (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₄.gpr r = s₂.gpr r :=
    fun r a b c d e => by rw [hg₄, lo.other r a b c d e]
  -- The bytes copied, and the buffer.
  have hdk := length_bytesAt s.mem (State.addr D) k
  have fw : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₄.mem := by
    rw [hk₄.1, hm₃]; exact writeBytes_frame' _ hdk
  refine ⟨k, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg _ (by decide) (by decide)])
      (by rw [hk₄.2.2.2, lo.sp, hk₂'.sp]) (by rw [hk₄.2.1, lo.rd, hk₂'.rd]) (by rw [hk₄.2.2.1, lo.wr, hk₂'.wr]),
    hk'.symm, hk1, hk16, hkn, ?_, ?_, ?_, hz₄, h.data.of_eq (by rw [hk₄.2.1, lo.rd, hk₂'.rd]) (by rw [hk₄.2.2.1, lo.wr, hk₂'.wr]),
    ?_, ?_, ?_, fw⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]
  · rw [blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega), h.hH]
  · rw [hk₄.1, hm₃, show State.addr st + BitVec.ofNat 64 (32 + x.length % 16) =
        State.addr st + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (State.addr st + BitVec.ofNat 64 32) (x.length % 16)
      (bytesAt s.mem (State.addr D) k) (by rw [hdk]; omega)
    rwa [hdk] at this
  · exact blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega)) (by omega) (by omega)

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- After `headPre`: the buffer absorbed if full. -/
theorem headPost_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {k : Nat} {s : State}
    (h : HeadMid c st w sp k7 k8 yo H x D n m₀ k s) :
    WP isa (.ite .eq (ghash1 yo .r10 32) (.block [])) s
      (fun s' => ∃ j, j = k ∧ AbsMid c st w sp k7 k8 yo H x D n m₀ j s') := by
  have he := h.env
  have hk1 := h.k1; have hk16 := h.k16; have hkn := h.kn; have hkm := h.kmin
  have hdk := length_bytesAt m₀ (State.addr D) k
  refine WP.ite (decide (x.length % 16 + k = 16)) (eval_eq' h.z) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    have h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (ghash1_ok L hyo he .r10 32 (.inl rfl) (by decide) (P := st + BitVec.ofNat 32 32)
      (by rw [he.r10]) (by rw [L.stN (by decide)]; have := L.sw; omega) ?_ ?_ ?_ ?_) fun s₅ g => ?_
    · rw [L.stA (by decide)]; exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
    · rw [L.stA (by decide)]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · rw [L.stA (by decide)]; exact L.stk_st (by decide)
    · rw [L.stA (by decide)]; exact covers_left (he.perm.stC (by decide))
    refine ⟨k, rfl, g.env he, hkn, by rw [g.saved _ (by decide) (by decide)]; exact h.r4,
      by rw [g.saved _ (by decide) (by decide)]; exact h.r5, h.data.of_eq g.rd g.wr, ?_, ?_, .inr (by omega), ?_⟩
    · rw [blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm, h.hH]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16)
        (B := bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, h.buf, ha.2]
      · rw [g.out, h.hY, h.hH, L.stA (by decide)]; rfl
    · exact (buf_absFrame (yo := yo) (w := w) (sp := sp) h.fw hk16).trans (gh_absFrame g.frame)
  · -- Not full: the data is used up.
    have h16 : x.length % 16 + k < 16 := by simp at hf; omega
    refine WP.block_nil ⟨k, rfl, he, hkn, h.r4, h.r5, h.data, h.hH, fun ha => ?_, .inl (by omega),
      buf_absFrame (yo := yo) (w := w) (sp := sp) h.fw hk16⟩
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) h.hY (by rw [hdk]; exact h.buf)

/-- Filling the buffer. -/
theorem head_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead yo) s (fun s' => ∃ j, j = min (16 - x.length % 16) n ∧
      AbsMid c st w sp k7 k8 yo H x D n s.mem j s') :=
  WP.seq (WP.mono (headPre_ok L hyo h hn ho) fun _ ⟨_, hm⟩ =>
    WP.mono (headPost_ok L hyo hm) fun _ ⟨j, hj, h'⟩ => ⟨j, hj.trans hm.kmin, h'⟩)

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L hyo in
/-- The split of the rest into whole blocks and the last bytes. -/
theorem split_ok {s : State} {D : BitVec 32} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D + BitVec.ofNat 32 j) (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)) :
    ∃ s', runBlock isa splitWhole s = some s' ∧
      s'.gpr .r2 = D + BitVec.ofNat 32 j ∧ s'.gpr .r3 = BitVec.ofNat 32 ((n - j) / 16) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r5 = BitVec.ofNat 32 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.z = decide ((n - j) / 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (BitVec.ofNat 32 (n - j))
  rw [toNat32 (by omega)] at hand
  have hsub : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 ((n - j) % 16) = BitVec.ofNat 32 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) (by omega)]; congr 1; omega
  refine ⟨_, by simp only [splitWhole]; arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h4]
  · simp [gpr_setReg, h5, shr4 (show n - j < 2 ^ 32 by omega)]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h4, h5, hand, hsub, add32_ofNat_assoc]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, hand]
    congr 1; omega
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, shr4 (show n - j < 2 ^ 32 by omega)]
    rw [z_cmp (by omega) (by decide)]
  · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The whole blocks. -/
theorem whole_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid c st w sp k7 k8 yo H x D n m₀ j s) (hm₀ : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n) :
    WP isa (absorbWhole yo) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      AbsMid c st w sp k7 k8 yo H x D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.lt32
  have he := h.env
  obtain ⟨s₁, run₁, h2, h3, h4, h5, hz, hg₁, hk₁⟩ := split_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h3 h4 h5 hz
  have h16 : 16 * nb ≤ n - j := by omega
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ : DataOk st w sp s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  refine WP.ite (decide (nb = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, hd₁, by rw [hk₁.mem]; exact h.hH,
      fun ha => by rw [hk₁.mem]; exact h.abs ha, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega) (by omega)
    have h9 := he₁.r9; have h10 := he₁.r10; have h11 := he₁.r11
    obtain ⟨s₂, run₂, h0', h1', h12', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
        [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r12 .r11 scrO] s₁ = some s₂ ∧
        s₂.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s₂.gpr .r1 = st + BitVec.ofNat 32 yo ∧
        s₂.gpr .r12 = w + BitVec.ofNat 32 512 ∧
        (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
      refine ⟨_, by arun [show encodable (BitVec.ofNat 32 yo) = true by rcases hyo with rfl | rfl <;> decide], ?_,
        ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h9]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, h11]
      · intro r a b d; simp [gpr_setReg, a, b, d]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hk₂.sp hk₂.rd hk₂.wr
    have eD := h.data.addr (j := j) (by omega)
    refine WP.mono (ghCall_ok L hyo he₂ (P := D + BitVec.ofNat 32 j) (n := nb) h0' h1'
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h2])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h3]) h12' (by have := hdj.fit; omega)
      (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide))) hdj.stk
      (by rw [hk₂.rd, hk₂.wr, hk₁.rd, hk₁.wr]; exact hdj.rd)) fun s₃ g => ?_
    refine ⟨j + 16 * nb, by omega, ⟨g.env he₂, by omega, ?_, ?_, hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_,
      .inr (by omega), ?_⟩, by omega⟩
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h4]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h5]
    · rw [blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm), hk₂.mem, hk₁.mem]; exact h.hH
    · intro ha
      have ex : x ++ bytesAt m₀ (State.addr D) (j + 16 * nb) =
          (x ++ bytesAt m₀ (State.addr D) j) ++ bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [length_bytesAt]; omega) (by simp [length_bytesAt]) ?_
      rw [g.out, hk₂.mem, hk₁.mem, h.hH, Proof.Gcm.blocksAt_eq, eD]
      congr 2
      -- The data is as in `m₀`.
      have e₁ := congrArg (fun l => l.drop j) hm₀
      have e₂ : ∀ m : Mem, (bytesAt m (State.addr D) n).drop j =
          bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j) := fun m => by
        rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
          Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      have e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      have e₄ : ∀ m : Mem, (bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (State.addr D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hk₂.mem, hk₁.mem] at this; exact h.frame.trans (gh_absFrame this)

/-- The last bytes, buffered. -/
theorem tail_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid c st w sp k7 k8 yo H x D n m₀ j s) (hj : n - j < 16)
    (hm₀ : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n) :
    WP isa absorbTail s (AbsOut c st w sp k7 k8 yo H x (x ++ bytesAt m₀ (State.addr D) n) m₀) := by
  have hn' := h.data.lt32
  have he := h.env
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  refine WP.ite (decide (n - j = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, fun ha => by rw [hm₁]; exact h.abs ha, by rw [hm₁]; exact h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
    have hdj := h.data.sub (j := j) (k := n - j) (by omega) (by omega)
    have eD := h.data.addr (j := j) (by omega)
    have h10 := he₁.r10
    obtain ⟨s₂, run₂, h1', h2', h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
        [.mov .r1 (.reg .r4), addI .r2 .r10 32, .mov .r3 (.reg .r5)] s₁ = some s₂ ∧
        s₂.gpr .r1 = D + BitVec.ofNat 32 j ∧ s₂.gpr .r2 = st + BitVec.ofNat 32 32 ∧
        s₂.gpr .r3 = BitVec.ofNat 32 (n - j) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
      refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, hg₁, h.r4]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, hg₁, h.r5]
      · intro r a b d; simp [gpr_setReg, a, b, d]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have eB := L.stA (d := 32) (by decide)
    have lp : LoopPre s₂ (D + BitVec.ofNat 32 j) (st + BitVec.ofNat 32 32) (n - j) := by
      refine ⟨h1', h2', h3', by omega, by omega, hdj.fit, by rw [L.stN (by decide)]; have := L.sw; omega, ?_, ?_, ?_⟩
      · rw [hk₂.rd, hk₂.wr, hrd₁, hwr₁]; exact hdj.rd
      · rw [hk₂.wr, hwr₁, eB]; exact he.perm.stC (by omega)
      · rw [eB]; exact hdj.st.sub_right (Lay.stSub (by omega))
    refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
    rw [hk₂.mem, hm₁, eB, eD] at hm₃
    have hlen := length_bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j)
    have fw : Frame [⟨State.addr st + BitVec.ofNat 64 32, n - j⟩] s.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame' _ hlen
    refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide)]) (lo.sp.trans hk₂.sp) (lo.rd.trans hk₂.rd)
          (lo.wr.trans hk₂.wr), ?_, ?_⟩
    · intro ha
      have ex : x ++ bytesAt m₀ (State.addr D) n =
          (x ++ bytesAt m₀ (State.addr D) j) ++ bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
        rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' h.le]
      have ed : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
          bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
        have e₁ := congrArg (fun l => l.drop j) hm₀
        have e₂ : ∀ m : Mem, (bytesAt m (State.addr D) n).drop j =
            bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j) := fun m => by
          rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
            Nat.add_sub_cancel_left]
        simpa only [e₂] using e₁
      rw [ex, ← ed]
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [length_bytesAt]; omega) (by rw [hlen]; omega) ?_ ?_
      · rw [blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega)) (by omega) (by omega)]
      · rw [hm₃]; exact bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega)
    · exact h.frame.trans ((fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩))

omit L hyo in
theorem AbsIn.keep {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (hg : s'.gpr = s.gpr) (hk : Keeps s s') : AbsIn c st w sp k7 k8 yo H x D n s' where
  env := h.env.keep (fun r _ => by rw [hg]) hk.sp hk.rd hk.wr
  r4 := by rw [hg]; exact h.r4
  r5 := by rw [hg]; exact h.r5
  r6 := by rw [hg]; exact h.r6
  data := h.data.of_eq hk.rd hk.wr
  hH := by rw [hk.mem]; exact h.hH

omit L in
theorem AbsMid.data_eq {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : AbsMid c st w sp k7 k8 yo H x D n m₀ j s) : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n :=
  bytesAt_frame h.frame (data_absFrame hyo h.data) (by have := h.data.lt; omega)

/-- After the first test: the buffer filled if it holds bytes. -/
theorem absorbFill_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) (h0 : n ≠ 0) :
    WP isa (absorbFill yo) s (fun s' => ∃ j, j = (if x.length % 16 = 0 then 0 else min (16 - x.length % 16) n) ∧
      AbsMid c st w sp k7 k8 yo H x D n s.mem j s') := by
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 h.r6
    (by have := Nat.mod_lt x.length (show 16 > 0 by decide); omega)
  have h₂ := h.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (x.length % 16 = 0)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · have ho : x.length % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h₂.env, by omega, by rw [h₂.r4, add_ofNat_zero], by rw [h₂.r5, Nat.sub_zero], h₂.data,
      h₂.hH, fun ha => by rw [hm₂]; simpa [bytesAt] using ha, .inr (by omega), by rw [hm₂]; exact Frame.refl _ _⟩
  · have ho : x.length % 16 ≠ 0 := by simpa using hf
    have := head_ok L hyo h₂ h0 ho
    rw [hm₂] at this
    exact WP.mono this fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [ho, ite_false]; exact hj, hm⟩

/-- `absorb yo`. -/
theorem absorb_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : AbsIn c st w sp k7 k8 yo H x D n s) :
    WP isa (absorb yo) s (AbsOut c st w sp k7 k8 yo H x (x ++ bytesAt s.mem (State.addr D) n) s.mem) := by
  have hn' := h.data.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 hn'
  have h₁ := h.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨h₁.env, fun ha => by rw [hm₁]; simpa [bytesAt] using ha, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (absorbFill_ok L hyo h₁ h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (whole_ok L hyo hj (hj.data_eq hyo)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact tail_ok L hyo hj' hlt (hj'.data_eq hyo)

end

end VG.Proof.AesGcm.Arm
