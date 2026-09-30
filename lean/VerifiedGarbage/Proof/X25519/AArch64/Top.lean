import VerifiedGarbage.Proof.X25519.AArch64.Main
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# X25519 on AArch64: the whole function

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.X25519.x25519Contract` it uses, stated
for AArch64), and the correctness of `vg_x25519` against it: every write is
in the working space but the result's, so the arguments are read unchanged,
and the callee-saved registers it uses are restored from the working space.
-/

namespace VG.Proof.X25519

open VG VG.AArch64 in
/-- `vg_x25519(out = x0, scalar = x1, point = x2, scratch = x3)`. -/
def x25519AArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 32⟩
    let scalar : Region := ⟨s.gpr .x1, 32⟩
    let point : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, 4096⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch
  post s s' := Spec.X25519.bytesAt s'.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32)
      (Spec.X25519.bytesAt s.mem (s.gpr .x2) 32)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.X25519

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Regions of the working space, and outside it -/

theorem saveR_disj (b : Addr) {e n : Nat} (h : 48 ≤ e) (he : e + n ≤ 2 ^ 64) :
    (saveR b).Disjoint ⟨b + BitVec.ofNat 64 e, n⟩ := Offset.base_disjoint b h he

theorem sub_scR (b : Addr) {d n : Nat} (h : d + n ≤ 4096) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (scR b) := Offset.sub_base b h

/-- A byte of an argument outside the working space is unchanged. -/
theorem byte_out {b p : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (scR b)) (hd : (⟨p, 32⟩ : Region).Disjoint (scR b)) {i : Nat}
    (hi : i < 32) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf.bytes (R := ⟨p, 32⟩) (fun r hr => hd.sub_right (hs r hr)) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi

theorem bytesAt_out {b p : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (scR b)) (hd : (⟨p, 32⟩ : Region).Disjoint (scR b)) :
    bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => byte_out hf hs hd (List.mem_range.mp hi)

/-- A saved register's word is unchanged by writes elsewhere. -/
theorem save_frame {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (saveR b).Disjoint r) {k : Nat} (hk : k < 6) :
    wd m' b (SAVE + 8 * k) = wd m b (SAVE + 8 * k) := by
  simp only [wd]
  rw [hf.readW (r := saveR b) (Offset.contains_base b (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) hd (by decide)]

theorem saveR_slotArea (b : Addr) : ∀ r ∈ [slotArea b], (saveR b).Disjoint r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact saveR_disj b (by decide) (by decide)

/-! ## The arguments, decoded -/

theorem uN_uw (m : Mem) (p : Addr) :
    uN (uw m p 0) (uw m p 1) (uw m p 2) (uw m p 3) = leNum (bytesAt m p 32) := by
  rw [leNum_bytesAt_words64]
  have e0 : p + BitVec.ofNat 64 (8 * 0) = p := BitVec.add_zero p
  have e1 : p + BitVec.ofNat 64 (8 * 1) = p + 8 := rfl
  have e2 : p + BitVec.ofNat 64 (8 * 2) = p + 16 := rfl
  have e3 : p + BitVec.ofNat 64 (8 * 3) = p + 24 := rfl
  simp only [uN, uw, e0, e1, e2, e3]

theorem u_rep (m : Mem) (p : Addr) :
    Rep (ulimbF (uw m p)) (toFe (decodeUCoordinate (bytesAt m p 32))) 18 := by
  obtain ⟨hb, hv⟩ := ulimbF_rep (w := uw m p) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  refine ⟨hb.mono (by decide), ?_⟩
  show toFe (valN _ 15) = _
  rw [hv, uN_uw, decodeUCoordinate_eq (length_bytesAt _ _ _)]

theorem clampB_eq {m m₀ : Mem} {sc : Addr}
    (h : ∀ i < 32, m (sc + BitVec.ofNat 64 i) = m₀ (sc + BitVec.ofNat 64 i)) {t : Nat} (ht : t < 255) :
    clampB (fun i => m (sc + BitVec.ofNat 64 i)) t =
      BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt m₀ sc 32)) t) := by
  rw [scalar_bit (length_bytesAt _ _ _) ht]
  simp only [clampB]
  split_ifs
  · rfl
  · rfl
  · have hg : (bytesAt m₀ sc 32).getD (t / 8) 0 = m₀ (sc + BitVec.ofNat 64 (t / 8)) := by
      simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show t / 8 < 32 by omega), Option.map_some, Option.getD_some]
    rw [hg, h _ (by omega)]
    rfl

/-! ## The setup -/

theorem setup_ok {b sc pt : Addr} {s : State} (hs : Sc b s) (h1 : s.gpr .x1 = sc) (h2 : s.gpr .x2 = pt)
    (hsr : (⟨sc, 32⟩ : Region) ∈ s.rd) (hpr : (⟨pt, 32⟩ : Region) ∈ s.rd)
    (hdS : (⟨sc, 32⟩ : Region).Disjoint (scR b)) (hdP : (⟨pt, 32⟩ : Region).Disjoint (scR b)) :
    WP isa (.block setup) s fun s' => Sc b s' ∧
      Sl s'.mem b (lvals (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
        (init (toFe (decodeUCoordinate (bytesAt s.mem pt 32))))) lbnds ∧
      (∀ t < 255, s'.mem (b + BitVec.ofNat 64 (BITS + t)) =
        BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt s.mem sc 32)) t)) ∧
      (∀ k < 6, wd s'.mem b (SAVE + 8 * k) = v s (saved.getD k .x19)) ∧
      Kp fieldRegs s s' := by
  rw [setup, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (save_ok hs) fun s₁ ⟨sv₁, f₁, k₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  have fs₁ : ∀ r ∈ [saveR b], Region.Sub r (scR b) := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Region.sub_of_ble rfl
  refine WP.block_append (WP.mono (decode_ok hs₁ (by rw [k₁.gpr _ (by simp), h2])
    (fun q hq => ⟨_, List.mem_append_left _ (by rw [k₁.rd]; exact hpr),
      Offset.contains_base pt (by omega) (by omega)⟩)) fun s₂ ⟨l1, l3, f₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_kp k₂ (by decide)
  have fs₂ : ∀ r ∈ [slotR b X1, slotR b X3], Region.Sub r (scR b) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_scR b (by decide)
    · exact sub_scR b (by decide)
  have hin : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (sc + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨_, List.mem_append_left _ (by rw [k₂.rd, k₁.rd]; exact hsr), Offset.contains_base sc (by omega) (by omega)⟩
  have hdisj : ∀ i < 32, ∀ r ∈ [bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1 := fun i hi r hr => by
    rw [List.mem_singleton.mp hr]
    exact hdS.sub_right (sub_scR b (d := BITS) (n := 256) (by decide)) _
      (Offset.contains_base sc (by omega) (by omega))
  refine WP.block_append (WP.mono (bits_ok hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by simp), h1]) hin hdisj)
    fun s₃ ⟨b₃, f₃, k₃⟩ => ?_)
  have hs₃ := hs₂.of_kp k₃ (by decide)
  have R := u_rep s₁.mem pt
  rw [bytesAt_out f₁ fs₁ hdP] at R
  have hsl₃ : Sl s₃.mem b (fun _ => toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
      (fun n => if n = 0 ∨ n = 3 then some 18 else none) := by
    intro n hn k hk
    dsimp only at hk ⊢
    split at hk
    · cases hk
      rename_i h03
      rcases h03 with rfl | rfl
      · rw [limbs_frame (slot_ok (n := 0) (by decide)) f₃ (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)),
          show slot 0 = X1 from rfl, l1]
        exact R
      · rw [limbs_frame (slot_ok (n := 3) (by decide)) f₃ (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)),
          show slot 3 = X3 from rfl, l3]
        exact R
    · cases hk
  refine WP.mono (initSlots_ok hs₃ hsl₃ rfl rfl (by decide) (by decide)) fun s₄ ⟨hs₄, sl₄, k₄, f₄⟩ =>
    ⟨hs₄, sl₄, fun t ht => ?_, fun k hk => ?_, (((k₁.trans k₂).trans k₃).trans k₄).sub (by decide)⟩
  · rw [bits_frame f₄ (by omega), b₃ t (by omega)]
    exact clampB_eq (fun i hi => by rw [byte_out f₂ fs₂ hdS hi, byte_out f₁ fs₁ hdS hi]) ht
  · rw [save_frame f₄ (saveR_slotArea b) hk, save_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact saveR_disj b (by decide) (by decide)) hk,
      save_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact saveR_disj b (by decide) (by decide)
        · exact saveR_disj b (by decide) (by decide)) hk]
    exact sv₁ k hk

/-! ## The whole function -/

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨s₀.gpr .x1, 32⟩, ⟨s₀.gpr .x2, 32⟩]
  wr : s₀.wr = [⟨s₀.gpr .x0, 32⟩, ⟨s₀.gpr .x3, 4096⟩]
  out_sc : (⟨s₀.gpr .x0, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩
  scalar_sc : (⟨s₀.gpr .x1, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩
  point_sc : (⟨s₀.gpr .x2, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩

theorem Pre.of (s₀ : State) (h : Proof.X25519.x25519AArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Each callee-saved register is saved and restored, or never written. -/
theorem preserved_cases : ∀ r ∈ preserved,
    (∃ k < 6, saved.getD k .x19 = r) ∨ r ∉ loopRegs ++ saved := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa x25519 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      Proof.X25519.x25519AArch64.post s₀ s' := by
  obtain ⟨b, hb⟩ : ∃ b, s₀.gpr .x3 = b := ⟨_, rfl⟩
  have hs₀ : Sc b s₀ := ⟨hb, by rw [hp.wr, ← hb]; simp⟩
  refine WP.seq (WP.mono (setup_ok hs₀ rfl rfl (by rw [hp.rd]; simp) (by rw [hp.rd]; simp)
    (hb ▸ hp.scalar_sc) (hb ▸ hp.point_sc)) fun s₁ ⟨hs₁, sl₁, bits₁, sv₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (ladder_ok hs₁ sl₁ bits₁) fun s₂ ⟨hs₂, sl₂, sw₂, k₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hs₂ sl₂ (ladderAfter_swap_le _ _ (by decide)) sw₂)
    fun s₃ ⟨hs₃, ⟨vals, sl₃, e1, e2⟩, k₃, f₃⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hs₃ sl₃ e2 (by decide)) fun s₄ ⟨hs₄, sl₄, k₄, f₄⟩ => ?_)
  have hx0 : s₄.gpr .x0 = s₀.gpr .x0 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  have hw : outR (s₀.gpr .x0) ∈ s₄.wr := by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr, hp.wr]; simp
  have hdo : (saveR b).Disjoint (outR (s₀.gpr .x0)) :=
    (hb ▸ hp.out_sc).symm.sub_left (Region.sub_of_ble rfl)
  refine WP.mono (finish_ok hs₄ sl₄ (by simp [lbnds]) (by simp) hx0 hw hdo)
    fun s' ⟨r', sv', k', _⟩ => ⟨fun r hr => ?_, ?_⟩
  · rcases preserved_cases r hr with ⟨k, hk, rfl⟩ | hn
    · rw [sv' k hk]
      apply BitVec.eq_of_toNat_eq
      rw [show (s₀.gpr (saved.getD k .x19)).toNat = wd s₁.mem b (SAVE + 8 * k) from (sv₁ k hk).symm]
      show wd s₄.mem b _ = _
      rw [save_frame f₄ (saveR_slotArea b) hk, save_frame f₃ (saveR_slotArea b) hk,
        save_frame f₂ (saveR_slotArea b) hk]
    · exact ((((k₁.trans k₂).trans k₃).trans k₄).trans k').sub (by decide) |>.gpr r hn
  · show bytesAt s'.mem (s₀.gpr .x0) 32 = x25519 (bytesAt s₀.mem (s₀.gpr .x1) 32)
      (bytesAt s₀.mem (s₀.gpr .x2) 32)
    rw [r', x25519_eq]
    dsimp only
    rw [encodeUCoordinate_eq, invert_eq, Function.update_self, Function.update_of_ne (by decide), e1]

theorem x25519_ok (s : State) (hs : Proof.X25519.x25519AArch64.pre s) :
    ∃ t s', Exec isa Impl.X25519.AArch64.x25519 s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519AArch64.post s s' := by
  obtain ⟨t, s', he, h1, h2⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h1, Exec.sp he⟩, h2⟩

end VG.Proof.X25519.AArch64
