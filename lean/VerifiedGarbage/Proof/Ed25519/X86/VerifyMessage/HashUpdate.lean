import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Hash

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

structure Input (L : Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨p.setWidth 64, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R
  scratch : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR
  below : (below L.E 24).Disjoint ⟨p.setWidth 64, n.toNat⟩
  args : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ ⟨L.E.setWidth 64, 24⟩
  fit : p.toNat + n.toNat ≤ 2 ^ 32

def UpdateArgs (L : Lay) (c p n : BitVec 32) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 1 = c ∧ Whole.slots L.E t 2 = 0 ∧
    Whole.slots L.E t 3 = p ∧ Whole.slots L.E t 4 = n ∧ Whole.slots L.E t 5 = L.scr + 192

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

theorem update_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v)
    {c p n : BitVec 32} (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t)
    (hi : Input L p n) {prev : List Byte} (hcount : c.toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (setup 0 vs)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat) := by
  refine WP.seq (WP.mono (args_ok hc hL ha hlen hv) fun u ⟨hu, hf, hs⟩ => ?_)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hargs u hs
  have H := hashSpace hL
  have hp := Whole.update_pre hu.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inr (workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), a1, a2]
    exact (count_zero_high c).trans (congrArg (BitVec.ofNat 64) hcount)
  have hb : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ (below (u.gpr .esp) 4) := by
    rw [hu.esp]
    exact (hi.below.sub_left (below_sub (by decide) H.below)).symm
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.update_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) (ca (by decide) |>.trans a4) cnt hbsha hb
    (setup_repr hL hf hr)) fun t ⟨ht, hft, hrepr⟩ => ⟨ht, ?_, ?_⟩
  · refine (setup_frame hf).trans (hash_frame hft ?_)
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (shaWithin L)
    · exact .inl (workWithin hL)
  · have same : Spec.Ed25519.bytesAt u.mem (p.setWidth 64) n.toNat =
        Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      exact hf.bytes (R := ⟨p.setWidth 64, n.toNat⟩)
        (by rintro r hr; rw [List.mem_singleton.mp hr]; exact hi.args)
        (by have := n.isLt; change n.toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi')
    rw [same] at hrepr
    exact hrepr

end VG.Proof.Ed25519.X86.VerifyMessage
