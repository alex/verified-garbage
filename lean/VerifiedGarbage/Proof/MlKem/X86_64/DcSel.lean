import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
import VerifiedGarbage.Impl.MlKem.X86_64.Decaps

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_decaps`, the choice of the key

Untrusted: everything here is checked by Lean. The comparison of the
ciphertexts (`cmp_ok`: the OR of the XORs of their bytes), the mask
(`mid_ok`), and the choice of each byte of the key (`sel_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

theorem cmpBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) :
    WP isa cmpBody s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rdx = s.gpr .rdx ||| (BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^
          BitVec.setWidth 64 (s.mem (s.gpr .rdi))) ∧ s'.gpr .rsi = s.gpr .rsi + 1 ∧
        s'.gpr .rdi = s.gpr .rdi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold cmpBody
  xrun [h0, h1]

theorem selBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) (h2 : InRegions s.wr (s.gpr .r8) 1) :
    WP isa selBody s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8) (BitVec.setWidth 8 (((BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^
          BitVec.setWidth 64 (s.mem (s.gpr .rdi))) &&& s.gpr .rax) ^^^ BitVec.setWidth 64 (s.mem (s.gpr .rdi)))) ∧
        s'.gpr .rax = s.gpr .rax ∧ s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .r8 = s.gpr .r8 + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold selBody
  xrun [h0, h1, h2]

/-- The block between the loops: the mask, and the pointers of the choice. -/
abbrev midB : List Instr := [.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .mov .rsi (.reg .rbx),
  .alu .add .rsi (.imm (BitVec.ofNat 32 oG)), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oKB)),
  .mov .r8 (.reg .r12), .mov32 .rcx (.imm 32)]

theorem mask_eq (x : BitVec 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) =
      if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have : ¬ x.toNat < 1 := fun h' => h (BitVec.eq_of_toNat_eq (by simp; omega))
    rw [ifn h, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, decide_eq_false this]
    decide

theorem mid_ok (s : State) :
    WP isa (.block midB) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rax = (if s.gpr .rdx = 0 then BitVec.allOnes 64 else 0) ∧
        s'.gpr .rsi = pa s (sc oG) ∧ s'.gpr .rdi = pa s (sc oKB) ∧ s'.gpr .r8 = pa s (.r12, 0) ∧
        s'.gpr .rcx = BitVec.ofNat 64 32) ∧
      Keep [.rax, .rdx, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [sx_ofNat (show oG < 2 ^ 31 by decide), sx_ofNat (show oKB < 2 ^ 31 by decide)]
  exact ⟨mask_eq _, by rw [pa, add_ofNat_zero]⟩

/-! ## The loops -/

/-- The OR of the XORs of the bytes of `xs` and `ys`. -/
def accX (xs ys : List Byte) : Byte := (List.zipWith (· ^^^ ·) xs ys).foldl (· ||| ·) 0

theorem bytesAt_succ (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  rw [bytesAt_add, bytesAt_one]

theorem accX_snoc {xs ys : List Byte} (h : xs.length = ys.length) (x y : Byte) :
    accX (xs ++ [x]) (ys ++ [y]) = accX xs ys ||| (x ^^^ y) := by
  simp only [accX, List.zipWith_append h, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem zx_or_xor (a x y : Byte) :
    BitVec.setWidth 64 a ||| (BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) = BitVec.setWidth 64 (a ||| (x ^^^ y)) := by
  ext i hi
  simp

theorem sel_byte (x y : Byte) (e : Bool) :
    BitVec.setWidth 8 (((BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) &&& (if e then BitVec.allOnes 64 else 0)) ^^^
      BitVec.setWidth 64 y) = if e then x else y := by
  cases e
  · ext i hi; simp
  · rw [ifp rfl, ifp rfl, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact b8b x

theorem cmp_ok (s : State) {a b : Addr} (ha : InRegions (s.rd ++ s.wr) a 1088) (hb : InRegions (s.rd ++ s.wr) b 1088)
    (hsi : s.gpr .rsi = a) (hdi : s.gpr .rdi = b) (hdx : s.gpr .rdx = 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 1088) :
    WP isa (.loop cmpBody .ne) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdx = BitVec.setWidth 64 (accX (bytesAt s.mem a 1088) (bytesAt s.mem b 1088)) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine wp_countdown (cnt := .rcx) (N := 1088) (by decide) (by decide) (fun k s' =>
      s'.gpr .rsi = a + BitVec.ofNat 64 k ∧ s'.gpr .rdi = b + BitVec.ofNat 64 k ∧
      s'.gpr .rdx = BitVec.setWidth 64 (accX (bytesAt s.mem a k) (bytesAt s.mem b k)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', hdx', hm', hrd', hwr', kk⟩ _ => ?_) (fun _ ⟨_, _, h1, h2, h3, h4, h5⟩ => ⟨h2, h3, h4, h1, h5⟩)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [hdx]; rfl, rfl, rfl, rfl, Keep.refl _ _⟩ hcx
  refine WP.mono (cmpBody_ok s' (by rw [hrd', hwr', hsi']; exact inRegions_byte ha hk (by omega))
    (by rw [hrd', hwr', hdi']; exact inRegions_byte hb hk (by omega))) fun s'' ⟨⟨hm, hdx, hsi'', hdi'', hcx, hz⟩, k'⟩ =>
      ⟨⟨by rw [hsi'', hsi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
        by rw [hdi'', hdi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add], ?_, hm.trans hm',
        k'.2.1.trans hrd', k'.2.2.trans hwr', (kk.trans k').mono (by decide)⟩, hcx, hz⟩
  rw [hdx, hdx', hsi', hdi', hm', zx_or_xor, bytesAt_succ, bytesAt_succ,
    accX_snoc (by rw [bytesAt_length, bytesAt_length])]

theorem sel_ok (s : State) {g kb key : Addr} (e : Bool) (hg : InRegions (s.rd ++ s.wr) g 32)
    (hkb : InRegions (s.rd ++ s.wr) kb 32) (hkey : InRegions s.wr key 32)
    (dg : Region.Disjoint ⟨g, 32⟩ ⟨key, 32⟩) (dkb : Region.Disjoint ⟨kb, 32⟩ ⟨key, 32⟩)
    (hsi : s.gpr .rsi = g) (hdi : s.gpr .rdi = kb) (h8 : s.gpr .r8 = key)
    (hax : s.gpr .rax = if e then BitVec.allOnes 64 else 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 32) :
    WP isa (.loop selBody .ne) s fun s' =>
      bytesAt s'.mem key 32 = (if e then bytesAt s.mem g 32 else bytesAt s.mem kb 32) ∧
      Frame [⟨key, 32⟩] s.mem s'.mem ∧ Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.mono (wp_countdown (cnt := .rcx) (N := 32) (by decide) (by decide) (fun k s' =>
      s'.gpr .rsi = g + BitVec.ofNat 64 k ∧ s'.gpr .rdi = kb + BitVec.ofNat 64 k ∧
      s'.gpr .r8 = key + BitVec.ofNat 64 k ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨key, 32⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (key + BitVec.ofNat 64 j) =
        if e then s.mem (g + BitVec.ofNat 64 j) else s.mem (kb + BitVec.ofNat 64 j)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', h8', hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [h8]; simp, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), Keep.refl _ _⟩ hcx) fun s' ⟨_, _, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · have hax' : s'.gpr .rax = if e then BitVec.allOnes 64 else 0 := by rw [kk.gpr (by decide)]; exact hax
    refine WP.mono (selBody_ok s' (by rw [hrd', hwr', hsi']; exact inRegions_byte hg hk (by omega))
      (by rw [hrd', hwr', hdi']; exact inRegions_byte hkb hk (by omega))
      (by rw [hwr', h8']; exact inRegions_byte hkey hk (by omega)))
      fun s'' ⟨⟨hm, hax'', hsi'', hdi'', h8'', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hsi'', hsi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [hdi'', hdi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [h8'', h8', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, h8']
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
    · have eg : s'.mem (g + BitVec.ofNat 64 k) = s.mem (g + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨g, 32⟩) (by simpa using dg) (show 32 ≤ 2 ^ 64 by decide) hk
      have ekb : s'.mem (kb + BitVec.ofNat 64 k) = s.mem (kb + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨kb, 32⟩) (by simpa using dkb) (show 32 ≤ 2 ^ 64 by decide) hk
      rw [hm, h8', writeW8_apply]
      by_cases ej : j = k
      · subst ej
        rw [ifp rfl, hsi', hdi', hax', sel_byte, eg, ekb]
      · rw [ifn (fun h => ej (by have := congrArg BitVec.toNat h; simp at this; omega)), hc j (by omega)]
  · cases e
    · simp only [bytesAt, Bool.false_eq_true, ite_false]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)
    · simp only [bytesAt, ite_true]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)

/-! ## The choice -/

abbrev setupB : List Instr := [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx),
  .alu .add .rdi (.imm (BitVec.ofNat 32 oCT)), .mov32 .rcx (.imm 1088), .mov32 .rdx (.imm 0)]

theorem setup_ok (s : State) :
    WP isa (.block setupB) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rsi = pa s (.r14, 0) ∧ s'.gpr .rdi = pa s (sc oCT) ∧
        s'.gpr .rcx = BitVec.ofNat 64 1088 ∧ s'.gpr .rdx = 0) ∧
      Keep [.rsi, .rdi, .rcx, .rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [sx_ofNat (show oCT < 2 ^ 31 by decide)]
  rw [pa, add_ofNat_zero]

theorem zx_eq_zero {x : Byte} : BitVec.setWidth 64 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [b8b] at this
  · intro h; rw [h]; rfl

theorem select_ok {s : State} (hc : InRegions (s.rd ++ s.wr) (pa s (.r14, 0)) 1088)
    (hct : InRegions (s.rd ++ s.wr) (pa s (sc oCT)) 1088) (hg : InRegions (s.rd ++ s.wr) (pa s (sc oG)) 32)
    (hkb : InRegions (s.rd ++ s.wr) (pa s (sc oKB)) 32) (hkey : InRegions s.wr (pa s (.r12, 0)) 32)
    (dg : Region.Disjoint ⟨pa s (sc oG), 32⟩ ⟨pa s (.r12, 0), 32⟩)
    (dkb : Region.Disjoint ⟨pa s (sc oKB), 32⟩ ⟨pa s (.r12, 0), 32⟩) :
    WP isa select s fun s' => PPost s s' [((.r12, 0), 32)] ∧
      bytesAt s'.mem (pa s (.r12, 0)) 32 =
        if bytesAt s.mem (pa s (.r14, 0)) 1088 = bytesAt s.mem (pa s (sc oCT)) 1088 then
          bytesAt s.mem (pa s (sc oG)) 32 else bytesAt s.mem (pa s (sc oKB)) 32 := by
  unfold select
  refine WP.seq (WP.mono (setup_ok s) fun s₁ ⟨⟨hm₁, hsi₁, hdi₁, hcx₁, hdx₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmp_ok s₁ (by rw [k₁.2.1, k₁.2.2]; exact hc) (by rw [k₁.2.1, k₁.2.2]; exact hct) hsi₁ hdi₁
    hdx₁ hcx₁) fun s₂ ⟨hm₂, hrd₂, hwr₂, hdx₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok s₂) fun s₃ ⟨⟨hm₃, hax₃, hsi₃, hdi₃, h8₃, hcx₃⟩, k₃⟩ => ?_)
  have e12 : ∀ r ∈ [Reg.rbx, Reg.r12], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide),
      k₁.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide)]
  have pG : pa s₂ (sc oG) = pa s (sc oG) := by rw [pa, pa, e12 .rbx (by simp)]
  have pKB : pa s₂ (sc oKB) = pa s (sc oKB) := by rw [pa, pa, e12 .rbx (by simp)]
  have pK : pa s₂ (.r12, 0) = pa s (.r12, 0) := by rw [pa, pa, e12 .r12 (by simp)]
  rw [pG] at hsi₃; rw [pKB] at hdi₃; rw [pK] at h8₃
  have hmem : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have hrd : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k₃.2.1, k₃.2.2, hrd₂, hwr₂, k₁.2.1, k₁.2.2]
  have hwr : s₃.wr = s.wr := by rw [k₃.2.2, hwr₂, k₁.2.2]
  have hax : s₃.gpr .rax = if decide (bytesAt s.mem (pa s (.r14, 0)) 1088 = bytesAt s.mem (pa s (sc oCT)) 1088) then
      BitVec.allOnes 64 else 0 := by
    rw [hax₃, hdx₂, hm₁, ← hsi₁, ← hdi₁, hsi₁, hdi₁]
    exact if_congr (zx_eq_zero.trans ((eq_iff_foldl_or_xor (by rw [bytesAt_length, bytesAt_length])).symm.trans
      decide_eq_true_iff.symm)) rfl rfl
  refine WP.mono (sel_ok s₃ _ (by rw [hrd]; exact hg) (by rw [hrd]; exact hkb) (by rw [hwr]; exact hkey) dg dkb hsi₃
    hdi₃ h8₃ hax hcx₃) fun s₄ ⟨hb, hf, k₄⟩ => ⟨?_, ?_⟩
  · refine post_of_keep ((((k₁.trans k₂).trans k₃).trans k₄).mono (rs' := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10])
      (by decide)) (by decide) ?_
    rw [← hmem]; exact hf
  · rw [hb, hmem]
    simp only [decide_eq_true_eq]

end Decaps

end VG.Proof.MlKem.X86_64
