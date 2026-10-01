import VerifiedGarbage.Proof.Blake2.X86.CompressB.Body
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# BLAKE2b compression function on x86 (32-bit): one block and the loop

Untrusted: everything here is checked by Lean. `body_ok`: one block, from
the invariant `Common` after `i` blocks to `Common` after `i + 1`; `correct`:
the whole function.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Work Block stateAt blockAt compressBlocks)
open VG.Proof.Sha512.X86 (Acc rd64 write64 mem_rd readSrc_mem ea_of lo_rd64 hi_rd64 rd64_frame)
open VG.Proof.Sha512.Word64 (lo hi readW64 lo_append hi_append hi_append_lo)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store readW_writeW_addr)

/-! ## Regions within the 32-bit address space -/

theorem addr_contains {x : BitVec 32} {d n e k : Nat} (hfit : x.toNat + e + k ≤ 2 ^ 32)
    (hn : 0 < n) (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) : (⟨addr x e, k⟩ : Region).Contains (addr x d) n := by
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ h₁ h₂ (by omega)

theorem addr_sub {x : BitVec 32} {d n k : Nat} (h : d + n ≤ k) (hfit : x.toNat + k ≤ 2 ^ 32) :
    Region.Sub ⟨addr x d, n⟩ ⟨x.setWidth 64, k⟩ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro a ha; simp [Region.Contains] at ha
  rw [addr_eq (by omega)]
  exact Offset.sub_base _ h

theorem Region.Sub.trans' {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) :
    Region.Sub a c := fun x h => h₂ x (h₁ x h)

/-! ## The compression function, in the order of the code -/

/-- The final block flag as a word. -/
def flagW (f : Bool) : BitVec 64 := if f then BitVec.allOnes 64 else 0

/-- The work vector before the rounds (RFC 7693 §3.2). -/
def V0 (h : HashValue 64) (t : Nat) (f : Bool) : Work 64 :=
  let v : Work 64 := h ++ Spec.Blake2.b.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat 64 t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat 64 (t / 2 ^ 64))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 64) else v

theorem F_eq (h : HashValue 64) (m : Block 64) (t : Nat) (f : Bool) :
    Spec.Blake2.F Spec.Blake2.b h m t f = Vector.ofFn fun i : Fin 8 =>
      h[i] ^^^ ((List.range 12).foldl (Spec.Blake2.round Spec.Blake2.b m) (V0 h t f))[i] ^^^
        ((List.range 12).foldl (Spec.Blake2.round Spec.Blake2.b m) (V0 h t f))[i.val + 8] := rfl

theorem V0_get (h : HashValue 64) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) :
    (V0 h t f)[k] =
      if hk8 : k < 8 then h[k] else if k = 12 then Spec.Blake2.b.IV[4] ^^^ BitVec.ofNat 64 t
      else if k = 13 then Spec.Blake2.b.IV[5] ^^^ BitVec.ofNat 64 (t / 2 ^ 64)
      else if k = 14 then Spec.Blake2.b.IV[6] ^^^ flagW f else Spec.Blake2.b.IV[k - 8]'(by omega) := by
  have base : ((h ++ Spec.Blake2.b.IV : Work 64))[k] =
      if hk8 : k < 8 then h[k] else Spec.Blake2.b.IV[k - 8]'(by omega) := by
    simp only [Vector.getElem_append]
  have e12 : (h ++ Spec.Blake2.b.IV : Work 64)[12] = Spec.Blake2.b.IV[4] := by
    simp only [Vector.getElem_append]; rfl
  have e13 : (h ++ Spec.Blake2.b.IV : Work 64)[13] = Spec.Blake2.b.IV[5] := by
    simp only [Vector.getElem_append]; rfl
  have e14 : (h ++ Spec.Blake2.b.IV : Work 64)[14] = Spec.Blake2.b.IV[6] := by
    simp only [Vector.getElem_append]; rfl
  by_cases k14 : k = 14
  · subst k14; cases f <;> simp [V0, flagW, e14]
  by_cases k13 : k = 13
  · subst k13; cases f <;> simp [V0, e13]
  by_cases k12 : k = 12
  · subst k12; cases f <;> simp [V0, e12]
  have n14 : ¬14 = k := Ne.symm k14
  have n13 : ¬13 = k := Ne.symm k13
  have n12 : ¬12 = k := Ne.symm k12
  cases f <;> simp only [V0, Vector.getElem_set, n14, n13, n12, k14, k13, k12, ite_false, base,
    Bool.false_eq_true, ite_true]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

theorem saved_bounds : ∀ p ∈ saved, 288 ≤ p.2 ∧ p.2 + 4 ≤ 512 := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt 64 s.mem ((st s₀).setWidth 64) =
    compressBlocks Spec.Blake2.b (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i (t₀ s₀) (fl s₀)
  saved : Saved s₀ s.mem
  bl : s.mem.readW (addr (scr s₀) blOff) 32 = blkAddr s₀ i
  n : s.mem.readW (addr (scr s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i)
  tlo : rd64 s.mem (scr s₀) tOff = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 64)
  thi : rd64 s.mem (scr s₀) (tOff + 8) =
    BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes 64) / 2 ^ 64)
  f : rd64 s.mem (scr s₀) fOff = flagW (fl s₀)

/-! ## Copies of 32-bit words as 64-bit words -/

theorem rd64_of_copy {m m' : Mem} {D S : BitVec 32} {d so n : Nat}
    (h : ∀ j < n, m'.readW (addr D (d + 4 * j)) 32 = m.readW (addr S (so + 4 * j)) 32) {k : Nat}
    (hk : 2 * k + 1 < n) {d' so' : Nat} (hd : d' = d + 8 * k) (hs : so' = so + 8 * k) :
    rd64 m' D d' = rd64 m S so' := by
  have e₀ := h (2 * k) (by omega)
  have e₁ := h (2 * k + 1) (by omega)
  rw [show d + 4 * (2 * k) = d' by omega, show so + 4 * (2 * k) = so' by omega] at e₀
  rw [show d + 4 * (2 * k + 1) = d' + 4 by omega, show so + 4 * (2 * k + 1) = so' + 4 by omega] at e₁
  simp only [rd64]; rw [e₀, e₁]

theorem blk_rd64 {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) (j : Fin 16) :
    blk s₀ i j = rd64 s₀.mem (blkAddr s₀ i) (8 * j) := by
  have := hp.blk_fit hi
  have hj := j.2
  rw [rd64_eq (by omega), hp.blk_addr hi]
  exact Proof.Blake2.blockAt_word _ _ _ hj

/-! ## Copying the block and initializing the work vector -/

theorem stage1_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hc : Common s₀ i s) :
    WP isa (.block (copy ++ init)) s fun s' =>
      RI (scr s₀) (blk s₀ i)
        (V0 (stateAt 64 s.mem ((st s₀).setWidth 64)) (t₀ s₀ + i * Spec.Blake2.blockBytes 64)
          (fl s₀)) s' s' ∧
      Frame [⟨(scr s₀).setWidth 64, 256⟩] s.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.gpr .esi = scr s₀ ∧ s'.gpr .esp = esp₀ s₀ := by
  have fV := hp.scr_fits
  have fS := hp.st_fits
  have fB := hp.blk_fit hi
  have hm₁ : (⟨(scr s₀).setWidth 64, 128⟩ : Region) ∈ [(⟨(scr s₀).setWidth 64, 128⟩ : Region)] :=
    List.mem_singleton_self _
  rw [WP.block_append_iff]
  -- The block.
  unfold copy
  refine wp_movm (ea_of hc.esi _) (hp.in_scr hc.wr (by decide)) fun s₁ u₁ => ?_
  rw [hc.bl] at u₁
  refine WP.mono (copyWords_ok (src := .edi) (R := ⟨(scr s₀).setWidth 64, 128⟩) (by decide) u₁.gpr
    (by rw [u₁.other _ (by decide), hc.esi]) (by omega)
    (fun j hj => by rw [u₁.rd, u₁.wr, hc.rd, hc.wr]; exact hp.blk_rd hi (by omega))
    (fun j hj => by rw [u₁.wr, hc.wr]; exact hp.acc rfl _ (by omega))
    (fun j hj => contains_addr (by omega) (by omega) (by omega))
    (fun j hj => (hp.blk_scr.sub_left (Region.Sub.trans' (addr_sub (by omega) fB)
      (hp.blk_sub hi))).sub_right (Region.sub_prefix (by omega))))
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, c₂⟩ => ?_
  have hmsg₂ : Msg (scr s₀) (blk s₀ i) s₂.mem := fun j => by
    have hj := j.2
    rw [blk_rd64 hp hi j, rd64_of_copy c₂ (k := j) (by omega) (by simp only [msgOff]; omega) rfl,
      u₁.mem, Nat.zero_add]
    exact rd64_frame hc.frame (hp.blk_disj hi) fB (by omega)
  have F₂ : Frame [⟨(scr s₀).setWidth 64, 256⟩] s.mem s₂.mem := by
    rw [← u₁.mem]
    exact f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hrd₂ : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd, hc.rd]
  have hwr₂ : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr, hc.wr]
  have hesi₂ : s₂.gpr .esi = scr s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), hc.esi]
  have hesp₂ : s₂.gpr .esp = esp₀ s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), hc.esp]
  have hF₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
    hc.frame.trans (F₂.sub fun r hr => ⟨scrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)
  -- The state.
  unfold init
  refine wp_movm (ea_of hesp₂ _) (hp.in_arg hrd₂ (by decide) (by decide)) fun s₃ u₃ => ?_
  have ecx₃ : s₃.gpr .ecx = st s₀ := by rw [u₃.gpr]; exact hp.arg_frame hF₂ (i := 0) (by decide)
  rw [List.append_eq, WP.block_append_iff]
  have hR₃ : ∀ j < 16, (⟨addr (scr s₀) 128, 128⟩ : Region).Contains (addr (scr s₀) (vOff 0 + 4 * j)) 4 :=
    fun j hj => addr_contains (by omega) (by decide) (by simp only [vOff]; omega)
      (by simp only [vOff]; omega)
  refine WP.mono (copyWords_ok (src := .ecx) (S := st s₀) (D := scr s₀) (so := 0) (d := vOff 0)
    (n := 16) (R := ⟨addr (scr s₀) 128, 128⟩) (by decide) ecx₃ (by rw [u₃.other _ (by decide), hesi₂])
    (by simp only [vOff]; omega)
    (fun j hj => by rw [u₃.rd, u₃.wr]; exact hp.in_st hwr₂ (by omega))
    (fun j hj => by rw [u₃.wr, hwr₂]; exact hp.acc rfl _ (by simp only [vOff]; omega)) hR₃
    (fun j hj => (hp.st_scr.sub_left (addr_sub (by omega) fS)).sub_right
      (Region.Sub.trans' (addr_sub (by omega) fV) (Region.sub_prefix (Nat.le_refl _)))))
    fun s₄ ⟨g₄, rd₄, wr₄, f₄, c₄⟩ => ?_
  have hesi₄ : s₄.gpr .esi = scr s₀ := by rw [g₄ _ (by decide), u₃.other _ (by decide), hesi₂]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, u₃.wr, hwr₂]
  have hA := hp.acc hwr₄
  -- The rest of the work vector.
  rw [← List.append_nil (ivWord 15 _)]
  refine ivWord_ok hesi₄ hA (by decide) _ fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  refine ivWord_ok (by rw [g₅ _ (by decide), hesi₄]) (by rw [wr₅]; exact hA) (by decide) _
    fun s₆ g₆ rd₆ wr₆ m₆ => ?_
  refine ivWord_ok (by rw [g₆ _ (by decide), g₅ _ (by decide), hesi₄]) (by rw [wr₆, wr₅]; exact hA)
    (by decide) _ fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  refine ivWord_ok (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), hesi₄])
    (by rw [wr₇, wr₆, wr₅]; exact hA) (by decide) _ fun s₈ g₈ rd₈ wr₈ m₈ => ?_
  have e₈ : s₈.gpr .esi = scr s₀ := by
    rw [g₈ _ (by decide), g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), hesi₄]
  have w₈ : s₈.wr = s₄.wr := by rw [wr₈, wr₇, wr₆, wr₅]
  refine ivXor_ok e₈ (by rw [w₈]; exact hA) fV (by decide) (by decide) (by decide) _
    fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  refine ivXor_ok (by rw [g₉ _ (by decide), e₈]) (by rw [wr₉, w₈]; exact hA) fV (by decide)
    (by decide) (by decide) _ fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  refine ivXor_ok (by rw [g₁₀ _ (by decide), g₉ _ (by decide), e₈]) (by rw [wr₁₀, wr₉, w₈]; exact hA)
    fV (by decide) (by decide) (by decide) _ fun s₁₁ g₁₁ rd₁₁ wr₁₁ m₁₁ => ?_
  refine ivWord_ok (by rw [g₁₁ _ (by decide), g₁₀ _ (by decide), g₉ _ (by decide), e₈])
    (by rw [wr₁₁, wr₁₀, wr₉, w₈]; exact hA) (by decide) _
    fun s₁₂ g₁₂ rd₁₂ wr₁₂ m₁₂ => WP.block_nil ?_
  -- Frames.
  have hm : (⟨(scr s₀).setWidth 64, 256⟩ : Region) ∈ [(⟨(scr s₀).setWidth 64, 256⟩ : Region)] :=
    List.mem_singleton_self _
  have fw : ∀ {m m' : Mem} {o : Nat} (v : BitVec 64), o + 8 ≤ 256 →
      Frame [⟨(scr s₀).setWidth 64, 256⟩] m m' →
      Frame [⟨(scr s₀).setWidth 64, 256⟩] m (write64 m' (scr s₀) o v) :=
    fun v ho h => Proof.Sha512.X86.frame_write64 h hm (by omega) ho v
  have F₄ : Frame [⟨(scr s₀).setWidth 64, 256⟩] s.mem s₄.mem := by
    refine F₂.trans ?_
    rw [← u₃.mem]
    exact f₄.sub fun r hr => ⟨_, hm, by
      simp only [List.mem_singleton] at hr; subst hr
      exact addr_sub (by omega) (by omega)⟩
  have F₁₂ : Frame [⟨(scr s₀).setWidth 64, 256⟩] s.mem s₁₂.mem := by
    rw [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆, m₅]
    exact fw _ (by decide) (fw _ (by decide) (fw _ (by decide) (fw _ (by decide) (fw _ (by decide)
      (fw _ (by decide) (fw _ (by decide) (fw _ (by decide) F₄)))))))
  -- The parameters, read through the copies.
  have hi₄ : ∀ d, 256 ≤ d → d + 8 ≤ 512 → rd64 s₄.mem (scr s₀) d = rd64 s.mem (scr s₀) d :=
    fun d h1 h2 => hp.high_frame64 (.inl F₄) h1 h2
  have tl₄ := (hi₄ tOff (by decide) (by decide)).trans hc.tlo
  have th₄ := (hi₄ (tOff + 8) (by decide) (by decide)).trans hc.thi
  have fl₄ := (hi₄ fOff (by decide) (by decide)).trans hc.f
  have r₅ := rw64_ne fV; have r₆ := rw64_self fV
  -- The work vector.
  have hold : Holds (scr s₀)
      (V0 (stateAt 64 s.mem ((st s₀).setWidth 64)) (t₀ s₀ + i * Spec.Blake2.blockBytes 64)
        (fl s₀)) s₁₂.mem := by
    intro k hk
    rw [V0_get _ _ _ k hk]
    by_cases hk8 : k < 8
    · simp only [hk8, dite_true]
      have sp : ∀ j, 8 ≤ j → j < 16 → Sep8 (vOff j) (vOff k) := fun j h1 h2 => by
        simp only [Sep8, vOff]; omega
      have vk : vOff k + 8 ≤ 512 := by simp only [vOff]; omega
      rw [m₁₂, r₅ _ _ (by decide) vk (sp 15 (by decide) (by decide)), m₁₁,
        r₅ _ _ (by decide) vk (sp 14 (by decide) (by decide)), m₁₀,
        r₅ _ _ (by decide) vk (sp 13 (by decide) (by decide)), m₉,
        r₅ _ _ (by decide) vk (sp 12 (by decide) (by decide)), m₈,
        r₅ _ _ (by decide) vk (sp 11 (by decide) (by decide)), m₇,
        r₅ _ _ (by decide) vk (sp 10 (by decide) (by decide)), m₆,
        r₅ _ _ (by decide) vk (sp 9 (by decide) (by decide)), m₅,
        r₅ _ _ (by decide) vk (sp 8 (by decide) (by decide)),
        rd64_of_copy c₄ (k := k) (by omega) (by unfold vOff; omega) rfl, u₃.mem, Nat.zero_add,
        stateAt_rd64 fS _ hk8]
      exact rd64_frame F₂ (by simpa using hp.st_scr.sub_right (Region.sub_prefix (by omega))) fS
        (by omega)
    · have : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆, m₅, r₅, r₆, tl₄, th₄, fl₄,
        dite_false, ite_true, ite_false, Nat.reduceSub, Nat.lt_irrefl, Nat.reduceLT,
        Nat.reduceEqDiff]
  have hmsg : Msg (scr s₀) (blk s₀ i) s₁₂.mem := fun j => by
    have hj := j.2
    have mj : msgOff j + 8 ≤ 512 := by simp only [msgOff]; omega
    have sp : ∀ k, Sep8 (vOff k) (msgOff j) := fun k => (msg_vOff j).symm
    rw [m₁₂, r₅ _ _ (by decide) mj (sp _), m₁₁, r₅ _ _ (by decide) mj (sp _), m₁₀,
      r₅ _ _ (by decide) mj (sp _), m₉, r₅ _ _ (by decide) mj (sp _), m₈,
      r₅ _ _ (by decide) mj (sp _), m₇, r₅ _ _ (by decide) mj (sp _), m₆,
      r₅ _ _ (by decide) mj (sp _), m₅, r₅ _ _ (by decide) mj (sp _),
      rd64_frame f₄ (N := 128) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [addr_eq (by omega)]; exact Offset.base_disjoint _ (by decide) (by decide))
        (by omega) (by simp only [msgOff]; omega), u₃.mem]
    exact hmsg₂ j
  refine ⟨⟨hold, hmsg, Keep.refl _, Frame.refl _ _⟩, F₁₂, ?_, ?_, ?_, ?_⟩
  · rw [rd₁₂, rd₁₁, rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, u₃.rd, hrd₂]
  · rw [wr₁₂, wr₁₁, wr₁₀, wr₉, w₈, hwr₄]
  · rw [g₁₂ _ (by decide), g₁₁ _ (by decide), g₁₀ _ (by decide), g₉ _ (by decide), e₈]
  · rw [g₁₂ _ (by decide), g₁₁ _ (by decide), g₁₀ _ (by decide), g₉ _ (by decide),
      g₈ _ (by decide), g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide),
      u₃.other _ (by decide), hesp₂]

/-! ## The parameters after `advance` -/

theorem advMem_frame {s₀ : State} (hp : Pre s₀) (m : Mem) : Frame [scrR s₀] m (advMem (scr s₀) m) := by
  have c : ∀ d, d + 4 ≤ 512 → (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
    fun d hd => contains_addr hd (by omega) hp.scr_fits
  have hm := List.mem_singleton_self (scrR s₀)
  simp only [advMem]
  exact ((((((Frame.refl _ _).writeW hm _ (c _ (by decide))).writeW hm _ (c _ (by decide))).writeW
    hm _ (c _ (by decide))).writeW hm _ (c _ (by decide))).writeW hm _ (c _ (by decide))).writeW hm _
    (c _ (by decide))

/-- A 64-bit addition of a 32-bit constant, by `add` and `adc` of the halves. -/
theorem add_halves (L H : BitVec 32) (y : BitVec 32) :
    (H + 0 + (BitVec.ofBool (decide (2 ^ 32 ≤ L.toNat + y.toNat))).setWidth 32) ++ (L + y) =
      (H ++ L) + y.setWidth 64 := by
  apply Proof.Sha512.Word64.eq_of_lo_hi
  · rw [lo_append, Proof.Sha512.Word64.lo_add, lo_append]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [lo]
    exact (Nat.mod_eq_of_lt y.isLt).symm
  · rw [hi_append, Proof.Sha512.Word64.hi_add, hi_append, lo_append, Proof.Sha512.X86.carry_eq]
    have e1 : hi (y.setWidth 64) = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [Proof.Sha512.Word64.hi_toNat]; simp; omega
    have e2 : (lo (y.setWidth 64)).toNat = y.toNat := by
      rw [Proof.Sha512.Word64.lo_toNat]; simp; exact y.isLt
    rw [e1, e2]

/-- The carry out of `add_halves`. -/
theorem carry_halves (L H : BitVec 32) (y : BitVec 32) :
    (2 ^ 32 ≤ H.toNat + (0 : BitVec 32).toNat +
      (decide (2 ^ 32 ≤ L.toNat + y.toNat)).toNat) ↔ 2 ^ 64 ≤ (H ++ L).toNat + y.toNat := by
  have hL := L.isLt; have hH := H.isLt; have hy := y.isLt
  have e : (H ++ L).toNat = H.toNat * 2 ^ 32 + L.toNat := by
    have := Proof.Sha512.Word64.hi_toNat (H ++ L)
    have := Proof.Sha512.Word64.lo_toNat (H ++ L)
    rw [hi_append] at *; rw [lo_append] at *
    omega
  rw [e]
  by_cases h : 2 ^ 32 ≤ L.toNat + y.toNat <;> simp [h] <;> omega

/-- The carry into the high 64 bits of the counter, by `adc` of their halves. -/
theorem adc_halves (L H : BitVec 32) (c : Bool) :
    (H + 0 + (BitVec.ofBool (decide (2 ^ 32 ≤ L.toNat + (0 : BitVec 32).toNat + c.toNat))).setWidth 32) ++
      (L + 0 + (BitVec.ofBool c).setWidth 32) = (H ++ L) + (BitVec.ofBool c).setWidth 64 := by
  apply Proof.Sha512.Word64.eq_of_lo_hi
  · rw [lo_append, Proof.Sha512.Word64.lo_add, lo_append]
    apply BitVec.eq_of_toNat_eq
    cases c <;> simp [lo]
  · rw [hi_append, Proof.Sha512.Word64.hi_add, hi_append, lo_append]
    have e1 : hi ((BitVec.ofBool c).setWidth 64) = 0 := by cases c <;> decide
    have e2 : (lo ((BitVec.ofBool c).setWidth 64)).toNat = c.toNat := by cases c <;> decide
    rw [e1, e2]
    by_cases h : 2 ^ 32 ≤ L.toNat + c.toNat <;> simp [h]

theorem carry_ofNat (T : Nat) : BitVec.ofNat 64 (T / 2 ^ 64) +
    (BitVec.ofBool (decide (2 ^ 64 ≤ (BitVec.ofNat 64 T).toNat + 128))).setWidth 64 =
    BitVec.ofNat 64 ((T + 128) / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  by_cases h : 2 ^ 64 ≤ T % 2 ^ 64 + 128
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_true, Bool.toNat_true]
    omega
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_false, Bool.toNat_false]
    omega

theorem advMem_reads {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) (m : Mem) :
    (advMem B m).readW (addr B blOff) 32 = m.readW (addr B blOff) 32 + 128 ∧
    (advMem B m).readW (addr B nOff) 32 = m.readW (addr B nOff) 32 - 1 ∧
    rd64 (advMem B m) B tOff = rd64 m B tOff + 128 ∧
    rd64 (advMem B m) B (tOff + 8) = rd64 m B (tOff + 8) +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (rd64 m B tOff).toNat + 128))).setWidth 64 ∧
    ∀ d, 280 ≤ d → d + 4 ≤ 512 → (advMem B m).readW (addr B d) 32 = m.readW (addr B d) 32 := by
  have r32 := rw32_ne hfit
  refine ⟨?_, ?_, ?_, ?_, fun d h1 h2 => ?_⟩
  · simp (disch := decide) only [advMem, r32, Mem.readW_writeW_self32]
  · simp (disch := decide) only [advMem, Mem.readW_writeW_self32]
  · simp (disch := decide) only [advMem, rd64, r32, Mem.readW_writeW_self32]
    exact add_halves _ _ 128
  · simp only [rd64]
    rw [show tOff + 8 + 4 = tOff + 12 from rfl]
    simp (disch := decide) only [advMem, r32, Mem.readW_writeW_self32]
    rw [adc_halves, decide_eq_decide.mpr (carry_halves _ _ 128)]
    rfl
  · simp only [advMem]
    rw [r32 _ _ (by decide) h2 (by simp only [nOff]; omega), r32 _ _ (by decide) h2 (by simp only [tOff]; omega),
      r32 _ _ (by decide) h2 (by simp only [tOff]; omega), r32 _ _ (by decide) h2 (by simp only [tOff]; omega),
      r32 _ _ (by decide) h2 (by simp only [tOff]; omega), r32 _ _ (by decide) h2 (by simp only [blOff]; omega)]

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hc : Common s₀ i s) :
    WP isa body s fun s' =>
      Common s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0) := by
  have fV := hp.scr_fits
  have fS := hp.st_fits
  refine WP.seq (WP.mono (stage1_ok hp hi hc) fun sb ⟨hR, fb, rdb, wrb, esib, espb⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok fV esib (hp.acc wrb) hR 12) fun sc hR' => ?_)
  generalize hvR : (List.range 12).foldl (Spec.Blake2.round Spec.Blake2.b (blk s₀ i))
    (V0 (stateAt 64 s.mem ((st s₀).setWidth 64)) (t₀ s₀ + i * Spec.Blake2.blockBytes 64)
      (fl s₀)) = vR at hR'
  have esic : sc.gpr .esi = scr s₀ := hR'.keep.esi esib
  have espc : sc.gpr .esp = esp₀ s₀ := (hR'.keep.gpr _ (by decide)).trans espb
  have rdc : sc.rd = s₀.rd := hR'.keep.rd.trans rdb
  have wrc : sc.wr = s₀.wr := hR'.keep.wr.trans wrb
  have Fc : Frame [⟨(scr s₀).setWidth 64, 256⟩] s.mem sc.mem := fb.trans hR'.frame
  have sub256 : ∀ r ∈ [(⟨(scr s₀).setWidth 64, 256⟩ : Region)], ∃ r' ∈ [stR s₀, scrR s₀],
      Region.Sub r r' := fun r hr => ⟨scrR s₀, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hFc : Frame [stR s₀, scrR s₀] s₀.mem sc.mem := hc.frame.trans (Fc.sub sub256)
  -- XOR the work vector into the state.
  rw [WP.block_append_iff]
  unfold finish
  refine wp_movm (ea_of espc _) (hp.in_arg rdc (by decide) (by decide)) fun sd ud => ?_
  have ecxd : sd.gpr .ecx = st s₀ := by rw [ud.gpr]; exact hp.arg_frame hFc (i := 0) (by decide)
  refine WP.mono (finishWords_ok hp ecxd (by rw [ud.other _ (by decide), esic]) (by rw [ud.rd, rdc])
    (by rw [ud.wr, wrc])) fun se hF => ?_
  have esie : se.gpr .esi = scr s₀ := by rw [hF.gpr _ (by decide), ud.other _ (by decide), esic]
  have wre : se.wr = s₀.wr := by rw [hF.wr, ud.wr, wrc]
  have Fe : Frame [stR s₀] sc.mem se.mem := by rw [← ud.mem]; exact hF.frame
  -- Advance.
  refine WP.mono (advance_ok fV esie (hp.acc wre)) fun sf ⟨mf, zf, gf, rdf, wrf⟩ => ?_
  obtain ⟨ab, an, at', ah, ao⟩ := advMem_reads fV se.mem
  rw [← mf] at ab an at' ah ao
  have hs32 : ∀ d, 256 ≤ d → d + 4 ≤ 512 →
      se.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := fun d h1 h2 => by
    rw [hp.high_frame (.inr Fe) h1 h2, hp.high_frame (.inl Fc) h1 h2]
  have hs64 : ∀ d, 256 ≤ d → d + 8 ≤ 512 → rd64 se.mem (scr s₀) d = rd64 s.mem (scr s₀) d :=
    fun d h1 h2 => by simp only [rd64]; rw [hs32 _ h1 (by omega), hs32 _ (by omega) h2]
  have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hn : se.mem.readW (addr (scr s₀) nOff) 32 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [hs32 _ (by decide) (by decide), hc.n, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have Ff : Frame [stR s₀, scrR s₀] s₀.mem sf.mem := by
    refine (hFc.trans (Fe.mono (by simp))).trans ?_
    rw [mf]; exact (advMem_frame hp _).mono (by simp)
  refine ⟨⟨?_, ?_, ?_, ?_, Ff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [zf, hn]⟩
  · rw [gf _ (by decide), esie]
  · rw [gf _ (by decide), hF.gpr _ (by decide), ud.other _ (by decide), espc]
  · rw [rdf, hF.rd, ud.rd, rdc]
  · rw [wrf, wre]
  · rw [Proof.Blake2.compressBlocks_succ, ← hc.state, F_eq, hvR]
    apply Vector.ext; intro j hj
    have hst : ∀ r ∈ [scrR s₀], Region.Disjoint ⟨(st s₀).setWidth 64, 64⟩ r := by
      simpa using hp.st_scr
    have hst' : ∀ r ∈ [(⟨(scr s₀).setWidth 64, 256⟩ : Region)],
        Region.Disjoint ⟨(st s₀).setWidth 64, 64⟩ r := by
      simpa using hp.st_scr.sub_right (Region.sub_prefix (by omega))
    rw [stateAt_rd64 fS _ hj, Vector.getElem_ofFn, mf,
      rd64_frame (advMem_frame hp _) hst fS (by omega), FI.state hF hj, ud.mem,
      hR'.holds j (by omega), hR'.holds (j + 8) (by omega), rd64_frame Fc hst' fS (by omega),
      ← stateAt_rd64 fS _ hj]
    rfl
  · intro p hp'
    have := saved_bounds p hp'
    rw [ao _ (by omega) this.2, hs32 _ (by omega) this.2]
    exact hc.saved p hp'
  · rw [ab, hs32 _ (by decide) (by decide), hc.bl]
    simp only [blkAddr]
    rw [BitVec.add_assoc, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl,
      BitVec.ofNat_add_ofNat]
    rfl
  · rw [an, hn]
  · rw [at', hs64 _ (by decide) (by decide), hc.tlo, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl,
      BitVec.ofNat_add_ofNat]
    congr 1
    simp only [Spec.Blake2.blockBytes]; omega
  · rw [ah, hs64 _ (by decide) (by decide), hs64 _ (by decide) (by decide), hc.thi, hc.tlo,
      carry_ofNat]
    congr 2
    simp only [Spec.Blake2.blockBytes]; omega
  · rw [show fOff = 280 from rfl]
    simp only [rd64]
    rw [ao _ (by decide) (by decide), ao _ (by decide) (by decide), hs32 _ (by decide) (by decide),
      hs32 _ (by decide) (by decide)]
    exact hc.f

end VG.Proof.Blake2.X86.CompressB
