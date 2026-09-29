import VerifiedGarbage.Proof.Pbkdf2.AArch64.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256's iteration on AArch64

Untrusted: everything here is checked by Lean. The prologue, the epilogue,
and `Verified`. The first instruction zero-extends `n`, of which only the low
32 bits are public; `main` runs from there, with all of `x2` public, so its
constant time is proven by the taint analysis from that state.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (saved restore)
open VG.Proof.Hmac.X86_64 (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.AArch64 (contains_offset)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz wp_addImm wp_ldr wp_str readW_writeW_save
  untouched)
open VG.Proof.Sha256.AArch64.Stream (save_ok restore_ok saveMem saveMem_saved saveMem_frame)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base writeW_bytes writeBytes_append' iterate_congr)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The prologue -/

theorem wp_movz3 {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64 <<< 48) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 3 :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (imm.setWidth 64 <<< 48)) (by simp [exec, Size.bits])
    (k _ (Upd.write64 _ _ _))

/-- The padding into `scratch[224..256)`. -/
theorem padding_ok {s₀ : State} (hp : Pre s₀) {s : State} (h20 : s.gpr .x20 = scr s₀) (hwr : s.wr = s₀.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224) pad96 → WP isa (.block rest) s' Q) :
    WP isa (.block (padding ++ rest)) s Q := by
  simp only [padding, List.cons_append, List.nil_append]
  refine wp_movz fun s₁ u₁ => ?_
  have c₁ : s₁.gpr .x20 = scr s₀ := by rw [u₁.other _ (by decide), h20]
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 224) (by decide) (by rw [c₁])
    (in_scr hp (u₁.wr.trans hwr) (by omega)) fun s₂ g₂ => ?_
  refine wp_movz fun s₃ u₃ => ?_
  have c₃ : s₃.gpr .x20 = scr s₀ := by rw [u₃.other _ (by decide), g₂.gpr, c₁]
  have w₃ : s₃.wr = s.wr := by rw [u₃.wr, g₂.wr, u₁.wr]
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 232) (by decide) (by rw [c₃])
    (in_scr hp (w₃.trans hwr) (by omega)) fun s₄ g₄ => ?_
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 240) (by decide) (by rw [g₄.gpr, c₃])
    (by rw [g₄.wr]; exact in_scr hp (w₃.trans hwr) (by omega)) fun s₅ g₅ => ?_
  refine wp_movz3 fun s₆ u₆ => ?_
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 248) (by decide) (by rw [u₆.other _ (by decide), g₅.gpr, g₄.gpr, c₃])
    (by rw [u₆.wr, g₅.wr, g₄.wr]; exact in_scr hp (w₃.trans hwr) (by omega)) fun s₇ g₇ => ?_
  refine k s₇ (fun r hr => ?_) (by rw [g₇.rd, u₆.rd, g₅.rd, g₄.rd, u₃.rd, g₂.rd, u₁.rd])
    (by rw [g₇.wr, u₆.wr, g₅.wr, g₄.wr, w₃]) (by rw [g₇.sp, u₆.sp, g₅.sp, g₄.sp, u₃.sp, g₂.sp, u₁.sp]) ?_
  · rw [g₇.gpr, u₆.other r hr, g₅.gpr, g₄.gpr, u₃.other r hr, g₂.gpr, u₁.other r hr]
  · have e₂ : s₂.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224) [0x80, 0, 0, 0, 0, 0, 0, 0] := by
      rw [g₂.mem, u₁.gpr, u₁.mem]; exact writeW_bytes _ _ _ _ (by decide)
    have e₄ : s₄.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224)
        ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]) := by
      rw [g₄.mem, u₃.gpr, u₃.mem, e₂, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 0, 0] (by decide)]
      exact writeBytes_append' _ _ _ (by simp only [List.length_cons, List.length_nil]; bv_omega) (by simp)
    have e₅ : s₅.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 224)
        ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]) := by
      rw [g₅.mem, g₄.gpr, u₃.gpr, e₄, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 0, 0] (by decide)]
      exact writeBytes_append' _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; bv_omega)
        (by simp)
    rw [g₇.mem, u₆.gpr, u₆.mem, e₅, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 3, 0] (by decide),
      writeBytes_append' _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; bv_omega)
        (by simp)]
    rfl

theorem readW_writeW_ne (m : Mem) {a b : Addr} (v : BitVec 64) (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  (Frame.writeW (Frame.refl [⟨b, 8⟩] m) (r := ⟨b, 8⟩) (List.mem_singleton_self _) v
    (contains_base (by decide))).readW (r := ⟨a, 8⟩)
    (contains_base (by decide)) (by simpa using h) (by decide)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ (Inv s₀ (nn s₀)) := by
  unfold prologue
  refine save_ok (fun d _ hd₂ => in_scr hp rfl (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  -- The return address.
  refine wp_str (a := scr s₀ + BitVec.ofNat 64 256) (by decide) (by rw [g₁])
    (by rw [wr₁]; exact in_scr hp rfl (by omega)) fun s₂ g₂ => ?_
  -- Our registers.
  refine wp_addImm (by omega) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_mov fun s₇ u₇ => ?_
  have G : ∀ r, s₂.gpr r = s₀.gpr r := fun r => by rw [g₂.gpr, g₁]
  have hr : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s₇.gpr r = s₀.gpr r := by
    intro r h₁ h₂ h₃ h₄ h₅
    rw [u₇.other r h₅, u₆.other r h₄, u₅.other r h₃, u₄.other r h₂, u₃.other r h₁, G]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, rd₁]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, wr₁]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp, sp₁]
  have M₇ : s₇.mem = (saveMem s₀.mem (scr s₀) s₀.gpr).writeW (scr s₀ + BitVec.ofNat 64 256) (s₀.gpr .x30) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, m₁, g₁]
  have x19₇ : s₇.gpr .x19 = stA s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, G]
  have x20₇ : s₇.gpr .x20 = scr s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), G]
  have x21₇ : s₇.gpr .x21 = key s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), G]
  have x22₇ : s₇.gpr .x22 = tP s₀ := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), G]
  have x23₇ : s₇.gpr .x23 = s₀.gpr .x2 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), G]
  have x1₇ : s₇.gpr .x1 = uP s₀ := hr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- `U` and the padding.
  refine Proof.Hmac.AArch64.copy64_ok (by decide) (by decide) 0 192 4 ⟨rfl, rfl⟩ ⟨by omega, by omega⟩ _ s₇ _
    (fun j hj => by
      rw [x1₇, rd₇, wr₇, Proof.Pbkdf2.Memory.add_ofNat]
      exact ⟨uR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩)
    (fun j hj => by rw [x20₇, wr₇, Proof.Pbkdf2.Memory.add_ofNat]; exact in_scr hp rfl (by omega)) ?_
    fun s₈ g₈ rd₈ wr₈ sp₈ m₈ => ?_
  · rw [x1₇, x20₇]
    exact Region.Disjoint.sep hp.u_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  refine padding_ok hp (by rw [g₈ _ (by decide), x20₇]) (wr₈.trans wr₇) fun s₉ g₉ rd₉ wr₉ sp₉ m₉ => WP.block_nil ?_
  have G₉ : ∀ r, r ≠ .x9 → s₉.gpr r = s₇.gpr r := fun r h => by rw [g₉ r h, g₈ r h]
  have e0 : uP s₀ + BitVec.ofNat 64 0 = uP s₀ := by simp
  have hm : s₉.mem = writeBytes (writeBytes s₇.mem (blkA s₀) (bytesAt s₇.mem (uP s₀) 32))
      (scr s₀ + BitVec.ofNat 64 224) pad96 := by
    rw [m₉, m₈, x20₇, x1₇, e0]
  have inS : ∀ d n : Nat, d + n ≤ 384 → (scR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) n :=
    fun d n h => contains_offset h (by omega)
  have F₇ : Frame [scR s₀] s₀.mem s₇.mem := by
    rw [M₇]
    exact ((saveMem_frame s₀.mem (scr s₀) s₀.gpr).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (inS 256 8 (by omega))
  have fU : Frame [sR s₀ 192 32, sR s₀ 224 32] s₇.mem s₉.mem := by
    rw [hm]
    exact ((writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono (by simp)).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 224 32) (contains_base (by decide))).mono (by simp))
  have F' : Frame [scR s₀] s₀.mem s₉.mem :=
    F₇.trans (fU.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩
      · exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  have F : Frame [tR s₀, scR s₀] s₀.mem s₉.mem := F'.mono (by simp)
  have hsep : Mem.Sep (blkA s₀) 32 (scr s₀ + BitVec.ofNat 64 224) pad96.length :=
    Region.Disjoint.sep (scr_disj s₀ (a := 192) (m := 32) (b := 224) (n := 32) (by omega) (by omega) (by omega))
      (contains_base (Nat.le_refl _)) (contains_base (Nat.le_refl _))
  have hU : bytesAt s₉.mem (blkA s₀) 32 = bytesAt s₀.mem (uP s₀) 32 := by
    have := bytesAt_writeBytes_self s₇.mem (blkA s₀) (bytesAt s₇.mem (uP s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [hm, bytesAt_writeBytes_sep _ _ hsep (by omega), this]
    exact frame_bytesAt F₇ (by simpa using hp.u_s) (by omega)
  have hT : bytesAt s₉.mem (tP s₀) 32 = bytesAt s₀.mem (tP s₀) 32 :=
    frame_bytesAt F' (by simpa using hp.t_s) (by omega)
  have hS : ∀ {d : Nat}, (112 ≤ d ∧ d + 8 ≤ 160) ∨ 256 ≤ d → d + 8 ≤ 384 →
      s₉.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 = s₇.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    refine fU.readW (r := sR s₀ d 8) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_disj s₀ (by omega) (by omega) (by omega)
    · exact scr_disj s₀ (by omega) (by omega) (by omega)
  refine ⟨⟨by rw [rd₉, rd₈, rd₇], by rw [wr₉, wr₈, wr₇], by rw [sp₉, sp₈, sp₇], by rw [G₉ _ (by decide), x19₇],
    by rw [G₉ _ (by decide), x20₇], by rw [G₉ _ (by decide), x21₇], by rw [G₉ _ (by decide), x22₇], F⟩,
    ?_, ⟨fun p hp' => ?_, ?_⟩, ?_, (Nat.le_refl _), by rw [hU, hT]⟩
  · rw [G₉ _ (by decide), x23₇]; simp [nn]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rw [hS (.inl hd) (by omega), M₇, readW_writeW_save _ _ _ (by omega) (by omega) (by omega)]
    exact saveMem_saved _ _ _ p (by simp only [saved, List.mem_cons, List.not_mem_nil, or_false]; exact hp')
  · rw [hS (.inr (Nat.le_refl _)) (by omega), M₇, Mem.readW_writeW_self64]
  · rw [hm]
    exact bytesAt_writeBytes_self _ (scr s₀ + BitVec.ofNat 64 224) pad96 (by decide)

/-! ## The epilogue -/

/-- The postcondition of `main`. -/
def Post (s₀ s' : State) : Prop :=
  ∀ k0, k0.length = 64 → Repr s₀.mem (key s₀) (xorPad k0 ipad) → Repr s₀.mem (key s₀ + 96) (xorPad k0 opad) →
    bytesAt s'.mem (tP s₀) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) (nn s₀) (bytesAt s₀.mem (uP s₀) 32) (bytesAt s₀.mem (tP s₀) 32)

/-- With the key's streaming states as the contract requires, a step is HMAC-SHA-256. -/
theorem stepM_eq {s₀ : State} {k0 : List Byte} (hk : k0.length = 64)
    (hi : Repr s₀.mem (key s₀) (xorPad k0 ipad)) (ho : Repr s₀.mem (key s₀ + 96) (xorPad k0 opad))
    {u : List Byte} (hu : u.length = 32) :
    hmacBlockKey sha256 k0 u = stepM s₀ u := by
  have li : (xorPad k0 ipad).length = 64 := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = 64 := by simp [xorPad, hk]
  have e0 : key s₀ + BitVec.ofNat 64 0 = key s₀ := by simp
  have ho1 : stateAt s₀.mem (key s₀ + BitVec.ofNat 64 96) = _ := ho.1
  rw [hmac_step hk hu, stepM, Hi, Ho, e0, hi.1, ho1, li, lo]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.block epilogue) s fun s' => (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧
      s'.gpr .x30 = s₀.gpr .x30 ∧ s'.sp = s₀.sp ∧ Post s₀ s' := by
  unfold epilogue
  refine wp_ldr (a := scr s₀ + BitVec.ofNat 64 256) (by decide) (by rw [h.x20])
    (InRegions.right (in_scr hp h.wr (by omega))) fun s₁ u₁ => ?_
  refine restore_ok (scr := scr s₀) (by rw [u₁.other _ (by decide), h.x20])
    (fun d _ hd₂ => by rw [u₁.wr]; exact InRegions.right (in_scr hp h.wr (by omega))) s₀.gpr
    (fun p hp' => by rw [u₁.mem]; exact h.saved.1 p hp')
    fun s' hs hother hmem _ _ hsp => ⟨hs, by rw [hother .x30 (by simp [saved]), u₁.gpr, h.saved.2],
      by rw [hsp, u₁.sp, h.sp], fun k0 hk hi ho => ?_⟩
  have := h.val
  simp only [Spec.Pbkdf2.iterate] at this
  rw [hmem, u₁.mem, ← this]
  exact (iterate_congr (fun u hu => stepM_eq hk hi ho hu) (fun u => Pbkdf2.digest_length _) _ _ _
    (bytesAt_length _ _ _)).symm

/-! ## Correctness -/

/-- No instruction of `main` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs main, dstOf i ≠ some r := by
  have : ((instrs main).all fun i => untouched.all fun r => dstOf i != some r) = true :=
    instrs_keeps (by decide +kernel)
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa main s₀ fun s' => abiPreserved s₀ s' ∧ Post s₀ s' := by
  refine WP.mono (Proof.MdStream.AArch64.WP.gprs (Q := fun s' => (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧
      s'.gpr .x30 = s₀.gpr .x30 ∧ s'.sp = s₀.sp ∧ Post s₀ s') ?_ untouched_ok)
    fun s' ⟨⟨hsv, h30, hsp, hpost⟩, hu⟩ => ⟨⟨fun r hr => ?_, hsp⟩, hpost⟩
  · unfold main
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
    exact WP.seq (WP.mono (loop_ok hp h₁) fun s₂ h₂ => epilogue_ok hp h₂)
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.x19, 112) (by simp [saved])
    · exact hsv (.x20, 120) (by simp [saved])
    · exact hsv (.x21, 128) (by simp [saved])
    · exact hsv (.x22, 136) (by simp [saved])
    · exact hsv (.x23, 144) (by simp [saved])
    · exact hsv (.x24, 152) (by simp [saved])
    all_goals first | exact h30 | exact hu _ (by simp [untouched])

/-- The state after the first instruction, which zero-extends `n`. -/
def zext (s : State) : State := s.write .w .x2 (s.read .w .x2 + BitVec.ofNat 32 0)

theorem zext_exec (s : State) : Exec isa (.block [.addImm .w .x2 .x2 0]) s [] (zext s) := .block rfl

theorem zext_other (s : State) {r : Reg} (h : r ≠ .x2) : (zext s).gpr r = s.gpr r :=
  (Upd.write s .w .x2 _).other r h

theorem zext_x2 (s : State) : (zext s).gpr .x2 = ((s.gpr .x2).setWidth 32).setWidth 64 := by
  rw [zext, (Upd.write s .w .x2 _).gpr]; simp [State.read]

theorem pre_of {s : State} (h : Proof.Pbkdf2.iterateSha256AArch64.pre s) : Pre (zext s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e0 : (zext s).gpr .x0 = s.gpr .x0 := zext_other s (by decide)
  have e1 : (zext s).gpr .x1 = s.gpr .x1 := zext_other s (by decide)
  have e3 : (zext s).gpr .x3 = s.gpr .x3 := zext_other s (by decide)
  have e4 : (zext s).gpr .x4 = s.gpr .x4 := zext_other s (by decide)
  have hn : nn (zext s) < 2 ^ 32 := by
    simp only [nn, zext_x2, BitVec.toNat_setWidth]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hn⟩ <;>
    simp only [keyR, uR, tR, scR, key, uP, tP, scr, e0, e1, e3, e4] <;> assumption

theorem correct {s : State} (hs : Proof.Pbkdf2.iterateSha256AArch64.pre s) :
    ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ Proof.Pbkdf2.iterateSha256AArch64.post s s' := by
  obtain ⟨t, s', he, ⟨habi, hsp⟩, hpost⟩ := correctMain (pre_of hs)
  refine ⟨[] ++ t, s', .seq (zext_exec s) he, ⟨fun r hr => ?_, hsp⟩, fun k0 hk hi ho => ?_⟩
  · have hne : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [habi r hr, zext_other s hne]
  · have e0 : (zext s).gpr .x0 = s.gpr .x0 := zext_other s (by decide)
    have e1 : (zext s).gpr .x1 = s.gpr .x1 := zext_other s (by decide)
    have e3 : (zext s).gpr .x3 = s.gpr .x3 := zext_other s (by decide)
    have e : nn (zext s) = ((s.gpr .x2).setWidth 32).toNat := by
      simp only [nn, zext_x2, BitVec.toNat_setWidth]
      omega
    have hi' : Repr (zext s).mem (key (zext s)) (xorPad k0 ipad) := by simp only [key, e0]; exact hi
    have ho' : Repr (zext s).mem (key (zext s) + 96) (xorPad k0 opad) := by simp only [key, e0]; exact ho
    have := hpost k0 hk hi' ho'
    simp only [tP, uP, e1, e3, e] at this
    exact this

/-! ## Constant time -/

theorem ct_of {τ : VG.AArch64.Taint.T}
    (hτ : ∀ s₁ s₂, Proof.Pbkdf2.iterateSha256AArch64.pub s₁ s₂ → VG.AArch64.Taint.Agree τ (zext s₁) (zext s₂))
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ main hc).isSome = true) :
    ConstantTime isa Proof.Pbkdf2.iterateSha256AArch64.pre Proof.Pbkdf2.iterateSha256AArch64.pub iterate := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  obtain ⟨τ', hc'⟩ := Option.isSome_iff_exists.mp h
  unfold iterate at e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, rfl⟩ := Exec.det a₁ (zext_exec s₁)
      obtain ⟨rfl, rfl⟩ := Exec.det a₂ (zext_exec s₂)
      rw [(VG.Taint.check_sound (A := taint) hc' (hτ _ _ hp) b₁ b₂).1]

/-- The initial taint of `main`: the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Pbkdf2.iterateSha256AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (zext s₁) (zext s₂) := by
  obtain ⟨p0, p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [zext_other _ (by decide), zext_other _ (by decide), p0]
  · rw [zext_other _ (by decide), zext_other _ (by decide), p1]
  · rw [zext_x2, zext_x2, p2]
  · rw [zext_other _ (by decide), zext_other _ (by decide), p3]
  · rw [zext_other _ (by decide), zext_other _ (by decide), p4]

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 192⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 384⟩]

theorem iterate_ct : ConstantTime isa Proof.Pbkdf2.iterateSha256AArch64.pre
    Proof.Pbkdf2.iterateSha256AArch64.pub iterate :=
  ct_of (τ := VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (fun _ _ hp => agree₀ hp)
    (by taint_decide)

/-- `iterateSha256AArch64` with the 832 bytes of scratch of the shared
contract (sized for the x86-64 AVX2 compression function), of which the code
uses 384. -/
def iterateWide : Contract isa :=
  { Proof.Pbkdf2.iterateSha256AArch64 with
    pre := fun s =>
      let key : Region := ⟨s.gpr .x0, 192⟩
      let u : Region := ⟨s.gpr .x1, 32⟩
      let t : Region := ⟨s.gpr .x3, 32⟩
      let scratch : Region := ⟨s.gpr .x4, 832⟩
      s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
      key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧
      t.Disjoint scratch }

/-- The regions `iterateSha256AArch64` lets the code write. -/
def narrowWr (s : State) : List Region := [⟨s.gpr .x3, 32⟩, ⟨s.gpr .x4, 384⟩]

theorem iterateWide_pre (s : State) (h : iterateWide.pre s) :
    Proof.Pbkdf2.iterateSha256AArch64.pre (s.withRegions s.rd (narrowWr s)) :=
  let ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ := h
  ⟨h₁, rfl, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅, h₆.sub_right (Region.sub_of_ble rfl),
    h₇.sub_right (Region.sub_of_ble rfl)⟩

/-- A state satisfying `iterateWide.pre`. -/
def wideSat : State := { sat with wr := [⟨0x3000, 32⟩, ⟨0x4000, 832⟩] }

theorem iterateWide_implies :
    iterateWide.Implies (Spec.Pbkdf2.iterateSha256Contract AArch64.abi) := by
  sig_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig, iterateWide,
    Proof.Pbkdf2.iterateSha256AArch64, AArch64.abi, AArch64.argRegs] [wideSat, sat] using wideSat

/-- The proof is written against `iterateSha256AArch64`, widened to the
shared contract's scratch. -/
theorem iterate_verified :
    Verified AArch64.target Impl.Pbkdf2.AArch64.iterate
      (Spec.Pbkdf2.iterateSha256Contract AArch64.abi) :=
  have hsat := iterateWide_implies.sat_left
  (Verified.widen (Verified.of_correct (fun _ hs => correct hs) iterate_ct
    (.refl (hsat.elim fun s hs => ⟨_, iterateWide_pre s hs⟩)))
    narrowWr iterateWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat).of_implies iterateWide_implies

end VG.Proof.Pbkdf2.AArch64
