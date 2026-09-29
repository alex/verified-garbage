import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Scrypt.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# The Salsa20/8 Core on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Scrypt.X86_64

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega), bufAt, ofInt_natCast]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j (hj : j < 16), m.readW (bufAt (bp s₀) (4 * j)) 32 =
      (Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀))[j] + (V s₀)[j]) :
    Spec.Scrypt.bytesAt m (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, ← h j hj, bufAt, ofInt_natCast]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Scrypt.salsaX86_64.post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hf₁ : Frame [scR (sp s₀)] s₀.mem s₁.mem := hm₁ ▸ saveMem_frame s₀
  have hl₀ : LI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ h => absurd h (by omega), fun _ _ _ h => absurd h (by omega), Frame.refl _ _, hrd₁,
      hwr₁, by rw [hg₁], by rw [hg₁], by rw [hg₁]⟩
  refine WP.mono (wp_range_flatMap (LI s₀ s₁) (fun k s hk h => load_step hp hf₁ hk h) 16 (Nat.le_refl _)
    s₁ hl₀) fun s₂ hL => ?_
  have hri : RI (sp s₀) (V s₀) s₂ s₂ :=
    ⟨fun k hk => hL.regs k hk (by omega), fun k hk h12 => hL.slots k hk h12 hk, Frame.refl _ _,
      rfl, rfl, hL.rsi, rfl, rfl⟩
  have hw₂ : scR (sp s₀) ∈ s₂.wr := by rw [hL.wr]; exact hp.hs
  refine WP.seq (WP.mono (rounds_ok hri hw₂ 4) fun s₃ hR => ?_)
  rw [WP.block_append_iff]
  have hsc : Frame [slotR (sp s₀)] s₁.mem s₃.mem := hL.frame.trans hR.frame
  have hbf : Frame [scR (sp s₀)] s₀.mem s₃.mem := hf₁.trans (hsc.sub (sub_slot_sc _))
  have hF₀ : FI s₀ (Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)) s₃ 0 s₃ :=
    ⟨fun j hj => by rw [ite_neg' (by omega)]; exact read_b hp hbf hj, fun k hk _ => hR.regs k hk,
      Frame.refl _ _, hR.rd.trans hL.rd, hR.wr.trans hL.wr, hR.rsi, hR.rdi.trans hL.rdi,
      hR.rsp.trans hL.rsp⟩
  refine WP.mono (wp_range_flatMap (FI s₀ _ s₃)
    (fun k s hk h => finish_step hp (fun k hk h12 => hR.slots k hk h12) hk h) 16 (Nat.le_refl _) s₃ hF₀)
    fun s₄ hF => ?_
  have hsaved : Saved s₀ s₄.mem := saved_frame hp (hm₁ ▸ saveMem_saved s₀) hsc hF.frame
  refine WP.mono (restore_ok hsaved hF.rsi (by rw [hF.wr]; exact hp.hs))
    fun s' ⟨hm', hrsp', hg'⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hrsp'.trans hF.rsp
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
  · rw [hm', hF.frame.readW (r := retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_b)
      (by decide)]
    exact hbf.readW (r := retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_sc)
      (by decide)
  · show Spec.Scrypt.bytesAt s'.mem (bp s₀) 64 =
      Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64)
    rw [hm']
    exact post_of fun j hj => by simpa [hj] using hF.out j hj

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩]

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem salsa_ct : ConstantTime isa Proof.Scrypt.salsaX86_64.pre Proof.Scrypt.salsaX86_64.pub
    Impl.Scrypt.X86_64.salsa := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem salsa_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.salsa (Spec.Scrypt.salsaContract X86_64.abi) :=
  Verified.of_correct salsa_correct salsa_ct (by
    sig_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig, Proof.Scrypt.salsaX86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Scrypt.X86_64.satState] using Proof.Scrypt.X86_64.satState)

end VG.Proof.Scrypt.X86_64
