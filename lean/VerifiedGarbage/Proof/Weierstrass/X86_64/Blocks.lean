import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

/-!
# Short Weierstrass curves on x86-64: code as a sequence of blocks

`blocks ls` runs as the block `ls.flatten` (`blocks_wp`), so `fprogB` (a block
per field operation) runs as `fprog`, and `fprog_ok`/`rcb_ok` hold for it.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64

theorem blocks_wp : ∀ (ls : List (List Instr)) {s : State} {Q : State → Prop},
    WP isa (blocks ls) s Q ↔ WP isa (.block ls.flatten) s Q
  | [], _, _ => by simp [blocks]
  | [b], _, _ => by simp [blocks]
  | b :: c :: bs, s, Q => by
    rw [show blocks (b :: c :: bs) = .seq (.block b) (blocks (c :: bs)) from rfl, WP.seq_iff, List.flatten_cons, WP.block_append_iff]
    exact ⟨fun h => WP.mono h fun _ h' => (blocks_wp (c :: bs)).mp h',
      fun h => WP.mono h fun _ h' => (blocks_wp (c :: bs)).mpr h'⟩

theorem fprogB_wp (M : Mod) (ops : List FOp) {s : State} {Q : State → Prop} :
    WP isa (fprogB M ops) s Q ↔ WP isa (.block (fprog M ops)) s Q := by
  rw [fprogB, blocks_wp, fprog, List.flatMap_def]

end VG.Proof.Weierstrass.X86_64
